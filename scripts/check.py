#!/usr/bin/env python3
"""Check every adjacent equivalence in a property sequence, without deriving generators."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
ENV = ROOT / 'environment/env.sh'
COQ_FLAGS = ['-Q', 'support', 'ALCoq', '-Q', 'specification', 'Specification',
             '-Q', 'fixture', 'FixtureSpec', '-Q', 'p4', 'P4Spec',
             '-Q', 'wasm', 'WasmSpec', '-R', 'property', 'Property']
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
REQUIRE = re.compile(r'\b(?:From\s+([A-Za-z0-9_.]+)\s+)?Require'
                     r'(?:\s+(?:Import|Export))?\s+([A-Za-z0-9_.\s]+?)\s*\.')


class CheckError(Exception):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


def positive(value):
    value = int(value)
    if value <= 0:
        raise argparse.ArgumentTypeError('must be positive')
    return value


def nonnegative(value):
    value = int(value)
    if value < 0:
        raise argparse.ArgumentTypeError('must be nonnegative')
    return value


def code_only(source):
    """Remove nested Coq comments and strings before checking unsafe directives."""
    output, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == '(*':
                depth += 1
                index += 2
            elif pair == '*)':
                depth -= 1
                index += 2
            else:
                index += 1
            output.append(' ')
        elif quoted:
            if pair == '""':
                index += 2
            else:
                quoted = char != '"'
                index += 1
            output.append(' ')
        elif pair == '(*':
            depth = 1
            index += 2
            output.append(' ')
        elif char == '"':
            quoted = True
            index += 1
            output.append(' ')
        else:
            output.append(char)
            index += 1
    if depth or quoted:
        raise CheckError('Unterminated Coq comment or string')
    return ''.join(output)


def validate_source(path, data, *, authored=True):
    text = code_only(data.decode('utf-8'))
    declarations = (r'Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures|'
                    r'Admitted|Admit')
    if authored:
        declarations += r'|Hypothesis|Hypotheses|Variable|Variables|Context|Contexts|Assumption|Assumptions'
    declaration = re.search(r'(?:\A|\.\s+)\s*(?:#\[[^]]*\]\s*|'
                            r'(?:Local|Global|Export|Time|Fail|Succeed)\s+|'
                            r'Timeout\s+\d+\s+)*(?P<keyword>' + declarations + r')\b', text)
    if declaration:
        raise CheckError(f'{path}: {declaration.group("keyword")} is not allowed in sources')
    if re.search(r'(?<!\.)\badmit\b', text):
        raise CheckError(f'{path}: admit is not allowed in sources')
    forbidden = r'\b(?:Extract|Extraction|Load)\b|\bDeclare\s+ML\b|\b(?:Add|Remove)\s+(?:Rec\s+)?(?:LoadPath|ML\s+Path)\b|\bUnset\s+(?:Guard|Positivity|Universe)\s+Checking\b'
    execution = r'(?:^|\.\s)\s*(?:(?:Time|Fail|Timeout\s+\d+)\s+)*(?:QuickChick|QuickChickWith|QuickCheck|QuickCheckWith|Sample)\b'
    if re.search(forbidden, text) or re.search(execution, text):
        raise CheckError(f'{path}: execution, extraction, load-path overrides, and unsafe checking directives are not allowed in authored sources')


def dependencies(data):
    text = code_only(data.decode('utf-8'))
    for prefix, names in REQUIRE.findall(text):
        for name in names.split():
            yield f'{prefix}.{name}' if prefix else name


def namespace_roots(property_name, fixture_root=None):
    return {
        'ALCoq': (ROOT / 'translator/coq', Path('support')),
        'Specification': (ROOT / 'specification', Path('specification')),
        'P4Spec': (ROOT / 'specification/p4', Path('p4')),
        'WasmSpec': (ROOT / 'specification/wasm', Path('wasm')),
        'FixtureSpec': (fixture_root or ROOT / 'specification' / property_name,
                        Path('fixture')),
    }


def dependency_path(name, property_name, fixture_root=None, namespaces=None):
    parts = name.split('.')
    mapping = namespaces if namespaces is not None else namespace_roots(property_name, fixture_root)
    if parts[0] not in mapping:
        return None
    source_root, target_root = mapping[parts[0]]
    if not all(IDENTIFIER.fullmatch(part) for part in parts[1:]):
        raise CheckError(f'Invalid Coq dependency: {name}')
    relative = Path(*parts[1:]).with_suffix('.v')
    return source_root / relative, target_root / relative


def discover(prop, selected=None):
    if not (prop / 'Original.v').is_file():
        raise CheckError(f'Missing {prop / "Original.v"}')
    directory = prop / 'candidates'
    if not directory.is_dir():
        raise CheckError('Missing candidates directory')
    candidates = []
    for path in directory.iterdir():
        if path.name.startswith('.'):
            continue
        if not path.is_dir() or not re.fullmatch(r'v[0-9]+', path.name):
            raise CheckError(f'Invalid sequence entry: {path.name}; expected v001, v002, ...')
        candidates.append((int(path.name[1:]), path.name))
    candidates.sort()
    if selected is not None:
        names = [name for _, name in candidates]
        if selected not in names:
            raise CheckError(f'Unknown candidate: {selected}')
        candidates = candidates[:names.index(selected) + 1]
    if not candidates or [number for number, _ in candidates] != list(range(1, len(candidates) + 1)):
        raise CheckError('Candidate sequence must be nonempty and contiguous from v001 (no gaps or duplicate numbers)')
    return [name for _, name in candidates]


def module(name):
    return f'Property.candidates.{name}.Candidate'


def chain_source(sequence):
    imports = ['Property.Original']
    definitions = []
    previous = 'Property.Original'
    forward = backward = 'H'
    for name in sequence:
        current = module(name)
        proof = f'Property.candidates.{name}.Equivalence'
        imports.extend([current, proof])
        definitions.append(f'Definition link_{name} : forall x : Property.Original.Input,\n  Coq.Init.Logic.iff ({previous}.predicate x) ({current}.predicate x) :=\n  {proof}.equivalent.\n')
        forward = f'(Coq.Init.Logic.proj1 (link_{name} x) {forward})'
        previous = current
    for name in reversed(sequence):
        backward = f'(Coq.Init.Logic.proj2 (link_{name} x) {backward})'
    definitions.append(f'''Definition original_equivalent : forall x : Property.Original.Input,
  Coq.Init.Logic.iff (Property.Original.predicate x) ({previous}.predicate x) :=
  fun x => Coq.Init.Logic.conj (fun H => {forward}) (fun H => {backward}).
Print Assumptions original_equivalent.
''')
    return '\n'.join(f'Require {name}.' for name in imports) + '\n' + '\n'.join(definitions)


def assumptions(output):
    if 'Axioms:' not in output:
        if 'Closed under the global context' in output or 'Closed under global context' in output:
            return []
        raise CheckError('Could not read the proof assumption audit')
    block = output.split('Axioms:', 1)[1]
    names = []
    for line in block.splitlines():
        if not line.strip() or line[0].isspace():
            continue
        entry = re.fullmatch(r"(\S+?)(?:\s*:.*|\s*)", line)
        if not entry:
            raise CheckError(f'Unrecognized proof assumption entry: {line}')
        names.append(entry.group(1))
    if not names:
        raise CheckError('Could not parse proof assumptions')
    return sorted(set(names))


class Session:
    def __init__(self, prop, selected=None, timeout=120, fixture_root=None):
        self.prop = prop.resolve()
        self.selected = selected
        self.sequence = discover(self.prop, selected)
        self.timeout = timeout
        self.fixture_root = Path(fixture_root).resolve() if fixture_root is not None else None
        self.namespaces = namespace_roots(self.prop.name, self.fixture_root)
        self.coq_flags = list(COQ_FLAGS)
        self.publications = []
        runs = self.prop / '.runs'
        runs.mkdir(exist_ok=True)
        self.directory = Path(tempfile.mkdtemp(prefix='check-' if selected is None else 'run-', dir=runs))
        self.sources = self.directory / 'sources'
        self.sources.mkdir()
        for name in ['specification', 'support', 'p4', 'wasm', 'fixture', 'candidate']:
            (self.sources / name).mkdir()
        self.originals = {}
        self.report = {'status': 'running', 'sequence': self.sequence, 'property': str(self.prop),
                       'commands': [], 'source_hashes': {}, 'tool_hashes': {}, 'timeout_seconds': timeout}
        self.started = time.monotonic()
        self.save()

    def save(self):
        self.report['elapsed_seconds'] = round(time.monotonic() - self.started, 6)
        (self.directory / 'result.json').write_text(json.dumps(self.report, indent=2) + '\n')

    def command(self, args, label, coq=True):
        argv = ['bash', str(ENV), *map(str, args)] if coq else list(map(str, args))
        started = time.monotonic()
        log = self.directory / f'{label}.log'
        entry = {'command': argv, 'log': log.name}
        self.report['commands'].append(entry)
        stderr_log = self.directory / f'{label}.stderr.log'
        entry['stderr_log'] = stderr_log.name
        with log.open('w') as stream, stderr_log.open('w') as errors:
            process = subprocess.Popen(argv, cwd=self.sources, stdout=stream, stderr=errors,
                                       start_new_session=True)
            try:
                code = process.wait(timeout=self.timeout)
            except (subprocess.TimeoutExpired, KeyboardInterrupt):
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                entry.update(status='timeout', seconds=time.monotonic() - started)
                self.save()
                raise CheckError(f'{label}: timed out or interrupted; see {log}')
        entry.update(returncode=code, seconds=round(time.monotonic() - started, 6))
        self.save()
        if code:
            raise CheckError(f'{label}: command failed (exit {code}); see {log}\n{(log.read_text() + stderr_log.read_text())[-2500:]}')
        return log.read_text()

    def preserve(self, path, target, *, coq=False):
        if not path.is_file() or path.is_symlink():
            raise CheckError(f'Missing source or unsupported symlink: {path}')
        data = path.read_bytes()
        if coq:
            validate_source(path, data, authored=target.parts[0] == 'property')
        recorded = self.report['source_hashes'].get(str(target))
        if recorded is not None and recorded != digest(data):
            raise CheckError(f'Conflicting snapshot sources: {target}')
        destination = self.sources / target
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        self.originals[path] = digest(data)
        self.report['source_hashes'][str(target)] = digest(data)
        return data

    @staticmethod
    def publication_relative(value, manifest):
        if not isinstance(value, str):
            raise CheckError(f'Invalid semantic pass path in {manifest}')
        path = Path(value)
        if not path.parts or path.is_absolute() or '..' in path.parts:
            raise CheckError(f'Invalid semantic pass path in {manifest}: {value}')
        return path

    def register_publications(self, translator_hash):
        root = self.fixture_root or ROOT / 'specification' / self.prop.name
        selected = [(root, None)] + [(root / 'candidates' / name, name)
                                     for name in self.sequence]
        for directory, candidate in selected:
            manifest = directory / 'PassEvidence.json'
            legacy_source = (self.prop / 'candidates' / candidate / 'Helper.watsup'
                             if candidate else directory / 'source/Property.watsup')
            if not manifest.is_file():
                if legacy_source.is_file():
                    raise CheckError(f'Missing semantic pass evidence: {manifest}')
                continue
            try:
                evidence = json.loads(manifest.read_text())
            except (json.JSONDecodeError, UnicodeError) as error:
                raise CheckError(f'Invalid semantic pass evidence: {manifest}: {error}') from error
            if not isinstance(evidence, dict):
                raise CheckError(f'Invalid semantic pass evidence: {manifest}')
            namespace = evidence.get('namespace')
            if namespace is None:
                namespace = 'CandidateSpec' if candidate else 'FixtureSpec'
            if not isinstance(namespace, str) or not IDENTIFIER.fullmatch(namespace):
                raise CheckError(f'Invalid semantic pass namespace in {manifest}')
            target = (Path('candidate') if namespace == 'CandidateSpec' else
                      Path('candidate_' + candidate)) if candidate else Path('fixture')
            if namespace in self.namespaces and not (
                    candidate is None and namespace in {'FixtureSpec', 'P4Spec', 'WasmSpec'}):
                raise CheckError(f'Conflicting semantic pass namespace: {namespace}')
            self.namespaces[namespace] = (directory, target)
            if candidate is None and namespace != 'FixtureSpec':
                del self.namespaces['FixtureSpec']
            source_name = evidence.get('source')
            if source_name is not None:
                if not isinstance(source_name, str):
                    raise CheckError(f'Invalid semantic pass source in {manifest}')
                source = (directory / source_name).resolve()
                if not source.is_relative_to(ROOT):
                    raise CheckError(f'Semantic pass source escapes worktree: {source}')
            else:
                source = legacy_source
            if evidence.get('translator_sha256') != translator_hash:
                raise CheckError(f'Translator changed since semantic pass: {manifest}')
            if not source.is_file() or evidence.get('source_sha256') != digest(source.read_bytes()):
                raise CheckError(f'SpecTec source changed since semantic pass: {source}')
            source_target = (Path('property/candidates') / candidate / source.name
                             if candidate else target / 'source' / source.name)
            self.preserve(source, source_target)
            self.preserve(manifest, target / manifest.name)
            artifacts = evidence.get('artifacts', [])
            if not isinstance(artifacts, list):
                raise CheckError(f'Invalid semantic pass artifacts: {manifest}')
            for entry in artifacts:
                if not isinstance(entry, dict):
                    raise CheckError(f'Invalid semantic pass artifact in {manifest}')
                relative = self.publication_relative(entry.get('path'), manifest)
                if relative.suffix not in {'.json', '.txt', '.log'}:
                    raise CheckError(f'Invalid semantic pass artifact in {manifest}: {relative}')
                artifact = directory / relative
                if not artifact.is_file() or digest(artifact.read_bytes()) != entry.get('sha256'):
                    raise CheckError(f'Semantic pass artifact changed: {artifact}')
                self.preserve(artifact, target / relative)
            if 'namespace' in evidence and not all(
                    isinstance(evidence.get(field), str) and
                    any(entry.get('sha256') == evidence[field] for entry in artifacts)
                    for field in ['frontend_al_sha256', 'backend_manifest_sha256']):
                raise CheckError(f'Missing semantic pass artifacts: {manifest}')
            outputs = evidence.get('generated')
            if not isinstance(outputs, list) or not outputs:
                raise CheckError(f'Missing generated Coq manifest: {manifest}')
            hashes = {}
            for output in outputs:
                if not isinstance(output, dict):
                    raise CheckError(f'Invalid generated Coq entry: {manifest}')
                relative = self.publication_relative(output.get('path'), manifest)
                if relative.suffix != '.v' or relative in hashes:
                    raise CheckError(f'Invalid generated Coq path in {manifest}: {relative}')
                generated = directory / relative
                if not generated.is_file() or generated.is_symlink() or \
                        digest(generated.read_bytes()) != output.get('sha256'):
                    raise CheckError(f'Generated Coq changed since semantic pass: {generated}')
                hashes[relative] = output['sha256']
                self.originals[generated] = output['sha256']
            self.publications.append({'root': directory, 'target': target,
                                      'namespace': namespace, 'hashes': hashes})
            self.report.setdefault('semantic_publications', []).append({
                'candidate': candidate, 'namespace': namespace,
                'source': str(source_target), 'manifest': str(target / manifest.name),
                'artifacts': [str(target / item['path']) for item in artifacts]})
        self.coq_flags = []
        for namespace, (source, target) in self.namespaces.items():
            (self.sources / target).mkdir(parents=True, exist_ok=True)
            self.coq_flags.extend(['-Q', str(target), namespace])
        self.coq_flags.extend(['-R', 'property', 'Property'])
        self.report['namespace_mapping'] = {
            namespace: {'source': str(source), 'snapshot': str(target)}
            for namespace, (source, target) in self.namespaces.items()}

    def snapshot(self):
        translator_sources = sorted((ROOT / 'translator/src').glob('*.ml'))
        translator_hash = digest(b''.join(path.read_bytes() for path in translator_sources))
        self.register_publications(translator_hash)
        paths = [(self.prop / 'Original.v', Path('property/Original.v'))]
        for name in self.sequence:
            for filename in ['Candidate.v', 'Equivalence.v']:
                paths.append((self.prop / 'candidates' / name / filename,
                              Path('property/candidates') / name / filename))
        pending = list(paths)
        seen = set()
        while pending:
            path, target = pending.pop(0)
            if target in seen:
                continue
            seen.add(target)
            # Match physical publications even when an import uses the legacy
            # Specification/FixtureSpec alias. Candidate roots are more specific
            # than their enclosing fixed specification publication.
            for publication in sorted(self.publications,
                                      key=lambda item: len(item['root'].parts), reverse=True):
                if path.is_relative_to(publication['root']):
                    relative = path.relative_to(publication['root'])
                    if relative not in publication['hashes']:
                        raise CheckError(f'{path}: not listed in the semantic pass generated manifest')
                    break
            data = self.preserve(path, target, coq=True)
            for name in dependencies(data):
                dependency = dependency_path(name, self.prop.name, self.fixture_root,
                                             self.namespaces)
                if dependency is not None and dependency[1] not in seen:
                    pending.append(dependency)
        self.report['dependency_modules'] = sorted(self.report['source_hashes'])
        for path in [ROOT / 'scripts/check.py', ROOT / 'scripts/run.py', ENV, ROOT / 'environment/opam-switch.export']:
            if path.exists():
                self.report['tool_hashes'][str(path.relative_to(ROOT))] = digest(path.read_bytes())
        self.report['tool_hashes']['translator/src/all.ml'] = translator_hash
        self.command(['coqc', '--version'], 'version')
        self.command(['opam', 'list', '--installed', '--columns=name,version'], 'packages')
        self.save()

    def compile(self, file, label):
        return self.command(['coqc', '-q', *self.coq_flags, file], label)

    def fresh(self):
        if discover(self.prop, self.selected) != self.sequence:
            raise CheckError('Candidate sequence changed during verification')
        for path, old in self.originals.items():
            if not path.is_file() or digest(path.read_bytes()) != old:
                raise CheckError(f'Source changed during verification: {path}')
        for name, old in self.report['tool_hashes'].items():
            current = (digest(b''.join(path.read_bytes() for path in sorted((ROOT / 'translator/src').glob('*.ml'))))
                       if name == 'translator/src/all.ml' else digest((ROOT / name).read_bytes()))
            if current != old:
                raise CheckError(f'Tool changed during verification: {name}')

    def check(self):
        self.snapshot()
        files = sorted(str(p.relative_to(self.sources)) for p in self.sources.rglob('*.v'))
        order = self.command(['coqdep', '-sort', *self.coq_flags, *files], 'dependencies')
        # Paths are restricted to Coq identifiers and normalized snapshot directories.
        ordered = [str(Path(item).with_suffix('.v')) for item in order.split()]
        if len(ordered) != len(files) or set(ordered) != set(files):
            raise CheckError('Cannot determine an acyclic source compilation order; see dependencies.log')
        for index, file in enumerate(ordered):
            self.compile(file, f'compile-{index:03d}')
        (self.sources / 'Sequence.v').write_text(chain_source(self.sequence))
        found = assumptions(self.compile('Sequence.v', 'equivalence'))
        self.report['assumptions'] = found
        if found:
            raise CheckError(f'Equivalence has unsupported assumptions: {", ".join(found)}')
        self.command(['coqchk', '-silent', *self.coq_flags, 'Sequence'], 'equivalence-kernel')
        self.fresh()
        self.save()

    def finish(self, error=None):
        self.report['status'] = 'failed' if error else 'passed'
        if error:
            self.report['error'] = str(error)
        self.save()
        return self.directory / 'result.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('property', type=Path, help='directory containing Original.v and candidates/vNNN/')
    parser.add_argument('--timeout', type=positive, default=120, help='seconds per subprocess (default: 120)')
    args = parser.parse_args()
    session = None
    try:
        session = Session(args.property, timeout=args.timeout)
        session.check()
        print(f'Checked {len(session.sequence)} equivalence links: {session.finish()}')
        return 0
    except (CheckError, OSError, UnicodeError) as error:
        if session:
            print(f'Report: {session.finish(error)}', file=sys.stderr)
        print(error, file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
