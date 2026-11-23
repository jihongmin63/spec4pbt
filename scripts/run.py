#!/usr/bin/env python3
"""Check a candidate prefix, derive its tactic generator, and sample Inputs."""
import argparse
import json
from pathlib import Path
import re
import sys

from check import CheckError, Session, COQ_FLAGS, assumptions, code_only, nonnegative, positive

PRELUDE = '''From QuickChick Require Import QuickChick.
From Coq Require Import List ZArith String.
Import ListNotations QcDefaultNotation.
Open Scope qc_scope.
Require Extraction.
'''


def renamed_candidate(source, candidate):
    if not re.search(r'\b(?:Inductive|Definition)\s+predicate\b', code_only(source)):
        raise CheckError(f'{candidate}: no predicate declaration to derive')
    # The tactic resolves relations by name, so each predecessor in the checked
    # prefix needs its own derivation name. Original authored files stay intact.
    for number in range(1, int(candidate[1:])):
        previous = f'v{number:03d}'
        source = source.replace(f'Property.candidates.{previous}.Candidate.predicate',
                                f'Property.DeriveCandidate_{previous}.predicate_{previous}')
        source = source.replace(f'Property.candidates.{previous}.Candidate',
                                f'Property.DeriveCandidate_{previous}')
    return re.sub(r"(?<![A-Za-z0-9_.'])\bpredicate\b", f'predicate_{candidate}', source)


def validate_tactic_form(source, original_source):
    """Reject known forms the pinned tactic either miscompiles or cannot reify."""
    text = code_only(source)
    original = code_only(original_source)
    constructors = set(re.findall(r'\bRecord\s+Input\s*:=\s*([A-Za-z_][A-Za-z0-9_]*)', original))
    constructors.update(re.findall(r'\|\s*([A-Za-z_][A-Za-z0-9_]*)\s*:', original))
    definitions = set(re.findall(r'\bDefinition\s+([A-Za-z_][A-Za-z0-9_]*)', text))
    aliases = set(re.findall(r'\bDefinition\s+([A-Za-z_][A-Za-z0-9_]*)[^.]*?:=\s*'
                             r'(?:Nat|Z|List|String|Bool)\.[A-Za-z_][A-Za-z0-9_]*', text))
    relation = re.search(r'\bInductive\s+predicate\b(.*?)(?=\n\s*(?:Definition|Theorem|Lemma|End|Inductive)\b|\Z)',
                         text, re.S)
    if not relation:
        return
    for constructor in re.finditer(r'\|\s*\w+\s*:\s*(.*?)(?=\n\s*\||\Z)', relation.group(1), re.S):
        rule = constructor.group(1)
        conclusion = re.search(r'\bpredicate\s*(?:\(([^\n]*)\)|([A-Za-z_][A-Za-z0-9_]*))\s*\.', rule)
        if not conclusion:
            continue
        premises = rule[:conclusion.start()]
        for name in sorted(definitions - aliases - {'predicate'}):
            if re.search(r'\b' + re.escape(name) + r'\b', premises):
                raise CheckError(f'global constant {name} in predicate premise is unsupported by tactic')
        standard = re.search(r'\b(?:Nat|Z|List|String|Bool)\.[A-Za-z_][A-Za-z0-9_]*', premises)
        if standard:
            raise CheckError(f'unaliased standard function {standard.group()} in predicate premise')
        expression = conclusion.group(1)
        if expression:
            head = re.match(r'\s*([A-Za-z_][A-Za-z0-9_.]*)\s+', expression)
            if head and ('.' in head.group(1) or
                         head.group(1).split('.')[-1] not in constructors and
                         not head.group(1)[0].isupper()):
                raise CheckError(f'function call {head.group(1)} in predicate conclusion')


def derivation(candidate):
    predicate = f'predicate_{candidate}'
    return PRELUDE + f'''Require Sequence.
Require Import Property.DeriveCandidate_{candidate}.
Theorem generator_factory : forall x : Property.Original.Input,
  {predicate} x -> true = true.
Proof.
  quickchick 2.
  Extraction "generator.ml" GenSizedSuchThat_{predicate}_O Property.Original.encode_input.
  intros; reflexivity.
Qed.
Print Assumptions generator_factory.
'''


def audit_schedule(output):
    match = re.search(r'Theorem Schedule:\s*(.*?)\s*Pieces:', output, re.S)
    if not match:
        raise CheckError('Tactic did not print a schedule')
    variables = re.findall(r'\bdo\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*:', match.group(1))
    if variables != ['x']:
        raise CheckError(f'Tactic schedule generates {variables}, expected only Input x')
    return variables


DRIVER = r'''
let print_json chars = List.iter print_char chars
let () =
  let seed = Random.State.make [| SAMPLER_SEED |] in
  print_char '[';
  for i = 0 to SAMPLER_COUNT - 1 do
    if i > 0 then print_char ',';
    match Generator.run (Generator.GENERATOR_NAME SAMPLER_SIZE) SAMPLER_SIZE seed with
    | None -> print_string "null"
    | Some input -> print_json (Generator.encode_input input)
  done;
  print_endline "]"
'''


def normalize_extraction(directory, stem='samples'):
    """Apply the pinned upstream integer-alias workaround to both extracted files."""
    changed = []
    for extension in ['ml', 'mli']:
        path = directory / f'{stem}.{extension}'
        original = path.read_text()
        normalized = re.sub(r'\btype int =\s*int\b',
                            'type qc_runtime_int = int\ntype int = qc_runtime_int', original)
        if normalized != original:
            (directory / f'{stem}.extracted.{extension}').write_text(original)
            path.write_text(normalized)
            changed.append(path.name)
    return changed


def execute(session, candidate, samples, size, seed, derive_only=False):
    session.report.update(candidate=candidate, samples=samples, size=size, seed=seed,
                          derive_only=derive_only, generator_proof='not_checked')
    session.check()
    for name in session.sequence:
        source = (session.sources / 'property/candidates' / name / 'Candidate.v').read_text()
        validate_tactic_form(source, (session.sources / 'property/Original.v').read_text())
        renamed = session.sources / 'property' / f'DeriveCandidate_{name}.v'
        renamed.write_text(renamed_candidate(source, name))
        session.compile(str(renamed.relative_to(session.sources)), f'candidate-derivation-copy-{name}')
    (session.sources / 'Derived.v').write_text(derivation(candidate))
    log = session.compile('Derived.v', 'derivation')
    session.report['schedule_variables'] = audit_schedule(log)
    found = assumptions(log)
    session.report['generator_factory_assumptions'] = found
    if found:
        raise CheckError(f'Generator factory has unsupported assumptions: {", ".join(found)}')
    session.command(['coqchk', '-silent', *COQ_FLAGS, 'Derived'], 'generator-kernel')
    session.report['normalized_extraction_files'] = normalize_extraction(session.sources, 'generator')
    session.fresh()
    if derive_only:
        return
    session.command(['ocamlfind', 'ocamlopt', '-package', 'zarith,unix', '-linkpkg',
                     '-rectypes', '-w', '-a', '-c', 'generator.mli'], 'compile-interface')
    driver = (DRIVER.replace('SAMPLER_SEED', str(seed))
                    .replace('SAMPLER_COUNT', str(samples))
                    .replace('SAMPLER_SIZE', str(size))
                    .replace('GENERATOR_NAME', f'genSizedSuchThat_predicate_{candidate}_O'))
    (session.sources / 'driver.ml').write_text(driver)
    session.command(['ocamlfind', 'ocamlopt', '-package', 'zarith,unix', '-linkpkg',
                     '-rectypes', '-w', '-a', 'generator.ml', 'driver.ml',
                     '-o', 'sampler'], 'compile-executable')
    session.fresh()
    output = session.command([str(session.sources / 'sampler')], 'execution', coq=False)
    try:
        values = json.loads(output)
    except json.JSONDecodeError as error:
        raise CheckError(f'Invalid typed JSON from sampler: {error}') from error
    if not isinstance(values, list) or len(values) != samples:
        raise CheckError('Sampler did not return the requested number of values')
    (session.directory / 'samples.json').write_text(json.dumps(values, indent=2) + '\n')
    session.report.update(generated=sum(x is not None for x in values),
                          failed=sum(x is None for x in values))
    session.fresh()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('property', type=Path)
    parser.add_argument('--candidate', required=True, help='candidate directory, e.g. v002')
    parser.add_argument('--samples', type=positive, default=100)
    parser.add_argument('--size', type=nonnegative, default=30)
    parser.add_argument('--seed', type=nonnegative, default=0)
    parser.add_argument('--timeout', type=positive, default=120, help='seconds per subprocess')
    parser.add_argument('--derive-only', action='store_true', help='verify tactic generation and extraction')
    args = parser.parse_args()
    session = None
    try:
        session = Session(args.property, selected=args.candidate, timeout=args.timeout)
        execute(session, args.candidate, args.samples, args.size, args.seed, args.derive_only)
        print(f'Equivalence checked; tactic generator derived for {args.candidate}: {session.finish()}')
        return 0
    except (CheckError, OSError, UnicodeError) as error:
        if session:
            print(f'Report: {session.finish(error)}', file=sys.stderr)
        print(error, file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
