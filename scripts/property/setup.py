"""Shared, property-independent specification and implementation manifests.

All authored paths are relative to their manifest, constrained to this worktree,
and identified by exact file hashes. PATH executables (for example python3) stay
as argv command names; local executables and script arguments are resolved and
hashed. Imported code must be listed explicitly in ``dependencies``.
"""
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
import shutil
import tomllib

from .bridge import ROOT
from .model import CompileError


class _FrozenDict(dict):
    def _immutable(self, *args, **kwargs):
        raise TypeError('shared setup is immutable')
    __setitem__ = __delitem__ = clear = pop = popitem = setdefault = update = __ior__ = _immutable


class _FrozenList(list):
    def _immutable(self, *args, **kwargs):
        raise TypeError('shared setup is immutable')
    __setitem__ = __delitem__ = append = clear = extend = insert = pop = remove = reverse = sort = __iadd__ = __imul__ = _immutable


def _freeze(value):
    if isinstance(value, dict):
        return _FrozenDict((key, _freeze(item)) for key, item in value.items())
    if isinstance(value, list):
        return _FrozenList(_freeze(item) for item in value)
    if isinstance(value, tuple):
        return tuple(_freeze(item) for item in value)
    return value


@dataclass(frozen=True)
class SpecificationContext:
    manifest: Path
    id: str
    sources: tuple[Path, ...]
    profile: str
    namespace: str
    hashes: dict[str, str]

    def __post_init__(self):
        object.__setattr__(self, 'sources', tuple(self.sources))
        object.__setattr__(self, 'hashes', _freeze(self.hashes))


@dataclass(frozen=True)
class ImplementationSetup:
    manifest: Path
    specification: str
    external: tuple[dict, ...]
    commands: dict[str, list[str]]
    hashes: dict[str, str]

    def __post_init__(self):
        for name in ('external', 'commands', 'hashes'):
            value = getattr(self, name)
            object.__setattr__(self, name, _freeze(tuple(value) if name == 'external' else value))


_NAMESPACES = {'fixture': 'FixtureSpec', 'p4': 'P4Spec', 'wasm': 'WasmSpec'}


def _error(manifest, code, message, **details):
    raise CompileError(f'{manifest}: {message}', code=code,
                       details={'manifest': str(manifest), **details})


def _within_root(path, manifest):
    try:
        resolved = path.resolve()
    except (ValueError, OSError) as error:
        _error(manifest, 'invalid_path', f'invalid path {str(path)!r}: {error}', path=str(path))
    if not resolved.is_relative_to(ROOT.resolve()):
        _error(manifest, 'path_outside_worktree', f'path outside worktree: {path}', path=str(path))
    return resolved


def _file(value, manifest, field):
    if not isinstance(value, str) or not value.strip():
        _error(manifest, 'invalid_path', f'{field} requires a nonempty file path', field=field)
    path = _within_root(manifest.parent / value, manifest)
    if not path.is_file():
        _error(manifest, 'missing_file', f'{field} file is missing: {path}', field=field, path=str(path))
    return path


def _hash(path, manifest):
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as error:
        _error(manifest, 'unreadable_file', f'cannot read {path}: {error}', path=str(path))


def _read_manifest(path, filename):
    path = Path(path)
    if not path.is_absolute():
        # Relative selection always starts at the worktree, never process cwd.
        path = ROOT / path
    if path.is_dir():
        path /= filename
    manifest = _within_root(path, path)
    if not manifest.is_file():
        _error(manifest, 'missing_file', 'manifest file is missing')
    try:
        data = tomllib.loads(manifest.read_text())
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        _error(manifest, 'invalid_manifest', f'invalid TOML manifest: {error}')
    return manifest, data


def _fields(data, allowed, manifest, section):
    if not isinstance(data, dict):
        _error(manifest, 'invalid_manifest', f'{section} must be a table', section=section)
    unknown = set(data) - allowed
    if unknown:
        _error(manifest, 'unknown_field', f'unknown {section} fields: {", ".join(sorted(unknown))}',
               section=section, fields=sorted(unknown))


def _identifier(value, manifest, field):
    if (not isinstance(value, str) or not value.strip() or value != value.strip()
            or any(character.isspace() for character in value)):
        _error(manifest, 'invalid_identifier', f'{field} requires a nonempty identifier', field=field)
    return value


def load_specification(path):
    """Load Specification.toml without selecting a property or implementation."""
    manifest, data = _read_manifest(path, 'Specification.toml')
    _fields(data, {'id', 'sources', 'profile', 'namespace'}, manifest, 'specification')
    identifier = _identifier(data.get('id'), manifest, 'id')
    profile = data.get('profile')
    if not isinstance(profile, str) or profile not in _NAMESPACES:
        _error(manifest, 'invalid_profile', 'profile must be fixture, p4, or wasm', profile=profile)
    namespace = data.get('namespace', _NAMESPACES[profile])
    if namespace != _NAMESPACES[profile]:
        _error(manifest, 'invalid_namespace', f'{profile} requires namespace {_NAMESPACES[profile]}',
               profile=profile, namespace=namespace)
    values = data.get('sources')
    if not isinstance(values, list) or not values:
        _error(manifest, 'invalid_sources', 'sources requires a nonempty ordered array of file paths')
    sources = tuple(_file(value, manifest, 'sources') for value in values)
    if len(set(sources)) != len(sources):
        _error(manifest, 'duplicate_source', 'sources contains duplicate resolved paths')
    hashes = {str(file): _hash(file, manifest) for file in (manifest, *sources)}
    return SpecificationContext(manifest, identifier, sources, profile, namespace, hashes)


def _dependencies(data, manifest, hashes, section):
    values = data.get('dependencies', [])
    if not isinstance(values, list):
        _error(manifest, 'invalid_dependencies', f'{section}.dependencies must be an array of file paths')
    seen = set()
    for value in values:
        file = _file(value, manifest, f'{section}.dependencies')
        if file in seen:
            _error(manifest, 'duplicate_dependency', f'duplicate dependency: {file}', path=str(file))
        seen.add(file)
        hashes[str(file)] = _hash(file, manifest)


def _python_operands(values):
    """Identify Python's script and literal option operands without evaluating argv."""
    literals = set()
    if not re.fullmatch(r'(?:python|pypy)(?:[0-9]+(?:\.[0-9]+)*)?', Path(values[0]).name):
        return None, literals
    index = 1
    while index < len(values):
        value = values[index]
        if value == '-':
            return None, literals
        if value.startswith(('-c', '-m')):
            if value in ('-c', '-m') and index + 1 < len(values):
                literals.add(index + 1)
            return None, literals
        if value == '--':
            return (index + 1 if index + 1 < len(values) else None), literals
        if value in ('-W', '-X', '--check-hash-based-pycs'):
            if index + 1 < len(values):
                literals.add(index + 1)
            index += 2
        elif value.startswith('-'):
            index += 1
        else:
            return index, literals
    return None, literals


def _command(values, manifest, hashes, adapter):
    if (not isinstance(values, list) or not values or
            any(not isinstance(value, str) or '\x00' in value for value in values) or not values[0]):
        _error(manifest, 'invalid_command', f'{adapter}: command requires an explicit nonempty argv array')
    executable = values[0]
    result = list(values)
    local = manifest.parent / executable
    if '/' in executable or '\\' in executable or local.exists():
        file = _file(executable, manifest, f'{adapter}.command[0]')
        result[0] = str(file)
        hashes[str(file)] = _hash(file, manifest)
    elif not re.fullmatch(r'[A-Za-z0-9_.+\-]+', executable) or shutil.which(executable) is None:
        _error(manifest, 'invalid_command', f'{adapter}: executable not found on PATH: {executable}')
    # Shell evaluation is never used. Local file arguments are independent of cwd;
    # ordinary literal values/options remain verbatim argv entries.
    script_index, literal_operands = _python_operands(values)
    for index, value in enumerate(values[1:], 1):
        if index in literal_operands or value.startswith('-'):
            continue
        candidate = manifest.parent / value
        explicit_path = value.startswith(('./', '../'))
        if candidate.is_file() or explicit_path or index == script_index:
            file = _file(value, manifest, f'{adapter}.command[{index}]')
            result[index] = str(file)
            hashes[str(file)] = _hash(file, manifest)
    return result


def load_implementation(path, specification: SpecificationContext):
    """Load an adapter catalog; relation typing remains the compiler's job.

    ``dependencies`` may appear at the top level or in an external table. A
    relation maps to one adapter; multiple relations may share that adapter only
    when they declare the same resolved command.
    """
    manifest, data = _read_manifest(path, 'Adapter.toml')
    _fields(data, {'specification', 'external', 'dependencies'}, manifest, 'implementation')
    identifier = _identifier(data.get('specification'), manifest, 'specification')
    if identifier != specification.id:
        _error(manifest, 'specification_mismatch',
               f'implementation targets {identifier}, selected specification is {specification.id}',
               expected=specification.id, actual=identifier)
    hashes = {str(manifest): _hash(manifest, manifest)}
    _dependencies(data, manifest, hashes, 'implementation')
    entries = data.get('external', [])
    if not isinstance(entries, list):
        _error(manifest, 'invalid_external', 'external must be an array of tables')
    external, commands, relations = [], {}, set()
    allowed = {'relation', 'adapter', 'command', 'conversion', 'observed_outputs', 'dependencies'}
    for entry in entries:
        _fields(entry, allowed, manifest, 'external')
        relation = _identifier(entry.get('relation'), manifest, 'external.relation')
        adapter = _identifier(entry.get('adapter'), manifest, 'external.adapter')
        if relation in relations:
            _error(manifest, 'duplicate_relation', f'duplicate external relation: {relation}', relation=relation)
        relations.add(relation)
        if entry.get('conversion') != 'json-v1':
            _error(manifest, 'invalid_conversion', f'{relation}: conversion must be json-v1', relation=relation)
        positions = entry.get('observed_outputs')
        if (not isinstance(positions, list) or
                any(type(position) is not int or position < 0 for position in positions) or
                len(set(positions)) != len(positions)):
            _error(manifest, 'invalid_observed_outputs', f'{relation}: observed_outputs requires unique natural positions', relation=relation)
        command = _command(entry.get('command'), manifest, hashes, adapter)
        if adapter in commands and commands[adapter] != command:
            _error(manifest, 'conflicting_command', f'conflicting commands for adapter: {adapter}', adapter=adapter)
        commands[adapter] = command
        _dependencies(entry, manifest, hashes, f'external.{relation}')
        external.append({'relation': relation, 'adapter': adapter, 'conversion': 'json-v1',
                         'observed_outputs': sorted(positions)})
    return ImplementationSetup(manifest, identifier, tuple(external), commands, hashes)
