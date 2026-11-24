"""Lower multiline property wrappers using the pinned native SpecTec frontend."""
from dataclasses import dataclass
from difflib import SequenceMatcher
from pathlib import Path
import hashlib
import json
import re
import subprocess

from .bridge import ROOT, build_bridge
from .compiler import frontend_check
from .model import CompileError


@dataclass(frozen=True)
class LoweredProperty:
    name: str
    source: Path
    config: Path
    source_map: dict


def _mask(text, source):
    """Hide lexical comments/literals while retaining offsets and newlines."""
    result = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('(;', i):
                result[i:i + 2] = '  '
                depth += 1
                i += 2
            elif text.startswith(';)', i):
                result[i:i + 2] = '  '
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    result[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\':
                result[i:i + 2] = '  '
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != '\n':
                    result[i] = ' '
                i += 1
        elif text.startswith(';;', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            result[i:end] = ' ' * (end - i)
            i = end
        elif text.startswith('(;', i):
            result[i:i + 2] = '  '
            depth, i = 1, i + 2
        elif text[i] == '"':
            result[i] = ' '
            string, i = True, i + 1
        else:
            i += 1
    if depth or string:
        line = text.count('\n', 0, i) + 1
        raise CompileError(f'{source}:{line}: unclosed comment or string')
    return ''.join(result)


def _parse(path):
    text = path.read_text()
    mask = _mask(text, path)
    # String contents are hidden for splitting, but a literal-only goal is meaningful.
    lines, masks = text.splitlines(), mask.splitlines()
    significant = [i for i, line in enumerate(masks) if line.strip()]
    if not significant:
        raise CompileError(f'{path}:1: expected property declaration')
    header = significant[0]
    match = re.fullmatch(r'\s*property\s*\[([A-Za-z][\w-]*)\]\s*:\s*', masks[header])
    if not match:
        raise CompileError(f'{path}:{header + 1}: property header must occupy its own line')
    if len(significant) < 2:
        raise CompileError(f'{path}:{header + 1}: missing typed input line')
    binder_line = significant[1]
    line = masks[binder_line]
    inputs = []
    i = 0
    while i < len(line):
        if line[i].isspace():
            i += 1
            continue
        start = i
        if line[i] != '(':
            raise CompileError(f'{path}:{binder_line + 1}: inputs and goal must start on separate lines')
        depth = 1
        i += 1
        while i < len(line) and depth:
            depth += (line[i] == '(') - (line[i] == ')')
            i += 1
        if depth:
            raise CompileError(f'{path}:{binder_line + 1}: unclosed typed input binder')
        inside = lines[binder_line][start + 1:i - 1]
        if not inside.strip() and not inputs and not line[i:].strip():
            break
        binder = re.fullmatch(r'\s*([a-z][A-Za-z0-9_\']*)\s*:\s*(.+?)\s*', inside)
        if not binder:
            raise CompileError(f'{path}:{binder_line + 1}: expected (name : type)')
        name, typ = binder.groups()
        if name in [item[0] for item in inputs]:
            raise CompileError(f'{path}:{binder_line + 1}: duplicate input {name}')
        inputs.append((name, typ))
    goal_lines, conditions = [], []
    for index in range(binder_line + 1, len(lines)):
        stripped = masks[index].strip()
        if stripped.startswith('--'):
            dash = masks[index].index('--')
            conditions.append((index + 1, (lines[index][:dash] + lines[index][dash + 2:]).strip()))
        elif conditions:
            # Preserve blank/comment continuation lines for both native lexing
            # and exact source positions inside multiline premises.
            number, previous = conditions[-1]
            conditions[-1] = (number, previous + '\n' + lines[index])
        else:
            goal_lines.append((index + 1, lines[index]))
    while goal_lines and not goal_lines[0][1].strip():
        goal_lines.pop(0)
    while goal_lines and not goal_lines[-1][1].strip():
        goal_lines.pop()
    if not goal_lines or not _mask('\n'.join(x[1] for x in goal_lines), path).strip():
        raise CompileError(f'{path}:{binder_line + 2}: missing goal')
    goal = '\n'.join(x[1] for x in goal_lines).strip()
    # Relation judgment recognition is only wrapper syntax; native parsing handles its body.
    def premise(value):
        clean = _mask(value, path).lstrip()
        return value if re.match(r'(?:[A-Z][\w-]*\s*:|if\b|var\b|otherwise\b|debug\b)', clean) else 'if ' + value
    return match[1], inputs, binder_line + 1, (goal_lines[0][0], premise(goal)), [
        (line, premise(value)) for line, value in conditions]


class _Writer:
    def __init__(self, path, source_map):
        self.path, self.source_map, self.lines = path, source_map, []

    def add(self, text, original, line, variables=None, original_column=1, variable_roles=None):
        masks = _mask(text, original).split('\n')
        originals = Path(original).read_text().splitlines()
        for offset, value in enumerate(text.split('\n')):
            masked = masks[offset]
            # Align wrapper insertions to the source line before alpha renaming.
            # Equal spans retain exact original columns, including expression
            # tokens after an inserted `-- if` prefix.
            original_line = originals[line + offset - 1] if 0 < line + offset <= len(originals) else ''
            base = [original_column] * (len(value) + 1)
            for operation, a, b, c, d in SequenceMatcher(a=original_line, b=value, autojunk=False).get_opcodes():
                for index in range(c, d):
                    base[index] = (a + index - c + 1) if operation == 'equal' else min(a + 1, len(original_line) + 1)
            base[-1] = len(original_line) + 1
            rendered, columns, cursor = '', [], 0
            for match in re.finditer(r'[A-Za-z][A-Za-z0-9_\']*', masked):
                if not variables or match[0] not in variables or (match.start() and masked[match.start() - 1] in '$.'):
                    continue
                if variable_roles is not None and (line + offset, base[match.start()]) not in variable_roles:
                    continue
                rendered += value[cursor:match.start()]
                columns.extend(base[cursor:match.start()])
                replacement = variables[match[0]]
                rendered += replacement
                public_columns = base[match.start():match.end()]
                columns.extend(public_columns[min(i, len(public_columns) - 1)] for i in range(len(replacement)))
                cursor = match.end()
            rendered += value[cursor:]
            columns.extend(base[cursor:])
            self.lines.append(rendered)
            row = {'generated_file': str(self.path),
                   'generated_line': len(self.lines), 'file': str(original),
                   'line': line + offset, 'columns': columns}
            # Native positions count UTF-8 bytes; public columns count characters.
            # Keep the character map for writer alignment and add a native map
            # only where a multibyte character makes the coordinate systems differ.
            if len(rendered.encode('utf-8')) != len(rendered):
                row['byte_columns'] = [column for character, column in zip(rendered, columns)
                                       for _ in character.encode('utf-8')] + [columns[-1]]
            self.source_map['lines'].append(row)

    def save(self):
        self.path.write_text('\n'.join(self.lines) + '\n')


def remap_locations(value, source_map):
    """Return copied JSON/error text with generated locations and labels restored.

    Typed runtime values are opaque: text returned by a specification is never
    rewritten even if it happens to contain an internal name or source path.
    """
    if isinstance(value, dict):
        if 'type' in value and 'value' in value:
            return dict(value)
        if isinstance(value.get('file'), str) and isinstance(value.get('line'), int):
            row = next((row for row in source_map.get('lines', [])
                        if row['generated_file'] == value['file'] and row['generated_line'] == value['line']), None)
            if row:
                mapped = {**value, 'file': row['file'], 'line': row['line']}
                columns = row.get('byte_columns', row['columns'])
                if isinstance(value.get('column'), int) and columns:
                    mapped['column'] = columns[min(max(value['column'], 0), len(columns) - 1)] - 1
                return mapped
        return {key: remap_locations(item, source_map) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [remap_locations(item, source_map) for item in value]
    if not isinstance(value, str):
        return value
    lookup = {(row['generated_file'], row['generated_line']): row for row in source_map.get('lines', [])}
    paths = sorted({key[0] for key in lookup}, key=len, reverse=True)
    for path in paths:
        def replace(match):
            row = lookup.get((path, int(match['line'])))
            if not row:
                return match[0]
            columns = row.get('byte_columns', row['columns'])
            def column(number, columns=columns):
                return columns[min(max(int(number) - 1, 0), len(columns) - 1)] if columns else 1
            result = f"{row['file']}:{row['line']}"
            if match['column']:
                result += match['separator'] + str(column(match['column']))
            if match['endline']:
                end = lookup.get((path, int(match['endline'])), row)
                result += f"-{end['line']}.{column(match['endcolumn'], end.get('byte_columns', end['columns']))}"
            return result
        pattern = re.escape(path) + r':(?P<line>\d+)(?:(?P<separator>[.:])(?P<column>\d+))?(?:-(?P<endline>\d+)\.(?P<endcolumn>\d+))?'
        value = re.sub(pattern, replace, value)
    for internal, public in source_map.get('variables', {}).items():
        value = re.sub(r'(?<![A-Za-z0-9_])' + re.escape(internal) + r'(?![A-Za-z0-9_])', public, value)
    return value


def lower_property(property_source: Path, specification_sources: list[Path], output_dir: Path):
    property_source = Path(property_source).resolve()
    sources = tuple(Path(source).resolve() for source in specification_sources)
    output_dir = Path(output_dir).resolve()
    try:
        name, inputs, binder_line, goal, conditions = _parse(property_source)
        output_dir.mkdir(parents=True, exist_ok=True)
        source_map = {'version': 1, 'property': str(property_source),
                      'specification_sources': [str(path) for path in sources],
                      'variables': {}, 'lines': []}
        probe = output_dir / 'declaration-probe.watsup'
        def native_lines(text):
            # SpecTec treats empty lines as declaration separators, even inside
            # parentheses. Empty comments preserve property expression spacing
            # and retain every physical line for source mapping.
            return '\n'.join(line if line.strip() else '(; ;)' for line in text.split('\n'))
        variable_roles = None
        def write_probe(rename=None):
            source_map['lines'] = [row for row in source_map['lines'] if row['generated_file'] != str(probe)]
            writer = _Writer(probe, source_map)
            writer.add('relation PropertyProbe: PROPERTYPROBE\nrule PropertyProbe/main: PROPERTYPROBE', property_source, 1)
            for variable, typ in inputs:
                writer.add(f'  -- var {rename.get(variable, variable) if rename else variable} : {typ}',
                           property_source, binder_line)
            for line, condition in [*conditions, goal]:
                writer.add(native_lines('  -- ' + condition), property_source, line, rename, variable_roles=variable_roles)
            writer.save()
        write_probe()
        executable = build_bridge()
        def native(operation):
            result = subprocess.run(['bash', str(ROOT / 'environment/env.sh'), 'frontend',
                                     str(executable), 'declaration', str(probe)],
                                    input=json.dumps({'sources': list(map(str, sources)),
                                                      'operation': operation}) + '\n',
                                    capture_output=True, text=True, timeout=120)
            if result.returncode:
                raise CompileError(remap_locations(result.stderr or result.stdout, source_map), code='frontend_error')
            return json.loads(result.stdout)
        discovery = native('names')
        names = discovery['names']
        variable_roles = {(location['line'], location['column'] + 1)
                          for location in remap_locations(discovery['occurrences'], source_map)}
        # Internal names are alphabetic, so native metavariable suffix stripping
        # cannot accidentally merge distinct local variables.
        identity = hashlib.sha256(property_source.read_bytes() + b'\0' +
                                  b'\0'.join(path.read_bytes() for path in sources)).hexdigest()
        prefix = 'property' + ''.join(chr(ord('a') + int(ch, 16)) for ch in identity[:16])
        rename = {name: prefix + 'v' + 'a' * (i + 1) for i, name in enumerate(names)}
        source_map['variables'] = {internal: public for public, internal in rename.items()}
        write_probe(rename)
        report = native('check')
        variables = report['variables']
        # Condition locals remain existential constructor witnesses. Only locals
        # used by Goal cross the Pre/Goal boundary and require observations.
        abi_variables = [item for i, item in enumerate(variables)
                         if i < len(inputs) or item['name'] in report['goal_variables']]
        if not inputs and abi_variables:
            raise CompileError(f'{property_source}:{binder_line}: the pinned frontend cannot '
                               'express a relation with zero inputs and witness outputs')
        source = output_dir / 'Property.lowered.watsup'
        writer = _Writer(source, source_map)
        for path in sources:
            writer.add(path.read_text().rstrip('\n'), path, 1)
            writer.add('', path, 1)
        for item in variables:
            writer.add(f"var {item['name']} : {item['type']}", property_source, binder_line)
        pre, goal_name = 'PropertyPre' + identity[:12], 'PropertyGoal' + identity[:12]
        all_types = [item['type'] for item in abi_variables]
        all_names = [item['name'] for item in abi_variables]
        def signature(types):
            return 'PROPERTYARGS' + ''.join(f' ({typ})' for typ in types)
        def arguments(names):
            return 'PROPERTYARGS' + ''.join(' ' + name for name in names)
        def hint(count):
            return (' hint(input ' + ' '.join(f'%{i}' for i in range(count)) + ')') if count else ''
        writer.add(f'relation {pre}: {signature(all_types)}' + hint(len(inputs)), property_source, binder_line)
        writer.add(f'rule {pre}/main: {arguments(all_names)}', property_source, binder_line, rename)
        for line, condition in conditions:
            if not re.match(r'\s*var\b', _mask(condition, property_source)):
                writer.add(native_lines('  -- ' + condition), property_source, line, rename, variable_roles=variable_roles)
        writer.add(f'relation {goal_name}: {signature(all_types)}' + hint(len(abi_variables)), property_source, goal[0])
        writer.add(f'rule {goal_name}/main: {arguments(all_names)}', property_source, goal[0], rename)
        writer.add(native_lines('  -- ' + goal[1]), property_source, goal[0], rename, variable_roles=variable_roles)
        writer.save()
        try:
            frontend_check(source)
        except CompileError as error:
            raise CompileError(remap_locations(str(error), source_map), code=error.code) from error
        config = output_dir / 'Property.internal.toml'
        config.write_text(f'precondition = "{pre}"\ngoal = "{goal_name}"\n')
        return LoweredProperty(name, source, config, source_map)
    except OSError as error:
        raise CompileError(f'{property_source}: {error}') from error
