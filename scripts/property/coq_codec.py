"""Render the common Input wire format from the translator's type metadata.

``type_schema`` maps each named wire type to its ``coq_type`` and a list of
``constructors``. Each constructor has its wire ``name``, generated ``coq_name``,
and ordered ``fields`` (wire type names). The primitive wire types nat, int,
text, and bool are implicit. Text uses the same UTF-8 bytes as the AL bridge.
"""
import json
import re

from .codec import CodecError


_PRIMITIVES = {'nat', 'int', 'text', 'bool'}
_COQ_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def _identifier(value, description):
    if not isinstance(value, str) or not _COQ_NAME.fullmatch(value):
        raise CodecError(f'invalid Coq {description}: {value!r}')
    return value


def constructor_schema(type_schema):
    """Validate translator metadata and return the Python decoder's case map."""
    if not isinstance(type_schema, dict):
        raise CodecError('type schema must be an object')
    constructors = {}
    for name, declaration in type_schema.items():
        if not isinstance(name, str) or not name or name in _PRIMITIVES:
            raise CodecError(f'invalid named wire type: {name!r}')
        if not isinstance(declaration, dict):
            raise CodecError(f'invalid declaration for {name}')
        _identifier(declaration.get('coq_type'), f'type for {name}')
        cases = declaration.get('constructors')
        if not isinstance(cases, list):
            raise CodecError(f'{name}: constructors must be a list')
        constructors[name] = {}
        coq_names = set()
        for case in cases:
            if not isinstance(case, dict):
                raise CodecError(f'{name}: invalid constructor')
            token = case.get('name')
            if not isinstance(token, str) or not token or token in constructors[name]:
                raise CodecError(f'{name}: missing or duplicate wire constructor {token!r}')
            coq_name = _identifier(case.get('coq_name'), f'constructor for {name}.{token}')
            if coq_name in coq_names:
                raise CodecError(f'{name}: duplicate Coq constructor {coq_name}')
            coq_names.add(coq_name)
            fields = case.get('fields')
            if not isinstance(fields, list) or any(not isinstance(item, str) for item in fields):
                raise CodecError(f'{name}.{token}: fields must be a list of wire types')
            constructors[name][token] = tuple(fields)
    for name, cases in constructors.items():
        for token, fields in cases.items():
            for typ in fields:
                if typ not in _PRIMITIVES and typ not in constructors:
                    raise CodecError(f'{name}.{token}: unknown field type {typ}')
    return constructors


def _coq_text(text):
    """Quote UTF-8 bytes without relying on Coq's source escape conventions."""
    chunks, printable = [], []

    def flush():
        if printable:
            chunks.append('"' + ''.join(printable) + '"')
            printable.clear()

    for byte in text.encode('utf-8'):
        if 32 <= byte < 127:
            printable.append('""' if byte == 34 else chr(byte))
        else:
            flush()
            chunks.append(f'(String (Ascii.ascii_of_nat {byte}) EmptyString)')
    flush()
    return _append(chunks)


def _append(expressions):
    if not expressions:
        return '""'
    result = expressions[-1]
    for expression in reversed(expressions[:-1]):
        result = f'(String.append {expression} {result})'
    return result


def _json_text(value):
    return _coq_text(json.dumps(value, ensure_ascii=False, separators=(',', ':')))


def _support():
    # Escape every JSON control byte. The remaining bytes retain the bridge's
    # UTF-8 text representation, including multibyte Unicode characters.
    return '''From Coq Require Import String Ascii Bool ZArith DecimalString.
Open Scope string_scope.

Definition property_json_hex (n : nat) : ascii :=
  Ascii.ascii_of_nat (if Nat.ltb n 10 then 48 + n else 87 + n).
Definition property_json_escape_char (c : ascii) : string :=
  let n := Ascii.nat_of_ascii c in
  if Nat.eqb n 34 then QUOTE
  else if Nat.eqb n 92 then BACKSLASH
  else if Nat.ltb n 32 then
    String.append CONTROL
      (String (property_json_hex (Nat.div n 16))
        (String (property_json_hex (Nat.modulo n 16)) EmptyString))
  else String c EmptyString.
Fixpoint property_json_escape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String.append (property_json_escape_char c)
                                 (property_json_escape rest)
  end.
Definition property_json_quote (s : string) : string :=
  String.append DELIMITER (String.append (property_json_escape s) DELIMITER).
Definition property_json_nat (n : nat) : string :=
  String.append NAT_PREFIX
    (String.append (NilZero.string_of_uint (Nat.to_uint n)) NUMBER_SUFFIX).
Definition property_json_int (n : Z) : string :=
  String.append INT_PREFIX
    (String.append (NilZero.string_of_int (Z.to_int n)) NUMBER_SUFFIX).
Definition property_json_text (s : string) : string :=
  String.append TEXT_PREFIX
    (String.append (property_json_quote s) OBJECT_SUFFIX).
Definition property_json_bool (b : bool) : string :=
  if b then TRUE_VALUE else FALSE_VALUE.

'''.replace('QUOTE', _coq_text('\\"')).replace('BACKSLASH', _coq_text('\\\\')).replace(
        'CONTROL', _coq_text('\\u00')).replace('DELIMITER', _coq_text('"')).replace(
        'NAT_PREFIX', _coq_text('{"type":"nat","value":"')).replace(
        'INT_PREFIX', _coq_text('{"type":"int","value":"')).replace(
        'NUMBER_SUFFIX', _coq_text('"}')).replace(
        'TEXT_PREFIX', _coq_text('{"type":"text","value":')).replace(
        'OBJECT_SUFFIX', _coq_text('}')).replace('TRUE_VALUE', _json_text(
            {'type': 'bool', 'value': True})).replace('FALSE_VALUE', _json_text(
                {'type': 'bool', 'value': False}))


def _components(type_schema, roots):
    """Order reachable types by dependency, retaining mutually recursive groups."""
    indexes, lowlinks, stack, active, components = {}, {}, [], set(), []

    def visit(name):
        indexes[name] = lowlinks[name] = len(indexes)
        stack.append(name)
        active.add(name)
        for case in type_schema[name]['constructors']:
            for dependency in case['fields']:
                if dependency in _PRIMITIVES:
                    continue
                if dependency not in indexes:
                    visit(dependency)
                    lowlinks[name] = min(lowlinks[name], lowlinks[dependency])
                elif dependency in active:
                    lowlinks[name] = min(lowlinks[name], indexes[dependency])
        if indexes[name] == lowlinks[name]:
            component = []
            while True:
                item = stack.pop()
                active.remove(item)
                component.append(item)
                if item == name:
                    break
            components.append(component)

    for root in roots:
        if root not in _PRIMITIVES and root not in indexes:
            visit(root)
    return components


def render_input_codec(fields, type_schema, *, input_type='Input', function_name='encode_input'):
    """Emit Coq definitions for the declared fields and their reachable ADTs.

    Imports for generated ADT declarations belong to the enclosing property.
    This source can be appended after its Input record and predicate. An Input
    field may override the default ``input_<name>`` projection with
    ``coq_projection``. No Show instance participates in the wire encoding.
    """
    constructors = constructor_schema(type_schema)
    _identifier(input_type, 'Input type')
    _identifier(function_name, 'encoder name')
    if not isinstance(fields, (list, tuple)):
        raise CodecError('Input fields must be a list')
    seen, projections = set(), []
    for field in fields:
        if not isinstance(field, dict) or not isinstance(field.get('name'), str):
            raise CodecError('Input field must have a name')
        name = field['name']
        if not name or name in seen:
            raise CodecError(f'duplicate or empty Input field: {name!r}')
        seen.add(name)
        typ = field.get('type')
        if not isinstance(typ, str) or typ not in _PRIMITIVES and typ not in constructors:
            raise CodecError(f'{name}: unknown Input type {typ!r}')
        projections.append(_identifier(field.get('coq_projection', 'input_' + name),
                                       f'projection for {name}'))
    names = {typ: f'property_json_type_{index}'
             for index, typ in enumerate(sorted(type_schema))}
    names.update({typ: 'property_json_' + typ for typ in _PRIMITIVES})
    lines = [_support()]
    for component in _components(type_schema, [field['type'] for field in fields]):
        recursive = len(component) > 1 or any(
            typ in case['fields'] for typ in component
            for case in type_schema[typ]['constructors'])
        for index, typ in enumerate(component):
            declaration = type_schema[typ]
            keyword = 'with' if index else 'Fixpoint' if recursive else 'Definition'
            structural = ' {struct value}' if recursive else ''
            lines.append(f'{keyword} {names[typ]} (value : {declaration["coq_type"]})'
                         f'{structural} : string :=\n  match value with')
            for case in declaration['constructors']:
                variables = [f'arg_{position}' for position in range(len(case['fields']))]
                pattern = ' '.join([case['coq_name'], *variables])
                prefix = json.dumps({'type': typ, 'constructor': case['name']},
                                    ensure_ascii=False, separators=(',', ':'))[:-1] + ',"args":['
                expressions = [_coq_text(prefix)]
                for position, (arg_type, variable) in enumerate(zip(case['fields'], variables)):
                    if position:
                        expressions.append(_coq_text(','))
                    expressions.append(f'({names[arg_type]} {variable})')
                expressions.append(_coq_text(']}'))
                lines.append(f'  | {pattern} => {_append(expressions)}')
            lines.append('  end' + ('.\n' if index == len(component) - 1 else ''))
    expressions = [_coq_text('{')]
    for index, (field, projection) in enumerate(zip(fields, projections)):
        prefix = (',' if index else '') + json.dumps(field['name'], ensure_ascii=False) + ':'
        expressions.extend([_coq_text(prefix), f'({names[field["type"]]} ({projection} i))'])
    expressions.append(_coq_text('}'))
    lines.append(f'Definition {function_name} (i : {input_type}) : string :=\n'
                 f'  {_append(expressions)}.\n')
    return '\n'.join(lines)

def _finite_type_ranks(type_schema):
    """Find finite constructor trees before emitting total GenSized instances."""
    ranks = {}
    changed = True
    while changed:
        changed = False
        for name, declaration in type_schema.items():
            for case in declaration['constructors']:
                if all(field in _PRIMITIVES or field in ranks for field in case['fields']):
                    rank = 1 + max((ranks.get(field, 0) for field in case['fields']), default=0)
                    if name not in ranks or rank < ranks[name]:
                        ranks[name] = rank
                        changed = True
    missing = sorted(set(type_schema) - set(ranks))
    if missing:
        raise CodecError('no finite constructor value for named types: ' + ', '.join(missing))
    return ranks


def _choose_generators(generators):
    if len(generators) == 1:
        return generators[0]
    # Keep constructor generators inside the bind. Constructing every recursive
    # alternative eagerly can take exponential work before any branch is chosen.
    branches = [f"| {'S (' * index}O{')' * index} => {generator}"
                for index, generator in enumerate(generators[:-1])]
    branches.append(f'| _ => {generators[-1]}')
    return (f'(bindGen (choose (0, {len(generators) - 1})%nat) (fun choice => '
            'match choice with ' + ' '.join(branches) + ' end))')


def _constructor_generator(case, field_generator):
    arguments = [f'field_{index}' for index in range(len(case['fields']))]
    constructor = ' '.join([case['coq_name'], *arguments])
    expression = f'(returnGen ({constructor}))'
    for argument, field in reversed(list(zip(arguments, case['fields']))):
        expression = f'(bindGen ({field_generator(field)}) (fun {argument} => {expression}))'
    return expression


def _render_adt_generators(type_schema, ranks):
    names = {name: f'property_gen_type_{index}'
             for index, name in enumerate(sorted(type_schema))}
    bases = {name: f'property_gen_base_{index}'
             for index, name in enumerate(sorted(type_schema))}
    types = {name: declaration['coq_type'] for name, declaration in type_schema.items()}
    types.update(nat='nat', int='Z', text='string', bool='bool')
    lines = []
    # A member of a mutual group need not have a constructor without a recursive
    # field. Its size-zero generator uses a finite tree through lower rank types.
    for name in sorted(type_schema, key=lambda name: (ranks[name], name)):
        cases = [case for case in type_schema[name]['constructors']
                 if 1 + max((ranks.get(field, 0) for field in case['fields']), default=0)
                 == ranks[name]]
        generators = [_constructor_generator(case, lambda field:
                      f'@arbitrarySized {types[field]} _ 0' if field in _PRIMITIVES
                      else bases[field]) for case in cases]
        lines.append(f'Definition {bases[name]} : G {types[name]} :=\n'
                     f'  {_choose_generators(generators)}.\n')
    for component in _components(type_schema, list(type_schema)):
        recursive = len(component) > 1 or any(
            name in case['fields'] for name in component
            for case in type_schema[name]['constructors'])
        for index, name in enumerate(component):
            keyword = 'with' if index else 'Fixpoint' if recursive else 'Definition'
            structural = ' {struct size}' if recursive else ''
            generators = [_constructor_generator(case, lambda field:
                          f'{names[field]} rest' if field in component else
                          f'@arbitrarySized {types[field]} _ size')
                          for case in type_schema[name]['constructors']]
            lines.append(f'{keyword} {names[name]} (size : nat){structural} : G {types[name]} :=\n'
                         '  match size with\n'
                         f'  | O => {bases[name]}\n'
                         f'  | S rest => {_choose_generators(generators)}\n'
                         '  end' + ('.\n' if index == len(component) - 1 else ''))
        for name in component:
            lines.append(f'#[global] Instance {names[name]}_instance : GenSized {types[name]} :=\n'
                         f'  {{| arbitrarySized := {names[name]} |}}.\n')
    return '\n'.join(lines)


def render_type_generators(type_schema):
    """Render constructor generators and provide UTF-8 text to the typed wire.

    Coq strings are byte lists. An unrestricted ascii generator can produce
    invalid UTF-8, which is not a text value in the JSON/native interface.
    Generate Unicode scalar values and encode their bytes before extraction.
    These are generator instances, with no soundness/completeness claim.
    """
    constructor_schema(type_schema)
    ranks = _finite_type_ranks(type_schema)
    text = '''Definition property_utf8_scalar (n : nat) : string :=
  let byte n := Ascii.ascii_of_nat n in
  if Nat.ltb n 128 then String (byte n) EmptyString else
  if Nat.ltb n 2048 then
    String (byte (192 + n / 64)) (String (byte (128 + n mod 64)) EmptyString)
  else if Nat.ltb n 65536 then
    String (byte (224 + n / 4096))
      (String (byte (128 + (n / 64) mod 64))
        (String (byte (128 + n mod 64)) EmptyString))
  else String (byte (240 + n / 262144))
    (String (byte (128 + (n / 4096) mod 64))
      (String (byte (128 + (n / 64) mod 64))
        (String (byte (128 + n mod 64)) EmptyString))).
Fixpoint property_gen_text (size : nat) : G string :=
  match size with
  | O => returnGen EmptyString
  | S rest => bindGen (choose (0, 1112063)%nat) (fun index =>
      let scalar := if Nat.ltb index 55296 then index else (index + 2048)%nat in
      bindGen (property_gen_text rest) (fun tail =>
        returnGen (String.append (property_utf8_scalar scalar) tail)))
  end.
#[global] Instance property_gen_sized_text : GenSized string :=
  {| arbitrarySized := fun size => bindGen (choose (0, size)%nat) property_gen_text |}.
'''
    return text + _render_adt_generators(type_schema, ranks) + '\n'
