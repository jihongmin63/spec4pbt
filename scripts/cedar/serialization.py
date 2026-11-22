"""Reconstruct Original.Input from the official theorem checker's captured binders.

The five callback payloads for P0 are the selected schedule's type, schema,
request types, environments, and expression.  All text is passed back to Coq;
this parser only finds top-level constructor boundaries.  Coq checks the
resulting expression and a per-row equality for all seven input fields.  The
benchmark states the fixed entity-name list literally, so the scheduler does
not generate it; ``scheduler_entity_names`` is therefore always ``None``.
"""
import re


class SerializationError(ValueError):
    pass


def _callback_text(text):
    if not isinstance(text, str) or not text.endswith("\n"):
        raise SerializationError("callback must end in exactly one record newline")
    return text[:-1]


def _coq_literal(display):
    """Decode upstream Show's strings and negative Z constructor arguments.

    Upstream displays ``int -1``, which Coq parses as subtraction.  The
    transformation is lexical and preserves all quoted Cedar string bytes.
    The untouched callback remains available in raw-attempts.jsonl.
    """
    output = []
    i = 0
    while i < len(display):
        c = display[i]
        if c == '"':
            decoded, i = _decode_show_string(display, i)
            output.append(_encode_coq_string(decoded))
            continue
        elif c == '-' and i + 1 < len(display) and display[i + 1].isdigit() and (
                i == 0 or not (display[i - 1].isalnum() or display[i - 1] == '_')):
            match = re.match(r'-[0-9]+', display[i:])
            output.append(f'({match.group(0)})%Z')
            i += len(match.group(0))
            continue
        else:
            output.append(c)
        i += 1
    return ''.join(output)


def _decode_show_string(display, start):
    """Read one QuickChick showString token, including its byte escapes."""
    values = []
    i = start + 1
    while i < len(display):
        c = display[i]
        if c == '"':
            if i + 1 < len(display) and display[i + 1] == '"':
                values.append(34)
                i += 2
                continue
            return values, i + 1
        if c == '\\':
            if i + 1 >= len(display):
                break
            escape = display[i + 1]
            if escape in {'t': 9, 'n': 10, 'r': 13, '"': 34, '\\': 92}:
                values.append({'t': 9, 'n': 10, 'r': 13, '"': 34, '\\': 92}[escape])
                i += 2
                continue
            digits = display[i + 1:i + 4]
            if len(digits) == 3 and digits.isdecimal() and int(digits) <= 255:
                values.append(int(digits))
                i += 4
                continue
            raise SerializationError('unsupported QuickChick string escape')
        code = ord(c)
        if code > 126 or code < 32:
            raise SerializationError('unescaped nonprintable Show byte')
        values.append(code)
        i += 1
    raise SerializationError('unterminated QuickChick Show string')


def _encode_coq_string(values):
    if all(32 <= code <= 126 for code in values):
        return '"' + ''.join('""' if code == 34 else chr(code) for code in values) + '"'
    term = 'EmptyString'
    for code in reversed(values):
        term = f'String (Ascii.ascii_of_nat {code}) ({term})'
    return f'({term})'


def _split_top(text, delimiter):
    parts = []
    start = 0
    stack = []
    quoted = False
    i = 0
    matching = {')': '(', ']': '[', '}': '{'}
    while i < len(text):
        c = text[i]
        if quoted:
            if c == '"':
                if i + 1 < len(text) and text[i + 1] == '"':
                    i += 2
                    continue
                quoted = False
            i += 1
            continue
        if c == '"':
            quoted = True
        elif c in "([{":
            stack.append(c)
        elif c in ")]}":
            if not stack or stack.pop() != matching[c]:
                raise SerializationError("unbalanced Coq constructor display")
        elif c == delimiter and not stack:
            parts.append(text[start:i].strip())
            start = i + 1
        i += 1
    if quoted or stack:
        raise SerializationError("unterminated Coq constructor display")
    parts.append(text[start:].strip())
    if any(not p for p in parts):
        raise SerializationError("empty Coq constructor component")
    return parts


def _schema(text):
    if not text.startswith("MkSchema "):
        raise SerializationError("captured schema does not begin with MkSchema")
    args = _split_top(text[len("MkSchema "):], ' ')
    # Repeated spaces are not expected from derived Show and are rejected.
    if len(args) != 2:
        raise SerializationError("MkSchema must display exactly two fields")
    return args


def _unparen(text):
    if text.startswith('(') and text.endswith(')'):
        # Keep grouping in the constructed Coq term, but remove one outer pair
        # when inspecting a generated list.
        return text[1:-1].strip()
    return text


def reconstruct_p0(fields):
    """Return (input_coq, binder_literals, scheduler_names)."""
    if len(fields) != 5:
        raise SerializationError("P0 needs exactly five schedule callbacks")
    ty, schema, rs, envs, expr = map(lambda s: _coq_literal(_callback_text(s)), fields)
    if len(_split_top(ty if not (ty.startswith('(') and ty.endswith(')')) else ty[1:-1], ',')) != 1:
        raise SerializationError("first callback must be the generated type alone")
    ets, acts = _schema(schema)
    if not envs.startswith('[') or not envs.endswith(']'):
        raise SerializationError("environment callback must be a list")
    contents = envs[1:-1].strip()
    if not contents:
        raise SerializationError("generated input has no first environment")
    environments = _split_top(contents, ';')
    e = environments[0]
    es = '[' + '; '.join(environments[1:]) + ']'
    # _unparen is safe here because each source token is already balanced.
    ets, acts = _unparen(ets), _unparen(acts)
    expression = (
        f"Original.mkInput ({ets}) ({acts}) ({rs}) ({e}) ({es}) "
        f"({ty}) ({expr})"
    )
    return expression, (ty, schema, rs, envs, expr), None


def reconstruct_candidate(fields):
    if len(fields) != 1:
        raise SerializationError("candidate needs exactly one Input callback")
    expression = _coq_literal(_callback_text(fields[0]))
    if not expression.startswith("Original.mkInput ("):
        raise SerializationError("candidate callback is not a full Input")
    args = _split_top(expression[len("Original.mkInput "):], ' ')
    if len(args) != 7:
        raise SerializationError("Input display must have all seven fields")
    return expression


def adapter_lemma(index, expression, binders):
    """A Coq equality checks every P0 binder against the reconstructed input."""
    ty, schema, rs, envs, expr = binders
    n = f"sample_{index}"
    return f'''Definition {n} : Original.Input := {expression}.
Example {n}_adapter :
  ({ty} : CedarType) = Original.ty {n} /\\
  ({schema} : Schema) =
    MkSchema (Original.ets {n}) (Original.acts {n}) /\\
  ({rs} : list RequestType) = Original.rs {n} /\\
  ({envs} : list Environment) = Original.e {n} :: Original.es {n} /\\
  ({expr} : CedarExpr * PathSet) = Original.expr {n}.
Proof. repeat split; reflexivity. Qed.
'''


ADAPTER_PRELUDE = '''From Coq Require Import List String ZArith.
Require Import Specification.cedar.Spec Property.Original.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
'''
