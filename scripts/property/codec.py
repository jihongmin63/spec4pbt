"""Shared typed JSON representation for generated Inputs and AL values."""
from dataclasses import dataclass
import re


class CodecError(ValueError):
    pass


@dataclass(frozen=True)
class Value:
    type: str
    value: object = None
    constructor: str | None = None
    args: tuple['Value', ...] = ()


def decode_value(wire, expected_type, constructors=None):
    constructors = constructors or {}
    if not isinstance(wire, dict) or wire.get('type') != expected_type:
        raise CodecError(f'expected typed {expected_type} value')
    if expected_type in ('nat', 'int'):
        if set(wire) != {'type', 'value'}:
            raise CodecError(f'invalid {expected_type} fields')
        raw = wire['value']
        if type(raw) is int:
            raw = str(raw)
        if not isinstance(raw, str) or not re.fullmatch(r'-?(?:0|[1-9][0-9]*)', raw):
            raise CodecError(f'invalid {expected_type} literal')
        number = int(raw)
        if expected_type == 'nat' and number < 0:
            raise CodecError('nat must be nonnegative')
        return Value(expected_type, str(number))
    if expected_type in ('text', 'bool'):
        if set(wire) != {'type', 'value'} or not (
            isinstance(wire['value'], str) if expected_type == 'text'
            else type(wire['value']) is bool):
            raise CodecError(f'invalid {expected_type} value')
        return Value(expected_type, wire['value'])
    if set(wire) != {'type', 'constructor', 'args'}:
        raise CodecError(f'invalid {expected_type} constructor fields')
    cases = constructors.get(expected_type, {})
    name = wire['constructor']
    if name not in cases or not isinstance(wire['args'], list):
        raise CodecError(f'unknown {expected_type} constructor: {name}')
    arg_types = cases[name]
    if len(wire['args']) != len(arg_types):
        raise CodecError(f'{name} arity mismatch')
    return Value(expected_type, constructor=name,
                 args=tuple(decode_value(item, typ, constructors)
                            for item, typ in zip(wire['args'], arg_types)))


def encode_value(value):
    if value.constructor is None:
        return {'type': value.type, 'value': value.value}
    return {'type': value.type, 'constructor': value.constructor,
            'args': [encode_value(arg) for arg in value.args]}


def decode_input(wire, fields, constructors=None):
    if not isinstance(wire, dict):
        raise CodecError('Input must be an object')
    expected = {field['name'] for field in fields}
    if set(wire) != expected:
        raise CodecError(f'Input fields must be exactly {sorted(expected)}')
    return {field['name']: encode_value(decode_value(
        wire[field['name']], field['type'], constructors)) for field in fields}
