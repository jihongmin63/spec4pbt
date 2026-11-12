"""Strict inverse of the native JSON embedding for finite Rocq output comparisons.

All fields and representation choices are checked; this codec is test infrastructure,
not a proof that serialization preserves the pinned specification's AST.
"""
from __future__ import annotations

from collections import Counter
from typing import cast


def array(value: object) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f'Expected array, received {value!r}')
    return cast(list[object], value)


def record(value: object, fields: set[str]) -> dict[str, object]:
    if not isinstance(value, dict) or set(value) != fields:
        raise ValueError(f'Expected fields {fields!r}, received {value!r}')
    return cast(dict[str, object], value)


def natural(value: object) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f'Expected natural number, received {value!r}')
    return value


def signatures(row: dict[str, object]) -> list[object]:
    return array(row['TYPES'])


def functions(row: dict[str, object]) -> list[object]:
    return array(row['FUNCS'])


def i32_types(value: object) -> int:
    values = array(value)
    if any(item != {'NumT': 'I32T'} for item in values):
        raise ValueError(f'Expected I32 types, received {value!r}')
    return len(values)


def signature_counts(value: object) -> tuple[int, int]:
    group = array(record(value, {'RecT'})['RecT'])
    if len(group) != 1:
        raise ValueError(f'Expected singleton recursion group: {value!r}')
    subtype = array(record(group[0], {'SubT'})['SubT'])
    if len(subtype) != 3 or subtype[:2] != ['Final', []]:
        raise ValueError(f'Expected final supertype-free signature: {value!r}')
    function = array(record(record(subtype[2], {'DefFuncT'})['DefFuncT'], {'FuncT'})['FuncT'])
    if len(function) != 2:
        raise ValueError(f'Expected parameter/result pair: {value!r}')
    return i32_types(function[0]), i32_types(function[1])


def local_count(value: object) -> int:
    locals_ = array(record(value, {'FTYPE', 'LOCALS', 'BODY'})['LOCALS'])
    if any(item != {'LTYPE': {'NumT': 'I32T'}} for item in locals_):
        raise ValueError(f'Expected I32 locals: {locals_!r}')
    return len(locals_)


def block_term(value: object) -> str:
    if value == {'ValBlockType': None}:
        return 'WasmGenerator.EmptyBlock'
    if value == {'ValBlockType': {'NumT': 'I32T'}}:
        return 'WasmGenerator.ValueBlock'
    index = natural(record(value, {'VarBlockType'})['VarBlockType'])
    return f'(WasmGenerator.TypeBlock {index}%Z)'


def instr_term(value: object) -> str:
    if value == 'NOP':
        return 'WasmGenerator.INop'
    if value == 'DROP':
        return 'WasmGenerator.IDrop'
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError(f'Invalid instruction: {value!r}')
    tag, payload = next(iter(value.items()))
    if tag == 'CONST':
        number = natural(record(payload, {'I32'})['I32'])
        if number >= 2 ** 32:
            raise ValueError(f'I32 constant is out of range: {number}')
        return f'(WasmGenerator.IConst {number}%Z)'
    indexed = {'LOCAL.GET': 'ILocalGet', 'LOCAL.SET': 'ILocalSet', 'LOCAL.TEE': 'ILocalTee', 'CALL': 'ICall'}
    if tag in indexed:
        return f'(WasmGenerator.{indexed[tag]} {natural(payload)}%Z)'
    if tag == 'BINOP':
        operation = record(payload, {'I32'})['I32']
        if operation not in ('IAdd', 'ISub', 'IMul'):
            raise ValueError(f'Unexpected operation: {operation!r}')
        return f'WasmGenerator.{operation}'
    if tag in ('BLOCK', 'LOOP', 'IF % % ELSE %'):
        fields = array(payload)
        expected = 3 if tag == 'IF % % ELSE %' else 2
        if len(fields) != expected:
            raise ValueError(f'Invalid structured instruction: {value!r}')
        constructor = {'BLOCK': 'IBlock', 'LOOP': 'ILoop', 'IF % % ELSE %': 'IIf'}[tag]
        bodies = ' '.join(instrs_term(field) for field in fields[1:])
        return f'(WasmGenerator.{constructor} {block_term(fields[0])} {bodies})'
    raise ValueError(f'Unexpected instruction: {value!r}')


def instrs_term(value: object) -> str:
    return '[' + '; '.join(instr_term(item) for item in array(value)) + ']'


def module_term(row: dict[str, object]) -> str:
    record(row, {'TYPES', 'GLOBALS', 'TABLES', 'MEMS', 'TAGS', 'FUNCS',
                 'START', 'ELEMS', 'DATAS', 'IMPORTS', 'EXPORTS'})
    if any(row[name] != [] for name in ('GLOBALS', 'TABLES', 'MEMS', 'TAGS', 'ELEMS', 'DATAS', 'IMPORTS')):
        raise ValueError('Out-of-fragment module sections')
    types = signatures(row)
    bodies = functions(row)
    type_terms = [f'(WasmGenerator.FunctionSignature {p}%Z {r}%Z)' for p, r in map(signature_counts, types)]
    function_terms: list[str] = []
    for item in bodies:
        function = record(item, {'FTYPE', 'LOCALS', 'BODY'})
        index = natural(function['FTYPE'])
        if index >= len(types):
            raise ValueError(f'Invalid function type index: {index}')
        function_terms.append(
            f'(WasmGenerator.FunctionBody {index}%Z {local_count(item)}%Z {instrs_term(function["BODY"])})')
    exports: list[int] = []
    for position, item in enumerate(array(row['EXPORTS'])):
        export = record(item, {'NAME', 'EDESC'})
        if export['NAME'] != [ord(character) for character in f'f{position}']:
            raise ValueError(f'Unexpected export name: {export["NAME"]!r}')
        index = natural(record(export['EDESC'], {'FuncExport'})['FuncExport'])
        if index >= len(bodies):
            raise ValueError(f'Invalid export index: {index}')
        exports.append(index)
    start = 'None'
    if row['START'] is not None:
        index = natural(record(row['START'], {'SFUNC'})['SFUNC'])
        if index >= len(bodies):
            raise ValueError(f'Invalid start index: {index}')
        start = f'(Some {index}%Z)'
    return '(WasmGenerator.ConstructedModule [' + '; '.join(type_terms) + '] [' \
        + '; '.join(function_terms) + '] [' + '; '.join(f'{index}%Z' for index in exports) + f'] {start})'


def instruction_counts(items: object) -> Counter[str]:
    counts: Counter[str] = Counter()
    for item in array(items):
        instr_term(item)
        if isinstance(item, str):
            counts[item] += 1
        else:
            tag, payload = next(iter(cast(dict[str, object], item).items()))
            counts[tag] += 1
            if tag in ('BLOCK', 'LOOP', 'IF % % ELSE %'):
                for body in array(payload)[1:]:
                    counts.update(instruction_counts(body))
    return counts
