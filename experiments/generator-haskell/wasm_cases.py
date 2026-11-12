"""Hand-authored replay witnesses and independent expected whole-module ASTs."""
from __future__ import annotations

from typing import NamedTuple


Configuration = tuple[int, int, int, int, int, int, int]


class ReplayCase(NamedTuple):
    name: str
    config: Configuration
    tape: tuple[int, ...]
    expected: dict[str, object]


def module(types: list[tuple[int, int]], bodies: list[tuple[int, int, list[object]]],
           exports: list[int], start: int | None) -> dict[str, object]:
    i32: dict[str, str] = {'NumT': 'I32T'}
    return {
        'TYPES': [{'RecT': [{'SubT': ['Final', [], {'DefFuncT': {'FuncT': [
            [i32] * parameters, [i32] * results]}}]}]} for parameters, results in types],
        'GLOBALS': [], 'TABLES': [], 'MEMS': [], 'TAGS': [],
        'FUNCS': [{'FTYPE': index, 'LOCALS': [{'LTYPE': i32}] * locals_, 'BODY': body}
                  for index, locals_, body in bodies],
        'START': None if start is None else {'SFUNC': start},
        'ELEMS': [], 'DATAS': [], 'IMPORTS': [],
        'EXPORTS': [{'NAME': [ord(character) for character in f'f{position}'],
                     'EDESC': {'FuncExport': target}} for position, target in enumerate(exports)],
    }


def constant(value: int) -> dict[str, object]:
    return {'CONST': {'I32': value}}


def replay_cases() -> tuple[ReplayCase, ...]:
    empty = ReplayCase('empty', (0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0), module([], [], [], None))
    types_only = ReplayCase('unused-duplicate-types', (3, 0, 4, 3, 0, 0, 0),
        (3, 4, 3, 0, 0, 4, 3, 0, 0, 0), module([(4, 3), (0, 0), (4, 3)], [], [], None))
    indices = [0, 0, 1, 2, 0, 1, 1, 1]
    locals_ = [5, 4, 0, 3, 0, 0, 0, 0]
    exports = [7, 6, 5, 4, 3, 2, 1, 0, 0, 7, 3, 1]
    larger = ReplayCase('counts-sharing-start-exports', (3, 8, 4, 3, 5, 12, 0),
        tuple([3, 4, 3, 0, 0, 4, 3, 8] + indices + locals_ + [12] + exports + [2]),
        module([(4, 3), (0, 0), (4, 3)], [(index, local, [] if index == 1 else [constant(0)] * 3)
            for index, local in zip(indices, locals_, strict=True)], exports, 5))
    scalar_body: list[object] = [constant(4294967295), {'LOCAL.TEE': 0}, {'LOCAL.SET': 0},
        {'LOCAL.GET': 0}, constant(0), {'BINOP': {'I32': 'IAdd'}}, constant(1),
        {'BINOP': {'I32': 'ISub'}}, constant(2), {'BINOP': {'I32': 'IMul'}}, 'NOP']
    scalar = ReplayCase('u32-boundaries-local-mutation-arithmetic', (1, 1, 0, 1, 1, 1, 20),
        (1, 0, 1, 1, 0, 1, 1, 4294967295, 6, 0, 5, 0, 3, 0, 1, 0, 4, 1, 1, 5, 1, 2, 6, 2, 0, 1, 0, 0),
        module([(0, 1)], [(0, 1, scalar_body)], [0], None))
    calls = ReplayCase('forward-and-recursive-four-argument-calls', (2, 2, 4, 2, 0, 0, 16),
        (2, 0, 2, 4, 2, 2, 0, 1, 0, 1, 10, 1, 11, 1, 12, 1, 13, 8, 0,
         0, 3, 0, 4, 1, 7, 2, 7, 3, 11, 0, 0, 0),
        module([(0, 2), (4, 2)], [
            (0, 0, [constant(10), constant(11), constant(12), constant(13), {'CALL': 1}]),
            (1, 0, [{'LOCAL.GET': 0}, {'LOCAL.GET': 1}, {'LOCAL.GET': 2}, {'LOCAL.GET': 3}, {'CALL': 1}])], [], None))
    block_type: dict[str, int] = {'VarBlockType': 1}
    structured = ReplayCase('parameterized-multivalue-block-if', (2, 1, 2, 2, 0, 0, 32),
        (2, 0, 2, 2, 2, 1, 0, 0, 1, 1, 1, 2, 17, 3, 1, 3, 0, 1, 1, 19, 2, 0, 1, 4, 3, 0, 0, 0, 0),
        module([(0, 2), (2, 2)], [(0, 0, [constant(1), constant(2),
            {'BLOCK': [block_type, ['DROP', constant(3)]]}, constant(1),
            {'IF % % ELSE %': [block_type, ['NOP'], [constant(4), 'DROP']]}])], [], None))
    nested: list[object] = [constant(256)]
    for _ in range(8):
        nested = [{'BLOCK': [{'ValBlockType': {'NumT': 'I32T'}}, nested]}]
    deep = ReplayCase('eight-nested-blocks', (1, 1, 0, 1, 0, 0, 32),
        tuple([1, 0, 1, 1, 0, 0] + [6] * 8 + [1, 256] + [0] * 9 + [0, 0]),
        module([(0, 1)], [(0, 0, nested)], [], None))
    empty_loop = ReplayCase('empty-loop-and-if', (1, 1, 0, 0, 0, 0, 16),
        (1, 0, 0, 1, 0, 0, 5, 0, 1, 0, 7, 0, 0, 0, 0, 1),
        module([(0, 0)], [(0, 0, [{'LOOP': [{'ValBlockType': None}, []]}, constant(0),
            {'IF % % ELSE %': [{'ValBlockType': None}, [], []]}])], [], 0))
    long_body = ReplayCase('sixty-four-instructions', (1, 1, 0, 0, 0, 0, 64),
        tuple([1, 0, 0, 1, 0, 0] + [2] * 64 + [0, 0]),
        module([(0, 0)], [(0, 0, ['NOP'] * 64)], [], None))
    exhausted_budget = ReplayCase('shared-branch-budget', (1, 1, 0, 1, 0, 0, 2),
        (1, 0, 1, 1, 0, 0, 1, 9, 10, 0, 0),
        module([(0, 1)], [(0, 0, [constant(9),
            {'IF % % ELSE %': [{'ValBlockType': {'NumT': 'I32T'}}, [constant(0)], [constant(0)]]}])], [], None))
    return (empty, types_only, larger, scalar, calls, structured, deep, empty_loop, long_body, exhausted_budget)
