"""Finite replay witnesses for independent Wasm shapes, not a support model or proof."""
from __future__ import annotations

from typing import NamedTuple


class Config(NamedTuple):
    types: int
    functions: int
    parameters: int
    results: int
    locals: int
    exports: int
    fuel: int
    work: int


class ReplayCase(NamedTuple):
    name: str
    config: Config
    tape: tuple[int, ...]


def replay_arguments(case: ReplayCase) -> list[str]:
    return ['replay', *(str(value) for value in case.config),
            ','.join(str(value) for value in case.tape) if case.tape else '-']


def replay_cases() -> tuple[ReplayCase, ...]:
    """The cells below select specific signatures, stack effects, and full-width values."""
    wide_header: tuple[int, ...] = (
        1, 4, 0, 1, 0, 1, 2, 1, 0,  # one (i32,i64,i32,i64)->(i64,i32) type
        6, 0, 0, 0, 0, 0, 0,  # six functions sharing that type
    )
    wide_body: tuple[int, ...] = (3, 0, 1, 0, 0, (1 << 64) - 1, 0, (1 << 32) - 1)
    single: tuple[int, ...] = (1, 0, 1, 0, 1, 0, 0)  # []->[i32], one function, no locals
    # For the single-result context: calls are rule 8; inline block/loop/if 12/13/14.
    return (
        ReplayCase('empty', Config(0, 0, 0, 0, 0, 0, 0, 1000), (0,)),
        ReplayCase('empty_exact_work', Config(0, 0, 0, 0, 0, 0, 0, 1), (0,)),
        ReplayCase('type_only', Config(2, 0, 3, 2, 0, 0, 0, 1000),
                   (2, 3, 0, 1, 0, 2, 1, 0, 0, 0, 0)),
        ReplayCase('six_functions_wide_signatures_locals_aliases', Config(1, 6, 4, 2, 3, 12, 0, 10000),
                   wide_header + wide_body * 6 + (12, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0)),
        ReplayCase('self_call', Config(1, 1, 0, 1, 0, 2, 1, 1000),
                   single + (8, 2, 0, 0, 0)),
        ReplayCase('inline_if', Config(1, 1, 0, 1, 0, 2, 1, 1000),
                   single + (14, 0, 0, 0, 1, 0, 7, 0, 9, 2, 0, 0, 0)),
        ReplayCase('inline_block', Config(1, 1, 0, 1, 0, 0, 1, 1000),
                   single + (12, 0, 0, 7, 0, 0)),
        ReplayCase('inline_loop', Config(1, 1, 0, 1, 0, 0, 1, 1000),
                   single + (13, 0, 0, 9, 0, 0)),
        ReplayCase('nested_blocks_depth_eight', Config(1, 1, 0, 1, 0, 0, 8, 1000),
                   single + (12, 0) * 8 + (0, 7, 0, 0)),
        ReplayCase('mutual_void_calls', Config(1, 2, 0, 0, 0, 0, 1, 1000),
                   (1, 0, 0, 2, 0, 0, 0, 5, 0, 4, 0, 0)),
        ReplayCase('long_sequence_start', Config(1, 1, 0, 0, 0, 0, 64, 1000),
                   (1, 0, 0, 1, 0, 0) + (1,) * 64 + (0, 1)),
        ReplayCase('forward_wide_call', Config(2, 2, 4, 2, 0, 0, 1, 1000),
                   (2, 0, 2, 1, 0, 4, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1,
                    0, 9, 0, 1, 0, (1 << 64) - 1, 0, 2, 0, 0,
                    0, 0, 0, 11, 0, 12, 0, 0)),
        ReplayCase('indexed_block_parameters_multivalue', Config(1, 1, 4, 2, 0, 0, 1, 1000),
                   (1, 4, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0,
                    23, 0, 1, 1, 2, 2, 1, 1, 0, 0)),
    )
