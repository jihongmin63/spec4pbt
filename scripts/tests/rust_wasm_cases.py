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
    memories: int
    datas: int
    memory_imports: int
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
    return (
        ReplayCase('empty', Config(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000),
                   (0,)),
        ReplayCase('empty_exact_work', Config(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1),
                   (0,)),
        ReplayCase('memory_import_only', Config(0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7),
                   (0, 1, 0, 0, 0, 0, 0)),
        ReplayCase('memory_import_unbounded_names', Config(0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 164),
                   (0, 1, 0, 65536, 1, 0, 1, 0, 1, 4294967296) + (1,) * 80 +
                   (0, 1, 55296, 0, 1, 1114112, 1, 4294967296) + (1,) * 64 + (0, 0)),
        ReplayCase('imports_memories_datas', Config(0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 17),
                   (0, 1, 1, 281474976710656, 0, 0, 0, 1, 0, 0, 0, 1, 1, 72, 1, 105, 0)),
        ReplayCase('memory_only', Config(0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5),
                   (0, 1, 0, 0, 0)),
        ReplayCase('memory32_limit', Config(0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6),
                   (0, 1, 0, 65536, 1, 0)),
        ReplayCase('memory64_limit', Config(0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6),
                   (0, 1, 1, 281474976710656, 1, 0)),
        ReplayCase('memory64_unbounded_max', Config(0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5),
                   (0, 1, 1, 281474976710656, 0)),
        ReplayCase('mixed_memories', Config(0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 100),
                   (0, 1, 0, 1, 1, 9, 1, 1, 42, 0, 1, 0, 0, 1, 65536)),
        ReplayCase('memory_stop_empty', Config(0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2),
                   (0, 0)),
        ReplayCase('memory_early_stop', Config(0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6),
                   (0, 1, 0, 2, 0, 0)),
        ReplayCase('passive_empty_string', Config(0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3),
                   (0, 1, 0)),
        ReplayCase('passive_unicode', Config(0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 9),
                   (0, 1, 1, 65, 1, 0, 1, 127360, 0)),
        ReplayCase('passive_unicode_line_separators', Config(0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 9),
                   (0, 1, 1, 133, 1, 8232, 1, 8233, 0)),
        ReplayCase('passive_two_segments', Config(0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 7),
                   (0, 1, 0, 1, 1, 97, 0)),
        ReplayCase('passive_stop_empty', Config(0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2),
                   (0, 0)),
        ReplayCase('natural_i64_2pow80_plus5', Config(1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 96),
                   (1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 4294967296, 2, 1, 2) +
                   (1,) * 77 + (0, 0)),
        ReplayCase('type_only', Config(2, 0, 3, 2, 0, 0, 0, 0, 0, 0, 1006),
                   (2, 1, 0, 0, 3, 0, 1, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0)),
        ReplayCase('six_functions_wide_signatures_locals_aliases', Config(1, 6, 4, 2, 3, 12, 0, 0, 0, 0, 10387),
                   (1, 1, 0, 0, 4, 0, 1, 0, 1, 2, 1, 0, 6, 0, 0, 0, 0, 0, 0, 12, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 3, 0, 1, 0, 0, 4294967296, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 4294967295, 3, 0, 1, 0, 0, 4294967296, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 4294967295, 3, 0, 1, 0, 0, 4294967296, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 4294967295, 3, 0, 1, 0, 0, 4294967296, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 4294967295, 3, 0, 1, 0, 0, 4294967296, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 4294967295, 3, 0, 1, 0, 0, 4294967296, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 4294967295, 0)),
        ReplayCase('self_call', Config(1, 1, 0, 1, 0, 2, 1, 0, 0, 0, 1003),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0, 8, 0)),
        ReplayCase('inline_if', Config(1, 1, 0, 1, 0, 2, 1, 0, 0, 0, 1003),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0, 14, 0, 0, 0, 1, 0, 7, 0, 9, 0)),
        ReplayCase('inline_block', Config(1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1003),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 12, 0, 0, 7, 0)),
        ReplayCase('inline_loop', Config(1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1003),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 13, 0, 0, 9, 0)),
        ReplayCase('nested_blocks_depth_eight', Config(1, 1, 0, 1, 0, 0, 8, 0, 0, 0, 1003),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 12, 0, 12, 0, 12, 0, 12, 0, 12, 0, 12, 0, 12, 0, 12, 0, 0, 7, 0)),
        ReplayCase('unreachable_add', Config(1, 1, 0, 1, 0, 0, 2, 0, 0, 0, 20),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 5, 18, 0, 0)),
        ReplayCase('unreachable_one_concrete_operand', Config(1, 1, 0, 1, 0, 0, 3, 0, 0, 0, 24),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 5, 4, 7, 18, 0, 0)),
        ReplayCase('unreachable_nonempty_predecessor', Config(1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 19),
                   (1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 11, 1, 1, 0, 7, 0)),
        ReplayCase('loop_parameter_label', Config(1, 1, 0, 1, 0, 0, 2, 0, 0, 0, 22),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 13, 0, 19, 0, 0)),
        ReplayCase('outer_block_label', Config(1, 1, 0, 1, 0, 0, 3, 0, 0, 0, 29),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 12, 0, 12, 0, 21, 0, 0, 7, 0)),
        ReplayCase('br_if_retains_argument', Config(1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 20),
                   (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 20, 0, 7, 0, 0, 0)),
        ReplayCase('mutual_void_calls', Config(1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1003),
                   (1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 5, 0, 4, 0)),
        ReplayCase('long_sequence_start', Config(1, 1, 0, 0, 0, 0, 64, 0, 0, 0, 1003),
                   (1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)),
        ReplayCase('forward_wide_call', Config(2, 2, 4, 2, 0, 0, 1, 0, 0, 0, 1070),
                   (2, 1, 0, 0, 0, 2, 1, 0, 1, 0, 0, 4, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 0, 9, 0, 1, 0, 4294967296, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 11, 0, 12, 0)),
        ReplayCase('indexed_block_parameters_multivalue', Config(1, 1, 4, 2, 0, 0, 1, 0, 0, 0, 1003),
                   (1, 1, 0, 0, 4, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 23, 0, 1, 1, 2, 2, 1, 1, 0)),
        ReplayCase('recursive_parent', Config(2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 12),
                   (1, 2, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0)),
        ReplayCase('mutual_recursive_group', Config(2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 17),
                   (1, 2, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 0, 0, 0)),
        ReplayCase('raw_type_alias', Config(3, 1, 1, 1, 0, 0, 0, 0, 0, 0, 29),
                   (3, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0, 1, 1, 2, 0, 0, 1, 0)),
        ReplayCase('exported_ref_func', Config(1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 17),
                   (1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 15, 0, 0)),
        ReplayCase('empty_recursive_group', Config(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2),
                   (1, 0)),
        ReplayCase('exported_function_index', Config(1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 21),
                   (1, 1, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 16, 0, 0, 0, 0)),
        ReplayCase('recursive_type_alias', Config(3, 1, 1, 1, 0, 0, 0, 0, 0, 0, 35),
                   (3, 1, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0, 1, 1, 2, 0, 0, 1, 0)),
        ReplayCase('external_parent_alias', Config(5, 1, 1, 1, 0, 0, 0, 0, 0, 0, 35),
                   (5, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 2, 1, 0, 0, 1, 2, 0, 2, 1, 2, 0, 3, 1, 4, 0, 0, 1, 0)),
        ReplayCase('recursive_parent_alias', Config(3, 1, 1, 1, 0, 0, 0, 0, 0, 0, 33),
                   (3, 2, 1, 0, 0, 1, 0, 0, 2, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 2, 0, 1, 1, 2, 0, 3, 1, 4, 0, 0, 1, 0)),
    )
