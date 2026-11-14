"""Compile the handwritten Rust/Wasm contracts and proof attempts, without certification.

Run after ``experiments.generator-rust.translate`` with one explicit directory
containing the ordered Wasm ``Spec.lean`` and its ``identity.json``. Sources are
checked against this checkout's pinned Wasm files. All Lean modules are compiled
locally; no compiled property proofs are imported from the specification donor.
Use the shared build lock as shown in docs/wasm-generator-case-study.md.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil

from scripts.toolchain import PROJECT
from .translate import executable_source, run

EXPERIMENT: Path = PROJECT / 'experiments/generator-rust'
BUILD: Path = PROJECT / 'build/generator-rust'
OUTPUT: Path = BUILD / 'manual-proof'
PROOF_MODULES: tuple[str, ...] = (
    'WasmNatural', 'WasmNaturalEncoding', 'WasmNaturalDifference', 'WasmSequence', 'WasmTypeMatchingPrimitives',
    'WasmDataEncoding', 'WasmEmbedding', 'WasmContract', 'WasmSpecificationWitnesses', 'WasmDomainWitnesses',
    'WasmChoices', 'WasmReplaySteps', 'WasmNaturalWord', 'WasmChoiceSafety', 'WasmNaturalIndex',
    'WasmModulePrimitives', 'WasmNaturalChoice',
    'WasmConstantReplay', 'WasmConstantSpecification', 'WasmConstantSupport',
    'WasmReplayWitness', 'WasmModuleCoverage', 'WasmDataChoice', 'WasmDataSpecification', 'WasmDataSupport',
    'WasmGroundEvaluation', 'WasmControlSpecification', 'WasmReplayEvaluation', 'WasmControlReplay', 'WasmControlSupport',
    'WasmTypeContextReplay', 'WasmTypeContextSpecification', 'WasmTypeContextSupport',
    'WasmMemoryProperties', 'WasmMemoryWitness', 'WasmMemoryReplay',
    'WasmMemoryCoverage', 'WasmMemorySupport', 'WasmMemorySpecification', 'WasmMemoryRepresentation', 'WasmMemorySoundness',
    'WasmNameChoice', 'WasmMemoryImportChoice', 'WasmMemoryImportSpecification',
    'WasmMemoryImportSupport', 'WasmImportInversion', 'WasmMemoryImportRepresentation',
    'WasmMemorySectionComposition',
    'WasmMemoryImportSoundness',
    'WasmProofAudit',
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def string_fields(value: object, label: str) -> dict[str, str]:
    if not isinstance(value, dict) or not all(
        isinstance(key, str) and isinstance(item, str) for key, item in value.items()
    ):
        raise ValueError(f'{label} must be an object mapping strings to strings')
    return dict(value)


def specification_source(directory: Path) -> Path:
    """Validate the generated specification's recorded source and output hashes."""
    identity: object = json.loads((directory / 'identity.json').read_text())
    if (not isinstance(identity, dict) or identity.get('schema_version') != 1
            or identity.get('options') != ['--relation-semantics', 'ordered']):
        raise ValueError(f'{directory}/identity.json must describe ordered relation semantics')
    sources: dict[str, str] = string_fields(identity.get('sources'), 'specification sources')
    local: dict[str, str] = {
        path.name: digest(path) for path in (PROJECT / 'specifications/wasm/spec').glob('*.watsup')
    }
    recorded: dict[str, str] = {Path(path).name: sha for path, sha in sources.items()}
    if not local or len(recorded) != len(sources) or recorded != local:
        raise ValueError(f'{directory}/identity.json sources differ from the local pinned Wasm specification')
    generated: dict[str, str] = string_fields(identity.get('generated'), 'generated specification files')
    source: Path = directory / 'Spec.lean'
    if generated.get('Spec.lean') != digest(source):
        raise ValueError(f'{source} does not match its recorded generated hash')
    return source


def main() -> None:
    parser: argparse.ArgumentParser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('specification', type=Path)
    args: argparse.Namespace = parser.parse_args()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    result_path: Path = OUTPUT / 'result.json'
    result_path.unlink(missing_ok=True)
    source: Path = specification_source(args.specification.resolve())
    shutil.copyfile(source, OUTPUT / 'WasmSpecification.lean')
    saved: dict[str, str] = string_fields(
        json.loads((BUILD / 'lean-environment.json').read_text()), 'Lean environment',
    )
    if not saved.get('LEAN_PATH') or not saved.get('LEAN_SYSROOT'):
        raise ValueError('Lean environment lacks LEAN_PATH or LEAN_SYSROOT; rerun Rust translation')
    environment: dict[str, str] = dict(os.environ) | saved | {
        'LEAN_NUM_THREADS': '1',
        'LEAN_PATH': str(OUTPUT) + os.pathsep + saved['LEAN_PATH'],
    }
    lean: Path = Path(saved['LEAN_SYSROOT']) / 'bin/lean'
    executable_source(BUILD / 'lean/GeneratorRust.lean')
    modules: list[Path] = [
        OUTPUT / 'WasmSpecification.lean',
        BUILD / 'lean/GeneratorRust.lean',
        *[EXPERIMENT / 'proofs' / (name + '.lean') for name in PROOF_MODULES],
    ]
    for module in modules:
        run(
            [str(lean), '-j', '1', '-M', '3100',
             '-o', str(OUTPUT / (module.stem + '.olean')), str(module)],
            PROJECT, environment, OUTPUT / (module.stem + '.log'),
        )
    record_result(args.specification, modules)


def record_result(specification: Path, modules: list[Path]) -> None:
    """Record source identities after every listed module and the axiom audit compile successfully."""
    result: dict[str, object] = {
        'specification_identity': str(specification.resolve() / 'identity.json'),
        'compiled_sources': {str(path.relative_to(PROJECT)): digest(path) for path in modules},
        'rust_sources': {str(path.relative_to(PROJECT)): digest(path)
                         for path in sorted((EXPERIMENT / 'src').rglob('*.rs'))},
        'proved': ['memoryOnly_ok', 'dataOnly_ok', 'importsOnly_ok',
                   'globalsOnly_ok', 'globalsOnly_not_generated', 'not_complete', 'emptyModule_ok',
                   'name_choice_replay', 'name_literal_roundtrip', 'name_literal_replay',
                   'memory_import_entry_replay', 'memory_import_section_replay',
                   'memory_import_free_execute', 'memory_imports_free_execute',
                   'memory_import_execute', 'memory_imports_execute', 'memory_import_list_valid',
                   'memory_import_list_replay', 'memory_import_list_supported',
                   'memory_import_list_generated_valid', 'memory_import_representable',
                   'original_memory_imports_representable', 'original_memory_imports_generated_valid',
                   'importsOnly_supported', 'memtype_valid_of_execution', 'import_memory_type_valid',
                   'imports_memory_types_valid', 'module_imports_execution', 'memory_imports_module_complete',
                   'memory_sections_replay', 'memory_sections_supported', 'memory_sections_valid',
                   'original_memory_sections_generated_valid',
                   'memory_import_constructor_sound', 'memory_import_section_sound',
                   'memory_import_section_valid',
                   'memory_import_names_ok', 'passive_data_payload_ok',
                   'empty_replay', 'empty_supported', 'empty_generated_valid',
                   'copy_natural_eq', 'increment_total', 'decrement_total', 'natural_representable',
                   'tape_roundtrip', 'length_from_total', 'word_replay', 'word_replay_total', 'pick_word_replay',
                   'pick_replay', 'memory_limits_valid', 'memory_bounded_valid',
                   'memories_list', 'memory_replay', 'memory_supported', 'memory_generated_valid',
                   'naturalLiteral_value', 'increment_literal', 'decrement_literal',
                   'double_total', 'double_plus_one_total', 'positive_difference_total',
                   'natural_difference_total', 'natural_difference_literal',
                   'sequence_roundtrip', 'sequence_literal_values', 'sequence_append', 'sequence_snoc',
                   'sequence_length', 'sequence_get', 'sequence_select', 'sequence_last',
                   'sequence_reverse_into', 'sequence_reverse', 'sequence_split',
                   'pick_word_state', 'pick_state', 'positive_to_word', 'natural_to_word',
                   'literal_to_word', 'natural_from_word', 'pick_word_range',
                   'natural_index_replay', 'natural_index_spec', 'natural_index_sound',
                   'same_natural_total', 'completed_lookup', 'comparison_lookup_sound',
                   'recursive_index_literal', 'containing_group_split', 'containing_group_missing',
                   'pick_natural_word_state', 'copy_value_eq', 'copy_types_literal', 'join_types_literal',
                   'generate_types_zero', 'build_empty_types', 'replay_from_build',
                   'value_types_loop_replay', 'value_types_replay', 'choose_replay',
                   'unbounded_empty_supported',
                   'memory_none_replay', 'memory_some_replay',
                   'memory_section_replay', 'memory_list_replay', 'memory_list_supported',
                   'memories_bounded_execute', 'memory_list_valid', 'memory_list_generated_valid',
                   'limits_bounds_of_execution', 'memtype_bounds_of_execution',
                   'memtype_representable_iff', 'original_memories_representable',
                   'original_memories_generated_valid',
                   'memory_constructor_sound', 'memory_constructor_valid',
                   'positive_choice_replay', 'natural_choice_replay', 'natural_literal_choice',
                   'constant_replay', 'constant_embed', 'constant_supported',
                   'constant_module_ok', 'constant_generated_valid', 'integer_constant_replay',
                   'constant64_replay', 'constant64_embed', 'constant64_supported',
                   'constant64_module_ok', 'constant64_generated_valid',
                   'text_literal_valid', 'text_roundtrip', 'char_choice_decode',
                   'text_choice_replay', 'data_section_replay',
                   'data_literal_embed', 'passive_module_ok', 'data_list_replay',
                   'data_list_supported', 'data_list_generated_valid', 'dataOnly_supported',
                   'unreachable_add_replay', 'unreachable_add_embed', 'unreachable_add_module_ok',
                   'unreachable_add_supported', 'unreachable_add_generated_valid',
                   'unreachable_operand_replay', 'unreachable_operand_embed', 'unreachable_operand_module_ok',
                   'unreachable_operand_supported', 'unreachable_operand_generated_valid',
                   'unreachable_predecessor_replay', 'unreachable_predecessor_embed',
                   'unreachable_predecessor_module_ok', 'unreachable_predecessor_supported',
                   'unreachable_predecessor_generated_valid',
                   'loop_label_replay', 'loop_label_embed', 'loop_label_module_ok',
                   'loop_label_supported', 'loop_label_generated_valid',
                   'outer_label_replay', 'outer_label_embed', 'outer_label_module_ok',
                   'outer_label_supported', 'outer_label_generated_valid',
                   'branch_if_replay', 'branch_if_embed', 'branch_if_module_ok',
                   'branch_if_supported', 'branch_if_generated_valid',
                   'recursive_parent_replay', 'recursive_parent_embed', 'recursive_parent_module_ok',
                   'recursive_parent_supported', 'recursive_parent_generated_valid',
                   'mutual_group_replay', 'mutual_group_embed', 'mutual_group_module_ok',
                   'mutual_group_supported', 'mutual_group_generated_valid',
                   'raw_alias_replay', 'raw_alias_embed', 'raw_alias_module_ok',
                   'raw_alias_supported', 'raw_alias_generated_valid',
                   'exported_ref_replay', 'exported_ref_embed', 'exported_ref_module_ok',
                   'exported_ref_supported', 'exported_ref_generated_valid',
                   'closed_shared_aliases_match', 'closed_dangling_reference_rejected',
                   'closed_later_dangling_reference_rejected',
                   ],
        'unproved': ['Soundness', 'Completeness', 'SamplingSoundness', 'SamplingCompleteness'],
        'certificate': False,
    }
    result_path: Path = OUTPUT / 'result.json'
    result_path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'event': 'manual_proofs_checked', 'result': str(result_path)}), flush=True)


if __name__ == '__main__':
    main()
