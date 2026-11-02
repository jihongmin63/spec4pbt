/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import properties.wasm_module_ok.PositiveCorrespondence
namespace properties.wasm_module_ok.PositiveRuntime
open SpecTec SpecTecExecution
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem body_correct {α : Type} (c : Call α) :
    erase (body c) = SpecTec.specTecBody ⟨_, toOriginal c⟩ :=
  match c with
  | @Call.«$min_» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$min__clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$min__clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$min__clauses», SpecTec.«$min__clauses», List.map_cons, List.map_nil, «erase:$min_:clause:0», «erase:$min_:clause:1»]
  | @Call.«$rev_» X input0 => by
    change erase (ExecutablePlan.firstSuccess («$rev__clauses» X input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$rev__clauses» X input0) ())
    simp only [erase_firstSuccess, «$rev__clauses», SpecTec.«$rev__clauses», List.map_cons, List.map_nil, «erase:$rev_:clause:0», «erase:$rev_:clause:1»]
  | @Call.«$make_» X_T input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$make__clauses» X_T input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$make__clauses» X_T input0 input1) ())
    simp only [erase_firstSuccess, «$make__clauses», SpecTec.«$make__clauses», List.map_cons, List.map_nil, «erase:$make_:clause:0», «erase:$make_:clause:1»]
  | @Call.«$empty_set» K => by
    change erase (ExecutablePlan.firstSuccess («$empty_set_clauses» K) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$empty_set_clauses» K) ())
    simp only [erase_firstSuccess, «$empty_set_clauses», SpecTec.«$empty_set_clauses», List.map_cons, List.map_nil, «erase:$empty_set:clause:0»]
  | @Call.«$in_set» K_T eq_K_T input0 input1 => by
    change erase (letI : _root_.DecidableEq K_T := eq_K_T; ExecutablePlan.firstSuccess («$in_set_clauses» K_T input0 input1) ()) = (letI : _root_.DecidableEq K_T := eq_K_T; SpecTecExecution.firstSuccess (SpecTec.«$in_set_clauses» K_T input0 input1) ())
    simp only [erase_firstSuccess, «$in_set_clauses», SpecTec.«$in_set_clauses», List.map_cons, List.map_nil, «erase:$in_set:clause:0»]
  | @Call.«$map_set» X Y compare_Y input0 input1 => by
    change erase (letI : _root_.SpecTecCompareKey Y := compare_Y; ExecutablePlan.firstSuccess («$map_set_clauses» X Y input0 input1) ()) = (letI : _root_.SpecTecCompareKey Y := compare_Y; SpecTecExecution.firstSuccess (SpecTec.«$map_set_clauses» X Y (fun a0 => toOriginal (input0 a0)) input1) ())
    simp only [erase_firstSuccess, «$map_set_clauses», SpecTec.«$map_set_clauses», List.map_cons, List.map_nil, «erase:$map_set:clause:0», «erase:$map_set:clause:1»]
  | @Call.«$range» input0 => by
    change erase (ExecutablePlan.firstSuccess («$range_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$range_clauses» input0) ())
    simp only [erase_firstSuccess, «$range_clauses», SpecTec.«$range_clauses», List.map_cons, List.map_nil, «erase:$range:clause:0», «erase:$range:clause:1»]
  | @Call.«$rolldt'» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$rolldt'_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$rolldt'_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$rolldt'_clauses», SpecTec.«$rolldt'_clauses», List.map_cons, List.map_nil, «erase:$rolldt':clause:0», «erase:$rolldt':clause:1»]
  | @Call.«$min_addrtype» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$min_addrtype_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$min_addrtype_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$min_addrtype_clauses», SpecTec.«$min_addrtype_clauses», List.map_cons, List.map_nil, «erase:$min_addrtype:clause:0», «erase:$min_addrtype:clause:1»]
  | @Call.«$num_size» input0 => by
    change erase (ExecutablePlan.firstSuccess («$num_size_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$num_size_clauses» input0) ())
    simp only [erase_firstSuccess, «$num_size_clauses», SpecTec.«$num_size_clauses», List.map_cons, List.map_nil, «erase:$num_size:clause:0», «erase:$num_size:clause:1»]
  | @Call.«$vec_size» input0 => by
    change erase (ExecutablePlan.firstSuccess («$vec_size_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$vec_size_clauses» input0) ())
    simp only [erase_firstSuccess, «$vec_size_clauses», SpecTec.«$vec_size_clauses», List.map_cons, List.map_nil, «erase:$vec_size:clause:0»]
  | @Call.«$type_vecop» A input0 => by
    change erase (ExecutablePlan.firstSuccess («$type_vecop_clauses» A input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$type_vecop_clauses» A input0) ())
    simp only [erase_firstSuccess, «$type_vecop_clauses», SpecTec.«$type_vecop_clauses», List.map_cons, List.map_nil, «erase:$type_vecop:clause:0»]
  | @Call.«$free_empty»  => by
    change erase (ExecutablePlan.firstSuccess («$free_empty_clauses» ) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_empty_clauses» ) ())
    simp only [erase_firstSuccess, «$free_empty_clauses», SpecTec.«$free_empty_clauses», List.map_cons, List.map_nil, «erase:$free_empty:clause:0»]
  | @Call.«$fold_left» X_T Y input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$fold_left_clauses» X_T Y input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$fold_left_clauses» X_T Y (fun a0 a1 => toOriginal (input0 a0 a1)) input1 input2) ())
    simp only [erase_firstSuccess, «$fold_left_clauses», SpecTec.«$fold_left_clauses», List.map_cons, List.map_nil, «erase:$fold_left:clause:0», «erase:$fold_left:clause:1»]
  | @Call.«$free_union» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$free_union_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_union_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$free_union_clauses», SpecTec.«$free_union_clauses», List.map_cons, List.map_nil, «erase:$free_union:clause:0»]
  | @Call.«$free_unions» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_unions_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_unions_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_unions_clauses», SpecTec.«$free_unions_clauses», List.map_cons, List.map_nil, «erase:$free_unions:clause:0», «erase:$free_unions:clause:1»]
  | @Call.«$add_minus_one» input0 => by
    change erase (ExecutablePlan.firstSuccess («$add_minus_one_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$add_minus_one_clauses» input0) ())
    simp only [erase_firstSuccess, «$add_minus_one_clauses», SpecTec.«$add_minus_one_clauses», List.map_cons, List.map_nil, «erase:$add_minus_one:clause:0»]
  | @Call.«$free_idx» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_idx_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_idx_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_idx_clauses», SpecTec.«$free_idx_clauses», List.map_cons, List.map_nil, «erase:$free_idx:clause:0»]
  | @Call.«$free_shift» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_shift_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_shift_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_shift_clauses», SpecTec.«$free_shift_clauses», List.map_cons, List.map_nil, «erase:$free_shift:clause:0»]
  | @Call.«$free_list» X input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$free_list_clauses» X input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_list_clauses» X (fun a0 => toOriginal (input0 a0)) input1) ())
    simp only [erase_firstSuccess, «$free_list_clauses», SpecTec.«$free_list_clauses», List.map_cons, List.map_nil, «erase:$free_list:clause:0», «erase:$free_list:clause:1»]
  | @Call.«$free_opt» X_T input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$free_opt_clauses» X_T input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_opt_clauses» X_T (fun a0 => toOriginal (input0 a0)) input1) ())
    simp only [erase_firstSuccess, «$free_opt_clauses», SpecTec.«$free_opt_clauses», List.map_cons, List.map_nil, «erase:$free_opt:clause:0», «erase:$free_opt:clause:1»]
  | @Call.«$free_packtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_packtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_packtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_packtype_clauses», SpecTec.«$free_packtype_clauses», List.map_cons, List.map_nil, «erase:$free_packtype:clause:0»]
  | @Call.«$free_numtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_numtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_numtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_numtype_clauses», SpecTec.«$free_numtype_clauses», List.map_cons, List.map_nil, «erase:$free_numtype:clause:0»]
  | @Call.«$free_vectype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_vectype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_vectype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_vectype_clauses», SpecTec.«$free_vectype_clauses», List.map_cons, List.map_nil, «erase:$free_vectype:clause:0»]
  | @Call.«$update_types» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_types_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_types_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_types_clauses», SpecTec.«$update_types_clauses», List.map_cons, List.map_nil, «erase:$update_types:clause:0»]
  | @Call.«$update_globals» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_globals_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_globals_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_globals_clauses», SpecTec.«$update_globals_clauses», List.map_cons, List.map_nil, «erase:$update_globals:clause:0»]
  | @Call.«$update_tables» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_tables_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_tables_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_tables_clauses», SpecTec.«$update_tables_clauses», List.map_cons, List.map_nil, «erase:$update_tables:clause:0»]
  | @Call.«$update_mems» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_mems_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_mems_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_mems_clauses», SpecTec.«$update_mems_clauses», List.map_cons, List.map_nil, «erase:$update_mems:clause:0»]
  | @Call.«$update_tags» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_tags_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_tags_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_tags_clauses», SpecTec.«$update_tags_clauses», List.map_cons, List.map_nil, «erase:$update_tags:clause:0»]
  | @Call.«$update_funcs» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_funcs_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_funcs_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_funcs_clauses», SpecTec.«$update_funcs_clauses», List.map_cons, List.map_nil, «erase:$update_funcs:clause:0»]
  | @Call.«$free_start» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_start_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_start_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_start_clauses», SpecTec.«$free_start_clauses», List.map_cons, List.map_nil, «erase:$free_start:clause:0»]
  | @Call.«$update_elems» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_elems_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_elems_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_elems_clauses», SpecTec.«$update_elems_clauses», List.map_cons, List.map_nil, «erase:$update_elems:clause:0»]
  | @Call.«$update_datas» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_datas_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_datas_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_datas_clauses», SpecTec.«$update_datas_clauses», List.map_cons, List.map_nil, «erase:$update_datas:clause:0»]
  | @Call.«$update_locals» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_locals_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_locals_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_locals_clauses», SpecTec.«$update_locals_clauses», List.map_cons, List.map_nil, «erase:$update_locals:clause:0»]
  | @Call.«$update_labels» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_labels_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_labels_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_labels_clauses», SpecTec.«$update_labels_clauses», List.map_cons, List.map_nil, «erase:$update_labels:clause:0»]
  | @Call.«$update_label» input0 => by
    change erase (ExecutablePlan.firstSuccess («$update_label_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$update_label_clauses» input0) ())
    simp only [erase_firstSuccess, «$update_label_clauses», SpecTec.«$update_label_clauses», List.map_cons, List.map_nil, «erase:$update_label:clause:0»]
  | @Call.«$free_memtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_memtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_memtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_memtype_clauses», SpecTec.«$free_memtype_clauses», List.map_cons, List.map_nil, «erase:$free_memtype:clause:0»]
  | @Call.«$free_mem» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_mem_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_mem_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_mem_clauses», SpecTec.«$free_mem_clauses», List.map_cons, List.map_nil, «erase:$free_mem:clause:0»]
  | @Call.«$match_numtype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_numtype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_numtype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_numtype_clauses», SpecTec.«$match_numtype_clauses», List.map_cons, List.map_nil, «erase:$match_numtype:clause:0», «erase:$match_numtype:clause:1»]
  | @Call.«$match_vectype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_vectype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_vectype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_vectype_clauses», SpecTec.«$match_vectype_clauses», List.map_cons, List.map_nil, «erase:$match_vectype:clause:0»]
  | @Call.«$match_packtype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_packtype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_packtype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_packtype_clauses», SpecTec.«$match_packtype_clauses», List.map_cons, List.map_nil, «erase:$match_packtype:clause:0»]
  | @Call.«$empty_context»  => by
    change erase (ExecutablePlan.firstSuccess («$empty_context_clauses» ) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$empty_context_clauses» ) ())
    simp only [erase_firstSuccess, «$empty_context_clauses», SpecTec.«$empty_context_clauses», List.map_cons, List.map_nil, «erase:$empty_context:clause:0»]
  | @Call.«$stack» input0 => by
    change erase (ExecutablePlan.firstSuccess («$stack_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$stack_clauses» input0) ())
    simp only [erase_firstSuccess, «$stack_clauses», SpecTec.«$stack_clauses», List.map_cons, List.map_nil, «erase:$stack:clause:0»]
  | @Call.«$peek» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$peek_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$peek_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$peek_clauses», SpecTec.«$peek_clauses», List.map_cons, List.map_nil, «erase:$peek:clause:0», «erase:$peek:clause:1»]
  | @Call.«$local» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$local_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$local_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$local_clauses», SpecTec.«$local_clauses», List.map_cons, List.map_nil, «erase:$local:clause:0»]
  | @Call.«$init_local» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$init_local_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$init_local_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$init_local_clauses», SpecTec.«$init_local_clauses», List.map_cons, List.map_nil, «erase:$init_local:clause:0»]
  | @Call.«$init_locals» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$init_locals_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$init_locals_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$init_locals_clauses», SpecTec.«$init_locals_clauses», List.map_cons, List.map_nil, «erase:$init_locals:clause:0», «erase:$init_locals:clause:1»]
  | @Call.«$init_valtypes» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$init_valtypes_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$init_valtypes_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$init_valtypes_clauses», SpecTec.«$init_valtypes_clauses», List.map_cons, List.map_nil, «erase:$init_valtypes:clause:0», «erase:$init_valtypes:clause:1»]
  | @Call.Numtype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Numtype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Numtype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Numtype_ok_clauses, SpecTec.Numtype_ok_clauses, List.map_cons, List.map_nil, «erase:Numtype_ok:clause:0»]
  | @Call.Vectype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Vectype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Vectype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Vectype_ok_clauses, SpecTec.Vectype_ok_clauses, List.map_cons, List.map_nil, «erase:Vectype_ok:clause:0»]
  | @Call.Limits_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Limits_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Limits_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Limits_ok_clauses, SpecTec.Limits_ok_clauses, List.map_cons, List.map_nil, «erase:Limits_ok:clause:0», «erase:Limits_ok:clause:1»]
  | @Call.«Instr_ok:br_table:iter:3» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Instr_ok:br_table:iter:3_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:br_table:iter:3_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Instr_ok:br_table:iter:3_clauses», SpecTec.«Instr_ok:br_table:iter:3_clauses», List.map_cons, List.map_nil, «erase:Instr_ok:br_table:iter:3:clause:0», «erase:Instr_ok:br_table:iter:3:clause:1»]
  | @Call.«$check_lane_index» input0 => by
    change erase (ExecutablePlan.firstSuccess («$check_lane_index_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$check_lane_index_clauses» input0) ())
    simp only [erase_firstSuccess, «$check_lane_index_clauses», SpecTec.«$check_lane_index_clauses», List.map_cons, List.map_nil, «erase:$check_lane_index:clause:0», «erase:$check_lane_index:clause:1», «erase:$check_lane_index:clause:2»]
  | @Call.«Funcbody_ok:rule:iter:2» input0 => by
    change erase (ExecutablePlan.firstSuccess («Funcbody_ok:rule:iter:2_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Funcbody_ok:rule:iter:2_clauses» input0) ())
    simp only [erase_firstSuccess, «Funcbody_ok:rule:iter:2_clauses», SpecTec.«Funcbody_ok:rule:iter:2_clauses», List.map_cons, List.map_nil, «erase:Funcbody_ok:rule:iter:2:clause:0», «erase:Funcbody_ok:rule:iter:2:clause:1»]
  | @Call.«$numtype_of_addrtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$numtype_of_addrtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$numtype_of_addrtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$numtype_of_addrtype_clauses», SpecTec.«$numtype_of_addrtype_clauses», List.map_cons, List.map_nil, «erase:$numtype_of_addrtype:clause:0», «erase:$numtype_of_addrtype:clause:1»]
  | @Call.Memtype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Memtype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Memtype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Memtype_ok_clauses, SpecTec.Memtype_ok_clauses, List.map_cons, List.map_nil, «erase:Memtype_ok:clause:0», «erase:Memtype_ok:clause:1»]
  | @Call.Vstoreop_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Vstoreop_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Vstoreop_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Vstoreop_ok_clauses, SpecTec.Vstoreop_ok_clauses, List.map_cons, List.map_nil, «erase:Vstoreop_ok:clause:0», «erase:Vstoreop_ok:clause:1»]
  | @Call.Mem_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Mem_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Mem_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Mem_ok_clauses, SpecTec.Mem_ok_clauses, List.map_cons, List.map_nil, «erase:Mem_ok:clause:0»]
  | @Call.Mems_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Mems_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Mems_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Mems_ok_clauses, SpecTec.Mems_ok_clauses, List.map_cons, List.map_nil, «erase:Mems_ok:clause:0», «erase:Mems_ok:clause:1»]
  | @Call.«$free_catch» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_catch_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_catch_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_catch_clauses», SpecTec.«$free_catch_clauses», List.map_cons, List.map_nil, «erase:$free_catch:clause:0», «erase:$free_catch:clause:1», «erase:$free_catch:clause:2», «erase:$free_catch:clause:3»]
  | @Call.«$push» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$push_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$push_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$push_clauses», SpecTec.«$push_clauses», List.map_cons, List.map_nil, «erase:$push:clause:0», «erase:$push:clause:1», «erase:$push:clause:2»]
  | @Call.«$free_exportdesc» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_exportdesc_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_exportdesc_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_exportdesc_clauses», SpecTec.«$free_exportdesc_clauses», List.map_cons, List.map_nil, «erase:$free_exportdesc:clause:0», «erase:$free_exportdesc:clause:1», «erase:$free_exportdesc:clause:2», «erase:$free_exportdesc:clause:3», «erase:$free_exportdesc:clause:4»]
  | @Call.«$free_export» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_export_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_export_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_export_clauses», SpecTec.«$free_export_clauses», List.map_cons, List.map_nil, «erase:$free_export:clause:0»]
  | @Call.Export_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Export_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Export_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Export_ok_clauses, SpecTec.Export_ok_clauses, List.map_cons, List.map_nil, «erase:Export_ok:clause:0», «erase:Export_ok:clause:1», «erase:Export_ok:clause:2», «erase:Export_ok:clause:3», «erase:Export_ok:clause:4»]
  | @Call.Exports_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Exports_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Exports_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Exports_ok_clauses, SpecTec.Exports_ok_clauses, List.map_cons, List.map_nil, «erase:Exports_ok:clause:0», «erase:Exports_ok:clause:1»]
  | @Call.«$type_externop» input0 => by
    change erase (ExecutablePlan.firstSuccess («$type_externop_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$type_externop_clauses» input0) ())
    simp only [erase_firstSuccess, «$type_externop_clauses», SpecTec.«$type_externop_clauses», List.map_cons, List.map_nil, «erase:$type_externop:clause:0», «erase:$type_externop:clause:1»]
  | @Call.«$is_const» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$is_const_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$is_const_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$is_const_clauses», SpecTec.«$is_const_clauses», List.map_cons, List.map_nil, «erase:$is_const:clause:0», «erase:$is_const:clause:1», «erase:$is_const:clause:2», «erase:$is_const:clause:3», «erase:$is_const:clause:4», «erase:$is_const:clause:5», «erase:$is_const:clause:6», «erase:$is_const:clause:7», «erase:$is_const:clause:8», «erase:$is_const:clause:9», «erase:$is_const:clause:10», «erase:$is_const:clause:11»]
  | @Call.«Const_ok:rule:iter:0» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Const_ok:rule:iter:0_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Const_ok:rule:iter:0_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Const_ok:rule:iter:0_clauses», SpecTec.«Const_ok:rule:iter:0_clauses», List.map_cons, List.map_nil, «erase:Const_ok:rule:iter:0:clause:0», «erase:Const_ok:rule:iter:0:clause:1»]
  | @Call.«$type_lane» A B C D E F input0 => by
    change erase (ExecutablePlan.firstSuccess («$type_lane_clauses» A B C D E F input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$type_lane_clauses» A B C D E F input0) ())
    simp only [erase_firstSuccess, «$type_lane_clauses», SpecTec.«$type_lane_clauses», List.map_cons, List.map_nil, «erase:$type_lane:clause:0», «erase:$type_lane:clause:1», «erase:$type_lane:clause:2», «erase:$type_lane:clause:3», «erase:$type_lane:clause:4», «erase:$type_lane:clause:5»]
  | @Call.«$type_vec_lane» A_T B_T C_T D_T E_T F_T input0 => by
    change erase (ExecutablePlan.firstSuccess («$type_vec_lane_clauses» A_T B_T C_T D_T E_T F_T input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$type_vec_lane_clauses» A_T B_T C_T D_T E_T F_T input0) ())
    simp only [erase_firstSuccess, «$type_vec_lane_clauses», SpecTec.«$type_vec_lane_clauses», List.map_cons, List.map_nil, «erase:$type_vec_lane:clause:0», «erase:$type_vec_lane:clause:1», «erase:$type_vec_lane:clause:2», «erase:$type_vec_lane:clause:3», «erase:$type_vec_lane:clause:4», «erase:$type_vec_lane:clause:5»]
  | @Call.«$lane_extractop» input0 => by
    change erase (ExecutablePlan.firstSuccess («$lane_extractop_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$lane_extractop_clauses» input0) ())
    simp only [erase_firstSuccess, «$lane_extractop_clauses», SpecTec.«$lane_extractop_clauses», List.map_cons, List.map_nil, «erase:$lane_extractop:clause:0», «erase:$lane_extractop:clause:1», «erase:$lane_extractop:clause:2», «erase:$lane_extractop:clause:3», «erase:$lane_extractop:clause:4», «erase:$lane_extractop:clause:5»]
  | @Call.«$lane_replaceop» input0 => by
    change erase (ExecutablePlan.firstSuccess («$lane_replaceop_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$lane_replaceop_clauses» input0) ())
    simp only [erase_firstSuccess, «$lane_replaceop_clauses», SpecTec.«$lane_replaceop_clauses», List.map_cons, List.map_nil, «erase:$lane_replaceop:clause:0», «erase:$lane_replaceop:clause:1», «erase:$lane_replaceop:clause:2», «erase:$lane_replaceop:clause:3», «erase:$lane_replaceop:clause:4», «erase:$lane_replaceop:clause:5»]
  | @Call.«$num_lanes» A B C D E F input0 => by
    change erase (ExecutablePlan.firstSuccess («$num_lanes_clauses» A B C D E F input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$num_lanes_clauses» A B C D E F input0) ())
    simp only [erase_firstSuccess, «$num_lanes_clauses», SpecTec.«$num_lanes_clauses», List.map_cons, List.map_nil, «erase:$num_lanes:clause:0», «erase:$num_lanes:clause:1», «erase:$num_lanes:clause:2», «erase:$num_lanes:clause:3», «erase:$num_lanes:clause:4», «erase:$num_lanes:clause:5»]
  | @Call.«$diff_reftype» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$diff_reftype_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$diff_reftype_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$diff_reftype_clauses», SpecTec.«$diff_reftype_clauses», List.map_cons, List.map_nil, «erase:$diff_reftype:clause:0», «erase:$diff_reftype:clause:1»]
  | @Call.«$match_null» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$match_null_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_null_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$match_null_clauses», SpecTec.«$match_null_clauses», List.map_cons, List.map_nil, «erase:$match_null:clause:0», «erase:$match_null:clause:1», «erase:$match_null:clause:2»]
  | @Call.«$type_num» A_T B_T C_T D_T input0 => by
    change erase (ExecutablePlan.firstSuccess («$type_num_clauses» A_T B_T C_T D_T input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$type_num_clauses» A_T B_T C_T D_T input0) ())
    simp only [erase_firstSuccess, «$type_num_clauses», SpecTec.«$type_num_clauses», List.map_cons, List.map_nil, «erase:$type_num:clause:0», «erase:$type_num:clause:1», «erase:$type_num:clause:2», «erase:$type_num:clause:3»]
  | @Call.«$type_cvtop» input0 => by
    change erase (ExecutablePlan.firstSuccess («$type_cvtop_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$type_cvtop_clauses» input0) ())
    simp only [erase_firstSuccess, «$type_cvtop_clauses», SpecTec.«$type_cvtop_clauses», List.map_cons, List.map_nil, «erase:$type_cvtop:clause:0», «erase:$type_cvtop:clause:1», «erase:$type_cvtop:clause:2», «erase:$type_cvtop:clause:3», «erase:$type_cvtop:clause:4», «erase:$type_cvtop:clause:5», «erase:$type_cvtop:clause:6», «erase:$type_cvtop:clause:7», «erase:$type_cvtop:clause:8», «erase:$type_cvtop:clause:9», «erase:$type_cvtop:clause:10», «erase:$type_cvtop:clause:11»]
  | @Call.«$check_uop_extends» input0 => by
    change erase (ExecutablePlan.firstSuccess («$check_uop_extends_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$check_uop_extends_clauses» input0) ())
    simp only [erase_firstSuccess, «$check_uop_extends_clauses», SpecTec.«$check_uop_extends_clauses», List.map_cons, List.map_nil, «erase:$check_uop_extends:clause:0», «erase:$check_uop_extends:clause:1», «erase:$check_uop_extends:clause:2»]
  | @Call.«$pack_size» input0 => by
    change erase (ExecutablePlan.firstSuccess («$pack_size_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$pack_size_clauses» input0) ())
    simp only [erase_firstSuccess, «$pack_size_clauses», SpecTec.«$pack_size_clauses», List.map_cons, List.map_nil, «erase:$pack_size:clause:0», «erase:$pack_size:clause:1», «erase:$pack_size:clause:2», «erase:$pack_size:clause:3»]
  | @Call.Pack_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Pack_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Pack_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Pack_ok_clauses, SpecTec.Pack_ok_clauses, List.map_cons, List.map_nil, «erase:Pack_ok:clause:0»]
  | @Call.Unop_ok input0 => by
    change erase (ExecutablePlan.firstSuccess (Unop_ok_clauses input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.Unop_ok_clauses input0) ())
    simp only [erase_firstSuccess, Unop_ok_clauses, SpecTec.Unop_ok_clauses, List.map_cons, List.map_nil, «erase:Unop_ok:clause:0», «erase:Unop_ok:clause:1», «erase:Unop_ok:clause:2»]
  | @Call.Loadop_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Loadop_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Loadop_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Loadop_ok_clauses, SpecTec.Loadop_ok_clauses, List.map_cons, List.map_nil, «erase:Loadop_ok:clause:0», «erase:Loadop_ok:clause:1», «erase:Loadop_ok:clause:2», «erase:Loadop_ok:clause:3»]
  | @Call.Storeop_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Storeop_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Storeop_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Storeop_ok_clauses, SpecTec.Storeop_ok_clauses, List.map_cons, List.map_nil, «erase:Storeop_ok:clause:0», «erase:Storeop_ok:clause:1», «erase:Storeop_ok:clause:2», «erase:Storeop_ok:clause:3»]
  | @Call.Vloadop_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Vloadop_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Vloadop_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Vloadop_ok_clauses, SpecTec.Vloadop_ok_clauses, List.map_cons, List.map_nil, «erase:Vloadop_ok:clause:0», «erase:Vloadop_ok:clause:1», «erase:Vloadop_ok:clause:2», «erase:Vloadop_ok:clause:3»]
  | @Call.Vlaneop_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Vlaneop_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Vlaneop_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Vlaneop_ok_clauses, SpecTec.Vlaneop_ok_clauses, List.map_cons, List.map_nil, «erase:Vlaneop_ok:clause:0», «erase:Vlaneop_ok:clause:1»]
  | @Call.«$unpacked_storage_type» input0 => by
    change erase (ExecutablePlan.firstSuccess («$unpacked_storage_type_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$unpacked_storage_type_clauses» input0) ())
    simp only [erase_firstSuccess, «$unpacked_storage_type_clauses», SpecTec.«$unpacked_storage_type_clauses», List.map_cons, List.map_nil, «erase:$unpacked_storage_type:clause:0», «erase:$unpacked_storage_type:clause:1»]
  | @Call.«$unpacked_field_type» input0 => by
    change erase (ExecutablePlan.firstSuccess («$unpacked_field_type_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$unpacked_field_type_clauses» input0) ())
    simp only [erase_firstSuccess, «$unpacked_field_type_clauses», SpecTec.«$unpacked_field_type_clauses», List.map_cons, List.map_nil, «erase:$unpacked_field_type:clause:0»]
  | @Call.«$is_packed_storage_type» input0 => by
    change erase (ExecutablePlan.firstSuccess («$is_packed_storage_type_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$is_packed_storage_type_clauses» input0) ())
    simp only [erase_firstSuccess, «$is_packed_storage_type_clauses», SpecTec.«$is_packed_storage_type_clauses», List.map_cons, List.map_nil, «erase:$is_packed_storage_type:clause:0», «erase:$is_packed_storage_type:clause:1»]
  | @Call.«Instr_ok:struct.new.explicit:iter:1» input0 => by
    change erase (ExecutablePlan.firstSuccess («Instr_ok:struct.new.explicit:iter:1_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:struct.new.explicit:iter:1_clauses» input0) ())
    simp only [erase_firstSuccess, «Instr_ok:struct.new.explicit:iter:1_clauses», SpecTec.«Instr_ok:struct.new.explicit:iter:1_clauses», List.map_cons, List.map_nil, «erase:Instr_ok:struct.new.explicit:iter:1:clause:0», «erase:Instr_ok:struct.new.explicit:iter:1:clause:1»]
  | @Call.«$functype_of_strtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$functype_of_strtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$functype_of_strtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$functype_of_strtype_clauses», SpecTec.«$functype_of_strtype_clauses», List.map_cons, List.map_nil, «erase:$functype_of_strtype:clause:0»]
  | @Call.«$abs_of_str_type» input0 => by
    change erase (ExecutablePlan.firstSuccess («$abs_of_str_type_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$abs_of_str_type_clauses» input0) ())
    simp only [erase_firstSuccess, «$abs_of_str_type_clauses», SpecTec.«$abs_of_str_type_clauses», List.map_cons, List.map_nil, «erase:$abs_of_str_type:clause:0», «erase:$abs_of_str_type:clause:1», «erase:$abs_of_str_type:clause:2»]
  | @Call.«$s_unroll» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$s_unroll_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$s_unroll_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$s_unroll_clauses», SpecTec.«$s_unroll_clauses», List.map_cons, List.map_nil, «erase:$s_unroll:clause:0», «erase:$s_unroll:clause:1»]
  | @Call.«$s_roll» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$s_roll_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$s_roll_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$s_roll_clauses», SpecTec.«$s_roll_clauses», List.map_cons, List.map_nil, «erase:$s_roll:clause:0», «erase:$s_roll:clause:1»]
  | @Call.«$free_typevar» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_typevar_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_typevar_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_typevar_clauses», SpecTec.«$free_typevar_clauses», List.map_cons, List.map_nil, «erase:$free_typevar:clause:0», «erase:$free_typevar:clause:1»]
  | @Call.«$subst_of» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$subst_of_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_of_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$subst_of_clauses», SpecTec.«$subst_of_clauses», List.map_cons, List.map_nil, «erase:$subst_of:clause:0», «erase:$subst_of:clause:1»]
  | @Call.«$is_num_type» input0 => by
    change erase (ExecutablePlan.firstSuccess («$is_num_type_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$is_num_type_clauses» input0) ())
    simp only [erase_firstSuccess, «$is_num_type_clauses», SpecTec.«$is_num_type_clauses», List.map_cons, List.map_nil, «erase:$is_num_type:clause:0», «erase:$is_num_type:clause:1», «erase:$is_num_type:clause:2»]
  | @Call.«$peek_ref» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$peek_ref_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$peek_ref_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$peek_ref_clauses», SpecTec.«$peek_ref_clauses», List.map_cons, List.map_nil, «erase:$peek_ref:clause:0», «erase:$peek_ref:clause:1»]
  | @Call.«$is_vec_type» input0 => by
    change erase (ExecutablePlan.firstSuccess («$is_vec_type_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$is_vec_type_clauses» input0) ())
    simp only [erase_firstSuccess, «$is_vec_type_clauses», SpecTec.«$is_vec_type_clauses», List.map_cons, List.map_nil, «erase:$is_vec_type:clause:0», «erase:$is_vec_type:clause:1», «erase:$is_vec_type:clause:2»]
  | @Call.«$defaultable» input0 => by
    change erase (ExecutablePlan.firstSuccess («$defaultable_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$defaultable_clauses» input0) ())
    simp only [erase_firstSuccess, «$defaultable_clauses», SpecTec.«$defaultable_clauses», List.map_cons, List.map_nil, «erase:$defaultable:clause:0», «erase:$defaultable:clause:1», «erase:$defaultable:clause:2», «erase:$defaultable:clause:3»]
  | @Call.«Instr_ok:struct.new.implicit:iter:1» input0 => by
    change erase (ExecutablePlan.firstSuccess («Instr_ok:struct.new.implicit:iter:1_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:struct.new.implicit:iter:1_clauses» input0) ())
    simp only [erase_firstSuccess, «Instr_ok:struct.new.implicit:iter:1_clauses», SpecTec.«Instr_ok:struct.new.implicit:iter:1_clauses», List.map_cons, List.map_nil, «erase:Instr_ok:struct.new.implicit:iter:1:clause:0», «erase:Instr_ok:struct.new.implicit:iter:1:clause:1»]
  | @Call.«$check_vbop_shuffle» input0 => by
    change erase (ExecutablePlan.firstSuccess («$check_vbop_shuffle_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$check_vbop_shuffle_clauses» input0) ())
    simp only [erase_firstSuccess, «$check_vbop_shuffle_clauses», SpecTec.«$check_vbop_shuffle_clauses», List.map_cons, List.map_nil, «erase:$check_vbop_shuffle:clause:0», «erase:$check_vbop_shuffle:clause:1»]
  | @Call.Vecbinop_ok input0 => by
    change erase (ExecutablePlan.firstSuccess (Vecbinop_ok_clauses input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.Vecbinop_ok_clauses input0) ())
    simp only [erase_firstSuccess, Vecbinop_ok_clauses, SpecTec.Vecbinop_ok_clauses, List.map_cons, List.map_nil, «erase:Vecbinop_ok:clause:0», «erase:Vecbinop_ok:clause:1»]
  | @Call.«$subst_heaptype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_heaptype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_heaptype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_heaptype_clauses», SpecTec.«$subst_heaptype_clauses», List.map_cons, List.map_nil, «erase:$subst_heaptype:clause:0», «erase:$subst_heaptype:clause:1», «erase:$subst_heaptype:clause:2»]
  | @Call.«$subst_subtype:case_1:iter:0» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_subtype:case_1:iter:0_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_subtype:case_1:iter:0_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_subtype:case_1:iter:0_clauses», SpecTec.«$subst_subtype:case_1:iter:0_clauses», List.map_cons, List.map_nil, «erase:$subst_subtype:case_1:iter:0:clause:0», «erase:$subst_subtype:case_1:iter:0:clause:1»]
  | @Call.«$subst_reftype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_reftype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_reftype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_reftype_clauses», SpecTec.«$subst_reftype_clauses», List.map_cons, List.map_nil, «erase:$subst_reftype:clause:0»]
  | @Call.«$subst_valtype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_valtype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_valtype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_valtype_clauses», SpecTec.«$subst_valtype_clauses», List.map_cons, List.map_nil, «erase:$subst_valtype:clause:0», «erase:$subst_valtype:clause:1», «erase:$subst_valtype:clause:2», «erase:$subst_valtype:clause:3»]
  | @Call.«$subst_resulttype:case_1:iter:0» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_resulttype:case_1:iter:0_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_resulttype:case_1:iter:0_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_resulttype:case_1:iter:0_clauses», SpecTec.«$subst_resulttype:case_1:iter:0_clauses», List.map_cons, List.map_nil, «erase:$subst_resulttype:case_1:iter:0:clause:0», «erase:$subst_resulttype:case_1:iter:0:clause:1»]
  | @Call.«$subst_resulttype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_resulttype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_resulttype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_resulttype_clauses», SpecTec.«$subst_resulttype_clauses», List.map_cons, List.map_nil, «erase:$subst_resulttype:clause:0»]
  | @Call.«$subst_functype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_functype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_functype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_functype_clauses», SpecTec.«$subst_functype_clauses», List.map_cons, List.map_nil, «erase:$subst_functype:clause:0»]
  | @Call.«$subst_storagetype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_storagetype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_storagetype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_storagetype_clauses», SpecTec.«$subst_storagetype_clauses», List.map_cons, List.map_nil, «erase:$subst_storagetype:clause:0», «erase:$subst_storagetype:clause:1»]
  | @Call.«$subst_fieldtype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_fieldtype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_fieldtype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_fieldtype_clauses», SpecTec.«$subst_fieldtype_clauses», List.map_cons, List.map_nil, «erase:$subst_fieldtype:clause:0»]
  | @Call.«$subst_structtype:case_1:iter:0» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_structtype:case_1:iter:0_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_structtype:case_1:iter:0_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_structtype:case_1:iter:0_clauses», SpecTec.«$subst_structtype:case_1:iter:0_clauses», List.map_cons, List.map_nil, «erase:$subst_structtype:case_1:iter:0:clause:0», «erase:$subst_structtype:case_1:iter:0:clause:1»]
  | @Call.«$subst_structtype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_structtype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_structtype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_structtype_clauses», SpecTec.«$subst_structtype_clauses», List.map_cons, List.map_nil, «erase:$subst_structtype:clause:0»]
  | @Call.«$subst_arraytype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_arraytype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_arraytype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_arraytype_clauses», SpecTec.«$subst_arraytype_clauses», List.map_cons, List.map_nil, «erase:$subst_arraytype:clause:0»]
  | @Call.«$subst_strtype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_strtype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_strtype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_strtype_clauses», SpecTec.«$subst_strtype_clauses», List.map_cons, List.map_nil, «erase:$subst_strtype:clause:0», «erase:$subst_strtype:clause:1», «erase:$subst_strtype:clause:2»]
  | @Call.«$subst_subtype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_subtype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_subtype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_subtype_clauses», SpecTec.«$subst_subtype_clauses», List.map_cons, List.map_nil, «erase:$subst_subtype:clause:0»]
  | @Call.«$subst_rectype:case_1:iter:0» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_rectype:case_1:iter:0_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_rectype:case_1:iter:0_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_rectype:case_1:iter:0_clauses», SpecTec.«$subst_rectype:case_1:iter:0_clauses», List.map_cons, List.map_nil, «erase:$subst_rectype:case_1:iter:0:clause:0», «erase:$subst_rectype:case_1:iter:0:clause:1»]
  | @Call.«$subst_rectype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_rectype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_rectype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_rectype_clauses», SpecTec.«$subst_rectype_clauses», List.map_cons, List.map_nil, «erase:$subst_rectype:clause:0»]
  | @Call.«$subst_deftype» X_T input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$subst_deftype_clauses» X_T input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$subst_deftype_clauses» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2) ())
    simp only [erase_firstSuccess, «$subst_deftype_clauses», SpecTec.«$subst_deftype_clauses», List.map_cons, List.map_nil, «erase:$subst_deftype:clause:0»]
  | @Call.«$rollrt» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$rollrt_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$rollrt_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$rollrt_clauses», SpecTec.«$rollrt_clauses», List.map_cons, List.map_nil, «erase:$rollrt:clause:0»]
  | @Call.«$unrollrt» input0 => by
    change erase (ExecutablePlan.firstSuccess («$unrollrt_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$unrollrt_clauses» input0) ())
    simp only [erase_firstSuccess, «$unrollrt_clauses», SpecTec.«$unrollrt_clauses», List.map_cons, List.map_nil, «erase:$unrollrt:clause:0»]
  | @Call.«$rolldt» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$rolldt_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$rolldt_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$rolldt_clauses», SpecTec.«$rolldt_clauses», List.map_cons, List.map_nil, «erase:$rolldt:clause:0»]
  | @Call.«$unrolldt» input0 => by
    change erase (ExecutablePlan.firstSuccess («$unrolldt_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$unrolldt_clauses» input0) ())
    simp only [erase_firstSuccess, «$unrolldt_clauses», SpecTec.«$unrolldt_clauses», List.map_cons, List.map_nil, «erase:$unrolldt:clause:0»]
  | @Call.«$expanddt» input0 => by
    change erase (ExecutablePlan.firstSuccess («$expanddt_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$expanddt_clauses» input0) ())
    simp only [erase_firstSuccess, «$expanddt_clauses», SpecTec.«$expanddt_clauses», List.map_cons, List.map_nil, «erase:$expanddt:clause:0»]
  | @Call.«$free_heaptype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_heaptype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_heaptype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_heaptype_clauses», SpecTec.«$free_heaptype_clauses», List.map_cons, List.map_nil, «erase:$free_heaptype:clause:0», «erase:$free_heaptype:clause:1»]
  | @Call.«$free_reftype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_reftype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_reftype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_reftype_clauses», SpecTec.«$free_reftype_clauses», List.map_cons, List.map_nil, «erase:$free_reftype:clause:0»]
  | @Call.«$free_valtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_valtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_valtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_valtype_clauses», SpecTec.«$free_valtype_clauses», List.map_cons, List.map_nil, «erase:$free_valtype:clause:0», «erase:$free_valtype:clause:1», «erase:$free_valtype:clause:2», «erase:$free_valtype:clause:3»]
  | @Call.«$free_functype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_functype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_functype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_functype_clauses», SpecTec.«$free_functype_clauses», List.map_cons, List.map_nil, «erase:$free_functype:clause:0»]
  | @Call.«$free_storagetype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_storagetype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_storagetype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_storagetype_clauses», SpecTec.«$free_storagetype_clauses», List.map_cons, List.map_nil, «erase:$free_storagetype:clause:0», «erase:$free_storagetype:clause:1»]
  | @Call.«$free_fieldtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_fieldtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_fieldtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_fieldtype_clauses», SpecTec.«$free_fieldtype_clauses», List.map_cons, List.map_nil, «erase:$free_fieldtype:clause:0»]
  | @Call.«$free_structtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_structtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_structtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_structtype_clauses», SpecTec.«$free_structtype_clauses», List.map_cons, List.map_nil, «erase:$free_structtype:clause:0»]
  | @Call.«$free_arraytype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_arraytype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_arraytype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_arraytype_clauses», SpecTec.«$free_arraytype_clauses», List.map_cons, List.map_nil, «erase:$free_arraytype:clause:0»]
  | @Call.«$free_strtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_strtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_strtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_strtype_clauses», SpecTec.«$free_strtype_clauses», List.map_cons, List.map_nil, «erase:$free_strtype:clause:0», «erase:$free_strtype:clause:1», «erase:$free_strtype:clause:2»]
  | @Call.«$free_subtype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_subtype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_subtype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_subtype_clauses», SpecTec.«$free_subtype_clauses», List.map_cons, List.map_nil, «erase:$free_subtype:clause:0»]
  | @Call.«$free_rectype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_rectype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_rectype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_rectype_clauses», SpecTec.«$free_rectype_clauses», List.map_cons, List.map_nil, «erase:$free_rectype:clause:0»]
  | @Call.«$free_type_» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_type__clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_type__clauses» input0) ())
    simp only [erase_firstSuccess, «$free_type__clauses», SpecTec.«$free_type__clauses», List.map_cons, List.map_nil, «erase:$free_type_:clause:0»]
  | @Call.«$free_globaltype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_globaltype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_globaltype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_globaltype_clauses», SpecTec.«$free_globaltype_clauses», List.map_cons, List.map_nil, «erase:$free_globaltype:clause:0»]
  | @Call.«$free_blocktype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_blocktype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_blocktype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_blocktype_clauses», SpecTec.«$free_blocktype_clauses», List.map_cons, List.map_nil, «erase:$free_blocktype:clause:0», «erase:$free_blocktype:clause:1», «erase:$free_blocktype:clause:2»]
  | @Call.«$free_instr» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_instr_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_instr_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_instr_clauses», SpecTec.«$free_instr_clauses», List.map_cons, List.map_nil, «erase:$free_instr:clause:0», «erase:$free_instr:clause:1», «erase:$free_instr:clause:2», «erase:$free_instr:clause:3», «erase:$free_instr:clause:4», «erase:$free_instr:clause:5», «erase:$free_instr:clause:6», «erase:$free_instr:clause:7», «erase:$free_instr:clause:8», «erase:$free_instr:clause:9», «erase:$free_instr:clause:10», «erase:$free_instr:clause:11», «erase:$free_instr:clause:12», «erase:$free_instr:clause:13», «erase:$free_instr:clause:14», «erase:$free_instr:clause:15», «erase:$free_instr:clause:16», «erase:$free_instr:clause:17», «erase:$free_instr:clause:18», «erase:$free_instr:clause:19», «erase:$free_instr:clause:20», «erase:$free_instr:clause:21», «erase:$free_instr:clause:22», «erase:$free_instr:clause:23», «erase:$free_instr:clause:24», «erase:$free_instr:clause:25», «erase:$free_instr:clause:26», «erase:$free_instr:clause:27», «erase:$free_instr:clause:28», «erase:$free_instr:clause:29», «erase:$free_instr:clause:30», «erase:$free_instr:clause:31», «erase:$free_instr:clause:32», «erase:$free_instr:clause:33», «erase:$free_instr:clause:34», «erase:$free_instr:clause:35», «erase:$free_instr:clause:36», «erase:$free_instr:clause:37», «erase:$free_instr:clause:38», «erase:$free_instr:clause:39», «erase:$free_instr:clause:40», «erase:$free_instr:clause:41», «erase:$free_instr:clause:42», «erase:$free_instr:clause:43», «erase:$free_instr:clause:44», «erase:$free_instr:clause:45», «erase:$free_instr:clause:46», «erase:$free_instr:clause:47», «erase:$free_instr:clause:48», «erase:$free_instr:clause:49», «erase:$free_instr:clause:50», «erase:$free_instr:clause:51», «erase:$free_instr:clause:52», «erase:$free_instr:clause:53», «erase:$free_instr:clause:54», «erase:$free_instr:clause:55», «erase:$free_instr:clause:56», «erase:$free_instr:clause:57», «erase:$free_instr:clause:58», «erase:$free_instr:clause:59», «erase:$free_instr:clause:60», «erase:$free_instr:clause:61», «erase:$free_instr:clause:62», «erase:$free_instr:clause:63», «erase:$free_instr:clause:64», «erase:$free_instr:clause:65», «erase:$free_instr:clause:66», «erase:$free_instr:clause:67», «erase:$free_instr:clause:68», «erase:$free_instr:clause:69», «erase:$free_instr:clause:70», «erase:$free_instr:clause:71», «erase:$free_instr:clause:72», «erase:$free_instr:clause:73», «erase:$free_instr:clause:74», «erase:$free_instr:clause:75», «erase:$free_instr:clause:76», «erase:$free_instr:clause:77», «erase:$free_instr:clause:78», «erase:$free_instr:clause:79», «erase:$free_instr:clause:80»]
  | @Call.«$free_block» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_block_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_block_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_block_clauses», SpecTec.«$free_block_clauses», List.map_cons, List.map_nil, «erase:$free_block:clause:0»]
  | @Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_list:specialized:627ab0672e3a767978c05fd35fc5a959_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_list:specialized:627ab0672e3a767978c05fd35fc5a959_clauses», SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959_clauses», List.map_cons, List.map_nil, «erase:$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0», «erase:$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1»]
  | @Call.«$free_const» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_const_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_const_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_const_clauses», SpecTec.«$free_const_clauses», List.map_cons, List.map_nil, «erase:$free_const:clause:0»]
  | @Call.«$free_global» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_global_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_global_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_global_clauses», SpecTec.«$free_global_clauses», List.map_cons, List.map_nil, «erase:$free_global:clause:0»]
  | @Call.«$free_tabletype» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_tabletype_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_tabletype_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_tabletype_clauses», SpecTec.«$free_tabletype_clauses», List.map_cons, List.map_nil, «erase:$free_tabletype:clause:0»]
  | @Call.«$free_table» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_table_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_table_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_table_clauses», SpecTec.«$free_table_clauses», List.map_cons, List.map_nil, «erase:$free_table:clause:0»]
  | @Call.«$free_elemmode» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$free_elemmode_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_elemmode_clauses» (fun a0 => toOriginal (input0 a0)) input1) ())
    simp only [erase_firstSuccess, «$free_elemmode_clauses», SpecTec.«$free_elemmode_clauses», List.map_cons, List.map_nil, «erase:$free_elemmode:clause:0», «erase:$free_elemmode:clause:1»]
  | @Call.«$free_elem» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_elem_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_elem_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_elem_clauses», SpecTec.«$free_elem_clauses», List.map_cons, List.map_nil, «erase:$free_elem:clause:0»]
  | @Call.«$free_datamode» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$free_datamode_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_datamode_clauses» (fun a0 => toOriginal (input0 a0)) input1) ())
    simp only [erase_firstSuccess, «$free_datamode_clauses», SpecTec.«$free_datamode_clauses», List.map_cons, List.map_nil, «erase:$free_datamode:clause:0», «erase:$free_datamode:clause:1»]
  | @Call.«$free_data» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_data_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_data_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_data_clauses», SpecTec.«$free_data_clauses», List.map_cons, List.map_nil, «erase:$free_data:clause:0»]
  | @Call.«$free_importdesc» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_importdesc_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_importdesc_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_importdesc_clauses», SpecTec.«$free_importdesc_clauses», List.map_cons, List.map_nil, «erase:$free_importdesc:clause:0», «erase:$free_importdesc:clause:1», «erase:$free_importdesc:clause:2», «erase:$free_importdesc:clause:3», «erase:$free_importdesc:clause:4»]
  | @Call.«$free_import» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_import_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_import_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_import_clauses», SpecTec.«$free_import_clauses», List.map_cons, List.map_nil, «erase:$free_import:clause:0»]
  | @Call.«$free_module» input0 => by
    change erase (ExecutablePlan.firstSuccess («$free_module_clauses» input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$free_module_clauses» input0) ())
    simp only [erase_firstSuccess, «$free_module_clauses», SpecTec.«$free_module_clauses», List.map_cons, List.map_nil, «erase:$free_module:clause:0»]
  | @Call.«$match_deftype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_deftype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_deftype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_deftype_clauses», SpecTec.«$match_deftype_clauses», List.map_cons, List.map_nil, «erase:$match_deftype:clause:0», «erase:$match_deftype:clause:1», «erase:$match_deftype:clause:2»]
  | @Call.«$match_heaptype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_heaptype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_heaptype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_heaptype_clauses», SpecTec.«$match_heaptype_clauses», List.map_cons, List.map_nil, «erase:$match_heaptype:clause:0», «erase:$match_heaptype:clause:1», «erase:$match_heaptype:clause:2», «erase:$match_heaptype:clause:3», «erase:$match_heaptype:clause:4», «erase:$match_heaptype:clause:5», «erase:$match_heaptype:clause:6», «erase:$match_heaptype:clause:7», «erase:$match_heaptype:clause:8», «erase:$match_heaptype:clause:9», «erase:$match_heaptype:clause:10», «erase:$match_heaptype:clause:11», «erase:$match_heaptype:clause:12», «erase:$match_heaptype:clause:13»]
  | @Call.«$match_heaptype_exists» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_heaptype_exists_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_heaptype_exists_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_heaptype_exists_clauses», SpecTec.«$match_heaptype_exists_clauses», List.map_cons, List.map_nil, «erase:$match_heaptype_exists:clause:0», «erase:$match_heaptype_exists:clause:1», «erase:$match_heaptype_exists:clause:2»]
  | @Call.«$match_reftype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_reftype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_reftype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_reftype_clauses», SpecTec.«$match_reftype_clauses», List.map_cons, List.map_nil, «erase:$match_reftype:clause:0», «erase:$match_reftype:clause:1»]
  | @Call.«$match_valtype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_valtype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_valtype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_valtype_clauses», SpecTec.«$match_valtype_clauses», List.map_cons, List.map_nil, «erase:$match_valtype:clause:0», «erase:$match_valtype:clause:1», «erase:$match_valtype:clause:2», «erase:$match_valtype:clause:3», «erase:$match_valtype:clause:4»]
  | @Call.«$match_storagetype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_storagetype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_storagetype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_storagetype_clauses», SpecTec.«$match_storagetype_clauses», List.map_cons, List.map_nil, «erase:$match_storagetype:clause:0», «erase:$match_storagetype:clause:1», «erase:$match_storagetype:clause:2»]
  | @Call.«$match_fieldtype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_fieldtype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_fieldtype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_fieldtype_clauses», SpecTec.«$match_fieldtype_clauses», List.map_cons, List.map_nil, «erase:$match_fieldtype:clause:0», «erase:$match_fieldtype:clause:1», «erase:$match_fieldtype:clause:2»]
  | @Call.«$match_arraytype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_arraytype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_arraytype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_arraytype_clauses», SpecTec.«$match_arraytype_clauses», List.map_cons, List.map_nil, «erase:$match_arraytype:clause:0»]
  | @Call.«$match_structtype:case_1:iter:0» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_structtype:case_1:iter:0_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_structtype:case_1:iter:0_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_structtype:case_1:iter:0_clauses», SpecTec.«$match_structtype:case_1:iter:0_clauses», List.map_cons, List.map_nil, «erase:$match_structtype:case_1:iter:0:clause:0», «erase:$match_structtype:case_1:iter:0:clause:1»]
  | @Call.«$match_structtype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_structtype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_structtype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_structtype_clauses», SpecTec.«$match_structtype_clauses», List.map_cons, List.map_nil, «erase:$match_structtype:clause:0», «erase:$match_structtype:clause:1»]
  | @Call.«$match_resulttype:case_1:iter:0» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_resulttype:case_1:iter:0_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_resulttype:case_1:iter:0_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_resulttype:case_1:iter:0_clauses», SpecTec.«$match_resulttype:case_1:iter:0_clauses», List.map_cons, List.map_nil, «erase:$match_resulttype:case_1:iter:0:clause:0», «erase:$match_resulttype:case_1:iter:0:clause:1»]
  | @Call.«$match_resulttype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_resulttype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_resulttype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_resulttype_clauses», SpecTec.«$match_resulttype_clauses», List.map_cons, List.map_nil, «erase:$match_resulttype:clause:0», «erase:$match_resulttype:clause:1»]
  | @Call.«$match_functype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_functype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_functype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_functype_clauses», SpecTec.«$match_functype_clauses», List.map_cons, List.map_nil, «erase:$match_functype:clause:0»]
  | @Call.«$match_strtype» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$match_strtype_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$match_strtype_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$match_strtype_clauses», SpecTec.«$match_strtype_clauses», List.map_cons, List.map_nil, «erase:$match_strtype:clause:0», «erase:$match_strtype:clause:1», «erase:$match_strtype:clause:2», «erase:$match_strtype:clause:3»]
  | @Call.«$top_of_str_type» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$top_of_str_type_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$top_of_str_type_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$top_of_str_type_clauses», SpecTec.«$top_of_str_type_clauses», List.map_cons, List.map_nil, «erase:$top_of_str_type:clause:0»]
  | @Call.«$top_of_heap_type» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$top_of_heap_type_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$top_of_heap_type_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$top_of_heap_type_clauses», SpecTec.«$top_of_heap_type_clauses», List.map_cons, List.map_nil, «erase:$top_of_heap_type:clause:0», «erase:$top_of_heap_type:clause:1», «erase:$top_of_heap_type:clause:2», «erase:$top_of_heap_type:clause:3», «erase:$top_of_heap_type:clause:4», «erase:$top_of_heap_type:clause:5»]
  | @Call.«Match_resulttype:rule:iter:0» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («Match_resulttype:rule:iter:0_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Match_resulttype:rule:iter:0_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «Match_resulttype:rule:iter:0_clauses», SpecTec.«Match_resulttype:rule:iter:0_clauses», List.map_cons, List.map_nil, «erase:Match_resulttype:rule:iter:0:clause:0», «erase:Match_resulttype:rule:iter:0:clause:1»]
  | @Call.Match_resulttype input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Match_resulttype_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Match_resulttype_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Match_resulttype_clauses, SpecTec.Match_resulttype_clauses, List.map_cons, List.map_nil, «erase:Match_resulttype:clause:0»]
  | @Call.«$pop» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («$pop_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$pop_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «$pop_clauses», SpecTec.«$pop_clauses», List.map_cons, List.map_nil, «erase:$pop:clause:0», «erase:$pop:clause:1», «erase:$pop:clause:2», «erase:$pop:clause:3»]
  | @Call.Heaptype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Heaptype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Heaptype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Heaptype_ok_clauses, SpecTec.Heaptype_ok_clauses, List.map_cons, List.map_nil, «erase:Heaptype_ok:clause:0», «erase:Heaptype_ok:clause:1»]
  | @Call.Reftype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Reftype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Reftype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Reftype_ok_clauses, SpecTec.Reftype_ok_clauses, List.map_cons, List.map_nil, «erase:Reftype_ok:clause:0»]
  | @Call.Valtype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Valtype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Valtype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Valtype_ok_clauses, SpecTec.Valtype_ok_clauses, List.map_cons, List.map_nil, «erase:Valtype_ok:clause:0», «erase:Valtype_ok:clause:1», «erase:Valtype_ok:clause:2»]
  | @Call.«Resulttype_ok:rule:iter:0» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Resulttype_ok:rule:iter:0_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Resulttype_ok:rule:iter:0_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Resulttype_ok:rule:iter:0_clauses», SpecTec.«Resulttype_ok:rule:iter:0_clauses», List.map_cons, List.map_nil, «erase:Resulttype_ok:rule:iter:0:clause:0», «erase:Resulttype_ok:rule:iter:0:clause:1»]
  | @Call.Resulttype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Resulttype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Resulttype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Resulttype_ok_clauses, SpecTec.Resulttype_ok_clauses, List.map_cons, List.map_nil, «erase:Resulttype_ok:clause:0»]
  | @Call.Functype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Functype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Functype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Functype_ok_clauses, SpecTec.Functype_ok_clauses, List.map_cons, List.map_nil, «erase:Functype_ok:clause:0»]
  | @Call.«Subtype_ok:rule:iter:0» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Subtype_ok:rule:iter:0_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Subtype_ok:rule:iter:0_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Subtype_ok:rule:iter:0_clauses», SpecTec.«Subtype_ok:rule:iter:0_clauses», List.map_cons, List.map_nil, «erase:Subtype_ok:rule:iter:0:clause:0», «erase:Subtype_ok:rule:iter:0:clause:1»]
  | @Call.Storagetype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Storagetype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Storagetype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Storagetype_ok_clauses, SpecTec.Storagetype_ok_clauses, List.map_cons, List.map_nil, «erase:Storagetype_ok:clause:0», «erase:Storagetype_ok:clause:1»]
  | @Call.Fieldtype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Fieldtype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Fieldtype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Fieldtype_ok_clauses, SpecTec.Fieldtype_ok_clauses, List.map_cons, List.map_nil, «erase:Fieldtype_ok:clause:0»]
  | @Call.«Structtype_ok:rule:iter:0» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Structtype_ok:rule:iter:0_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Structtype_ok:rule:iter:0_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Structtype_ok:rule:iter:0_clauses», SpecTec.«Structtype_ok:rule:iter:0_clauses», List.map_cons, List.map_nil, «erase:Structtype_ok:rule:iter:0:clause:0», «erase:Structtype_ok:rule:iter:0:clause:1»]
  | @Call.Structtype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Structtype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Structtype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Structtype_ok_clauses, SpecTec.Structtype_ok_clauses, List.map_cons, List.map_nil, «erase:Structtype_ok:clause:0»]
  | @Call.Arraytype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Arraytype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Arraytype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Arraytype_ok_clauses, SpecTec.Arraytype_ok_clauses, List.map_cons, List.map_nil, «erase:Arraytype_ok:clause:0»]
  | @Call.Strtype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Strtype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Strtype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Strtype_ok_clauses, SpecTec.Strtype_ok_clauses, List.map_cons, List.map_nil, «erase:Strtype_ok:clause:0», «erase:Strtype_ok:clause:1», «erase:Strtype_ok:clause:2»]
  | @Call.Subtype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Subtype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Subtype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Subtype_ok_clauses, SpecTec.Subtype_ok_clauses, List.map_cons, List.map_nil, «erase:Subtype_ok:clause:0»]
  | @Call.Subtype_sub_ok' input0 input1 input2 input3 => by
    change erase (ExecutablePlan.firstSuccess (Subtype_sub_ok'_clauses input0 input1 input2 input3) ()) = (SpecTecExecution.firstSuccess (SpecTec.Subtype_sub_ok'_clauses input0 input1 input2 input3) ())
    simp only [erase_firstSuccess, Subtype_sub_ok'_clauses, SpecTec.Subtype_sub_ok'_clauses, List.map_cons, List.map_nil, «erase:Subtype_sub_ok':clause:0»]
  | @Call.«Subtype_sub_ok:rule:iter:0» input0 input1 input2 input3 => by
    change erase (ExecutablePlan.firstSuccess («Subtype_sub_ok:rule:iter:0_clauses» input0 input1 input2 input3) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» input0 input1 input2 input3) ())
    simp only [erase_firstSuccess, «Subtype_sub_ok:rule:iter:0_clauses», SpecTec.«Subtype_sub_ok:rule:iter:0_clauses», List.map_cons, List.map_nil, «erase:Subtype_sub_ok:rule:iter:0:clause:0», «erase:Subtype_sub_ok:rule:iter:0:clause:1»]
  | @Call.Subtype_sub_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Subtype_sub_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Subtype_sub_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Subtype_sub_ok_clauses, SpecTec.Subtype_sub_ok_clauses, List.map_cons, List.map_nil, «erase:Subtype_sub_ok:clause:0»]
  | @Call.«Rectype_ok:rule:iter:2» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Rectype_ok:rule:iter:2_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Rectype_ok:rule:iter:2_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Rectype_ok:rule:iter:2_clauses», SpecTec.«Rectype_ok:rule:iter:2_clauses», List.map_cons, List.map_nil, «erase:Rectype_ok:rule:iter:2:clause:0», «erase:Rectype_ok:rule:iter:2:clause:1»]
  | @Call.«Rectype_ok:rule:iter:5» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Rectype_ok:rule:iter:5_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Rectype_ok:rule:iter:5_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Rectype_ok:rule:iter:5_clauses», SpecTec.«Rectype_ok:rule:iter:5_clauses», List.map_cons, List.map_nil, «erase:Rectype_ok:rule:iter:5:clause:0», «erase:Rectype_ok:rule:iter:5:clause:1»]
  | @Call.«Rectype_ok:rule:iter:6» input0 input1 input2 input3 => by
    change erase (ExecutablePlan.firstSuccess («Rectype_ok:rule:iter:6_clauses» input0 input1 input2 input3) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Rectype_ok:rule:iter:6_clauses» input0 input1 input2 input3) ())
    simp only [erase_firstSuccess, «Rectype_ok:rule:iter:6_clauses», SpecTec.«Rectype_ok:rule:iter:6_clauses», List.map_cons, List.map_nil, «erase:Rectype_ok:rule:iter:6:clause:0», «erase:Rectype_ok:rule:iter:6:clause:1»]
  | @Call.Rectype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Rectype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Rectype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Rectype_ok_clauses, SpecTec.Rectype_ok_clauses, List.map_cons, List.map_nil, «erase:Rectype_ok:clause:0»]
  | @Call.Globaltype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Globaltype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Globaltype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Globaltype_ok_clauses, SpecTec.Globaltype_ok_clauses, List.map_cons, List.map_nil, «erase:Globaltype_ok:clause:0»]
  | @Call.Tagtype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Tagtype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Tagtype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Tagtype_ok_clauses, SpecTec.Tagtype_ok_clauses, List.map_cons, List.map_nil, «erase:Tagtype_ok:clause:0»]
  | @Call.Tabletype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Tabletype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Tabletype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Tabletype_ok_clauses, SpecTec.Tabletype_ok_clauses, List.map_cons, List.map_nil, «erase:Tabletype_ok:clause:0», «erase:Tabletype_ok:clause:1»]
  | @Call.«$array_type» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$array_type_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$array_type_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$array_type_clauses», SpecTec.«$array_type_clauses», List.map_cons, List.map_nil, «erase:$array_type:clause:0»]
  | @Call.«$struct_type» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$struct_type_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$struct_type_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$struct_type_clauses», SpecTec.«$struct_type_clauses», List.map_cons, List.map_nil, «erase:$struct_type:clause:0»]
  | @Call.«$func_type» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («$func_type_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«$func_type_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «$func_type_clauses», SpecTec.«$func_type_clauses», List.map_cons, List.map_nil, «erase:$func_type:clause:0»]
  | @Call.Blocktype_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Blocktype_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Blocktype_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Blocktype_ok_clauses, SpecTec.Blocktype_ok_clauses, List.map_cons, List.map_nil, «erase:Blocktype_ok:clause:0», «erase:Blocktype_ok:clause:1», «erase:Blocktype_ok:clause:2»]
  | @Call.Catch_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Catch_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Catch_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Catch_ok_clauses, SpecTec.Catch_ok_clauses, List.map_cons, List.map_nil, «erase:Catch_ok:clause:0», «erase:Catch_ok:clause:1», «erase:Catch_ok:clause:2», «erase:Catch_ok:clause:3»]
  | @Call.«Instr_ok:br_table:iter:4» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («Instr_ok:br_table:iter:4_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:br_table:iter:4_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «Instr_ok:br_table:iter:4_clauses», SpecTec.«Instr_ok:br_table:iter:4_clauses», List.map_cons, List.map_nil, «erase:Instr_ok:br_table:iter:4:clause:0», «erase:Instr_ok:br_table:iter:4:clause:1»]
  | @Call.«Instr_ok:try_table:iter:0» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («Instr_ok:try_table:iter:0_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:try_table:iter:0_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «Instr_ok:try_table:iter:0_clauses», SpecTec.«Instr_ok:try_table:iter:0_clauses», List.map_cons, List.map_nil, «erase:Instr_ok:try_table:iter:0:clause:0», «erase:Instr_ok:try_table:iter:0:clause:1»]
  | @Call.Instrs_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Instrs_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Instrs_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Instrs_ok_clauses, SpecTec.Instrs_ok_clauses, List.map_cons, List.map_nil, «erase:Instrs_ok:clause:0», «erase:Instrs_ok:clause:1»]
  | @Call.Instr_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Instr_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Instr_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Instr_ok_clauses, SpecTec.Instr_ok_clauses, List.map_cons, List.map_nil, «erase:Instr_ok:clause:0», «erase:Instr_ok:clause:1», «erase:Instr_ok:clause:2», «erase:Instr_ok:clause:3», «erase:Instr_ok:clause:4», «erase:Instr_ok:clause:5», «erase:Instr_ok:clause:6», «erase:Instr_ok:clause:7», «erase:Instr_ok:clause:8», «erase:Instr_ok:clause:9», «erase:Instr_ok:clause:10», «erase:Instr_ok:clause:11», «erase:Instr_ok:clause:12», «erase:Instr_ok:clause:13», «erase:Instr_ok:clause:14», «erase:Instr_ok:clause:15», «erase:Instr_ok:clause:16», «erase:Instr_ok:clause:17», «erase:Instr_ok:clause:18», «erase:Instr_ok:clause:19», «erase:Instr_ok:clause:20», «erase:Instr_ok:clause:21», «erase:Instr_ok:clause:22», «erase:Instr_ok:clause:23», «erase:Instr_ok:clause:24», «erase:Instr_ok:clause:25», «erase:Instr_ok:clause:26», «erase:Instr_ok:clause:27», «erase:Instr_ok:clause:28», «erase:Instr_ok:clause:29», «erase:Instr_ok:clause:30», «erase:Instr_ok:clause:31», «erase:Instr_ok:clause:32», «erase:Instr_ok:clause:33», «erase:Instr_ok:clause:34», «erase:Instr_ok:clause:35», «erase:Instr_ok:clause:36», «erase:Instr_ok:clause:37», «erase:Instr_ok:clause:38», «erase:Instr_ok:clause:39», «erase:Instr_ok:clause:40», «erase:Instr_ok:clause:41», «erase:Instr_ok:clause:42», «erase:Instr_ok:clause:43», «erase:Instr_ok:clause:44», «erase:Instr_ok:clause:45», «erase:Instr_ok:clause:46», «erase:Instr_ok:clause:47», «erase:Instr_ok:clause:48», «erase:Instr_ok:clause:49», «erase:Instr_ok:clause:50», «erase:Instr_ok:clause:51», «erase:Instr_ok:clause:52», «erase:Instr_ok:clause:53», «erase:Instr_ok:clause:54», «erase:Instr_ok:clause:55», «erase:Instr_ok:clause:56», «erase:Instr_ok:clause:57», «erase:Instr_ok:clause:58», «erase:Instr_ok:clause:59», «erase:Instr_ok:clause:60», «erase:Instr_ok:clause:61», «erase:Instr_ok:clause:62», «erase:Instr_ok:clause:63», «erase:Instr_ok:clause:64», «erase:Instr_ok:clause:65», «erase:Instr_ok:clause:66», «erase:Instr_ok:clause:67», «erase:Instr_ok:clause:68», «erase:Instr_ok:clause:69», «erase:Instr_ok:clause:70», «erase:Instr_ok:clause:71», «erase:Instr_ok:clause:72», «erase:Instr_ok:clause:73», «erase:Instr_ok:clause:74», «erase:Instr_ok:clause:75», «erase:Instr_ok:clause:76», «erase:Instr_ok:clause:77», «erase:Instr_ok:clause:78», «erase:Instr_ok:clause:79», «erase:Instr_ok:clause:80», «erase:Instr_ok:clause:81», «erase:Instr_ok:clause:82», «erase:Instr_ok:clause:83», «erase:Instr_ok:clause:84», «erase:Instr_ok:clause:85», «erase:Instr_ok:clause:86», «erase:Instr_ok:clause:87», «erase:Instr_ok:clause:88», «erase:Instr_ok:clause:89», «erase:Instr_ok:clause:90», «erase:Instr_ok:clause:91», «erase:Instr_ok:clause:92», «erase:Instr_ok:clause:93», «erase:Instr_ok:clause:94», «erase:Instr_ok:clause:95», «erase:Instr_ok:clause:96», «erase:Instr_ok:clause:97», «erase:Instr_ok:clause:98», «erase:Instr_ok:clause:99»]
  | @Call.Block_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Block_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Block_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Block_ok_clauses, SpecTec.Block_ok_clauses, List.map_cons, List.map_nil, «erase:Block_ok:clause:0»]
  | @Call.Type_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Type_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Type_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Type_ok_clauses, SpecTec.Type_ok_clauses, List.map_cons, List.map_nil, «erase:Type_ok:clause:0»]
  | @Call.Types_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Types_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Types_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Types_ok_clauses, SpecTec.Types_ok_clauses, List.map_cons, List.map_nil, «erase:Types_ok:clause:0», «erase:Types_ok:clause:1»]
  | @Call.Import_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Import_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Import_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Import_ok_clauses, SpecTec.Import_ok_clauses, List.map_cons, List.map_nil, «erase:Import_ok:clause:0», «erase:Import_ok:clause:1», «erase:Import_ok:clause:2», «erase:Import_ok:clause:3», «erase:Import_ok:clause:4»]
  | @Call.Imports_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Imports_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Imports_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Imports_ok_clauses, SpecTec.Imports_ok_clauses, List.map_cons, List.map_nil, «erase:Imports_ok:clause:0», «erase:Imports_ok:clause:1»]
  | @Call.Func_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Func_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Func_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Func_ok_clauses, SpecTec.Func_ok_clauses, List.map_cons, List.map_nil, «erase:Func_ok:clause:0»]
  | @Call.Funcs_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Funcs_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Funcs_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Funcs_ok_clauses, SpecTec.Funcs_ok_clauses, List.map_cons, List.map_nil, «erase:Funcs_ok:clause:0», «erase:Funcs_ok:clause:1»]
  | @Call.Tag_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Tag_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Tag_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Tag_ok_clauses, SpecTec.Tag_ok_clauses, List.map_cons, List.map_nil, «erase:Tag_ok:clause:0»]
  | @Call.Tags_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Tags_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Tags_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Tags_ok_clauses, SpecTec.Tags_ok_clauses, List.map_cons, List.map_nil, «erase:Tags_ok:clause:0», «erase:Tags_ok:clause:1»]
  | @Call.Start_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Start_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Start_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Start_ok_clauses, SpecTec.Start_ok_clauses, List.map_cons, List.map_nil, «erase:Start_ok:clause:0», «erase:Start_ok:clause:1»]
  | @Call.Const_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Const_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Const_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Const_ok_clauses, SpecTec.Const_ok_clauses, List.map_cons, List.map_nil, «erase:Const_ok:clause:0»]
  | @Call.Table_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Table_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Table_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Table_ok_clauses, SpecTec.Table_ok_clauses, List.map_cons, List.map_nil, «erase:Table_ok:clause:0»]
  | @Call.Tables_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Tables_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Tables_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Tables_ok_clauses, SpecTec.Tables_ok_clauses, List.map_cons, List.map_nil, «erase:Tables_ok:clause:0», «erase:Tables_ok:clause:1»]
  | @Call.Global_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Global_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Global_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Global_ok_clauses, SpecTec.Global_ok_clauses, List.map_cons, List.map_nil, «erase:Global_ok:clause:0»]
  | @Call.Globals_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Globals_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Globals_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Globals_ok_clauses, SpecTec.Globals_ok_clauses, List.map_cons, List.map_nil, «erase:Globals_ok:clause:0», «erase:Globals_ok:clause:1»]
  | @Call.«Elem_ok:rule:iter:0» input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess («Elem_ok:rule:iter:0_clauses» input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Elem_ok:rule:iter:0_clauses» input0 input1 input2) ())
    simp only [erase_firstSuccess, «Elem_ok:rule:iter:0_clauses», SpecTec.«Elem_ok:rule:iter:0_clauses», List.map_cons, List.map_nil, «erase:Elem_ok:rule:iter:0:clause:0», «erase:Elem_ok:rule:iter:0:clause:1»]
  | @Call.Elemmode_ok input0 input1 input2 => by
    change erase (ExecutablePlan.firstSuccess (Elemmode_ok_clauses input0 input1 input2) ()) = (SpecTecExecution.firstSuccess (SpecTec.Elemmode_ok_clauses input0 input1 input2) ())
    simp only [erase_firstSuccess, Elemmode_ok_clauses, SpecTec.Elemmode_ok_clauses, List.map_cons, List.map_nil, «erase:Elemmode_ok:clause:0», «erase:Elemmode_ok:clause:1», «erase:Elemmode_ok:clause:2»]
  | @Call.Elem_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Elem_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Elem_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Elem_ok_clauses, SpecTec.Elem_ok_clauses, List.map_cons, List.map_nil, «erase:Elem_ok:clause:0»]
  | @Call.Elems_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Elems_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Elems_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Elems_ok_clauses, SpecTec.Elems_ok_clauses, List.map_cons, List.map_nil, «erase:Elems_ok:clause:0», «erase:Elems_ok:clause:1»]
  | @Call.Datamode_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Datamode_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Datamode_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Datamode_ok_clauses, SpecTec.Datamode_ok_clauses, List.map_cons, List.map_nil, «erase:Datamode_ok:clause:0», «erase:Datamode_ok:clause:1»]
  | @Call.Data_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Data_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Data_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Data_ok_clauses, SpecTec.Data_ok_clauses, List.map_cons, List.map_nil, «erase:Data_ok:clause:0»]
  | @Call.Datas_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Datas_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Datas_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Datas_ok_clauses, SpecTec.Datas_ok_clauses, List.map_cons, List.map_nil, «erase:Datas_ok:clause:0», «erase:Datas_ok:clause:1»]
  | @Call.Local_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Local_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Local_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Local_ok_clauses, SpecTec.Local_ok_clauses, List.map_cons, List.map_nil, «erase:Local_ok:clause:0», «erase:Local_ok:clause:1»]
  | @Call.«Funcbody_ok:rule:iter:1» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Funcbody_ok:rule:iter:1_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Funcbody_ok:rule:iter:1_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Funcbody_ok:rule:iter:1_clauses», SpecTec.«Funcbody_ok:rule:iter:1_clauses», List.map_cons, List.map_nil, «erase:Funcbody_ok:rule:iter:1:clause:0», «erase:Funcbody_ok:rule:iter:1:clause:1»]
  | @Call.Funcbody_ok input0 input1 => by
    change erase (ExecutablePlan.firstSuccess (Funcbody_ok_clauses input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.Funcbody_ok_clauses input0 input1) ())
    simp only [erase_firstSuccess, Funcbody_ok_clauses, SpecTec.Funcbody_ok_clauses, List.map_cons, List.map_nil, «erase:Funcbody_ok:clause:0»]
  | @Call.«Module_ok:rule:iter:2» input0 input1 => by
    change erase (ExecutablePlan.firstSuccess («Module_ok:rule:iter:2_clauses» input0 input1) ()) = (SpecTecExecution.firstSuccess (SpecTec.«Module_ok:rule:iter:2_clauses» input0 input1) ())
    simp only [erase_firstSuccess, «Module_ok:rule:iter:2_clauses», SpecTec.«Module_ok:rule:iter:2_clauses», List.map_cons, List.map_nil, «erase:Module_ok:rule:iter:2:clause:0», «erase:Module_ok:rule:iter:2:clause:1»]
  | @Call.Module_ok input0 => by
    change erase (ExecutablePlan.firstSuccess (Module_ok_clauses input0) ()) = (SpecTecExecution.firstSuccess (SpecTec.Module_ok_clauses input0) ())
    simp only [erase_firstSuccess, Module_ok_clauses, SpecTec.Module_ok_clauses, List.map_cons, List.map_nil, «erase:Module_ok:clause:0»]
end properties.wasm_module_ok.PositiveRuntime
