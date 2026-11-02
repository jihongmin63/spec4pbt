/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import properties.wasm_module_ok.bundle.Contract
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace properties.wasm_module_ok.PositiveRuntime
open SpecTec SpecTecExecution
set_option inductive.autoPromoteIndices false in
inductive Call : Type → Type 1 where
  | «$min_» (input0 : _root_.Nat) (input1 : _root_.Nat) : Call _root_.Nat
  | «$rev_» (X : Type) (input0 : (_root_.List X)) : Call (_root_.List X)
  | «$make_» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) : Call (_root_.List X_T)
  | «$empty_set» (K : Type) : Call (set K)
  | «$in_set» (K_T : Type) [_root_.DecidableEq K_T] (input0 : K_T) (input1 : (set K_T)) : Call _root_.Bool
  | «$map_set» (X : Type) (Y : Type) [specTecCompare_0 : _root_.SpecTecCompareKey Y] (input0 : (X → (Call Y))) (input1 : (set X)) : Call (set Y)
  | «$range» (input0 : _root_.Nat) : Call (_root_.List _root_.Nat)
  | «$rolldt'» (input0 : _root_.Nat) (input1 : rectype) : Call (_root_.List deftype)
  | «$min_addrtype» (input0 : addrtype) (input1 : addrtype) : Call addrtype
  | «$num_size» (input0 : numtype) : Call _root_.Int
  | «$vec_size» (input0 : vectype) : Call _root_.Int
  | «$type_vecop» (A : Type) (input0 : (vecop A)) : Call vectype
  | «$free_empty» : Call free
  | «$fold_left» (X_T : Type) (Y : Type) (input0 : (X_T → Y → (Call X_T))) (input1 : X_T) (input2 : (_root_.List Y)) : Call X_T
  | «$free_union» (input0 : free) (input1 : free) : Call free
  | «$free_unions» (input0 : (_root_.List free)) : Call free
  | «$add_minus_one» (input0 : idx) : Call idx
  | «$free_idx» (input0 : idx) : Call (set idx)
  | «$free_shift» (input0 : (set idx)) : Call (set idx)
  | «$free_list» (X : Type) (input0 : (X → (Call free))) (input1 : (_root_.List X)) : Call free
  | «$free_opt» (X_T : Type) (input0 : (X_T → (Call free))) (input1 : (_root_.Option X_T)) : Call free
  | «$free_packtype» (input0 : packtype) : Call free
  | «$free_numtype» (input0 : numtype) : Call free
  | «$free_vectype» (input0 : vectype) : Call free
  | «$update_types» (input0 : (set typeidx)) : Call free
  | «$update_globals» (input0 : (set globalidx)) : Call free
  | «$update_tables» (input0 : (set tableidx)) : Call free
  | «$update_mems» (input0 : (set memidx)) : Call free
  | «$update_tags» (input0 : (set tagidx)) : Call free
  | «$update_funcs» (input0 : (set funcidx)) : Call free
  | «$free_start» (input0 : start) : Call free
  | «$update_elems» (input0 : (set elemidx)) : Call free
  | «$update_datas» (input0 : (set dataidx)) : Call free
  | «$update_locals» (input0 : (set localidx)) : Call free
  | «$update_labels» (input0 : (set labelidx)) : Call free
  | «$update_label» (input0 : idx) : Call free
  | «$free_memtype» (input0 : memtype) : Call free
  | «$free_mem» (input0 : memory) : Call free
  | «$match_numtype» (input0 : (_root_.List deftype)) (input1 : numtype) (input2 : numtype) : Call _root_.Bool
  | «$match_vectype» (input0 : (_root_.List deftype)) (input1 : vectype) (input2 : vectype) : Call _root_.Bool
  | «$match_packtype» (input0 : (_root_.List deftype)) (input1 : packtype) (input2 : packtype) : Call _root_.Bool
  | «$empty_context» : Call context
  | «$stack» (input0 : resulttype) : Call (ellipses × resulttype)
  | «$peek» (input0 : _root_.Nat) (input1 : inferresulttype) : Call valtype
  | «$local» (input0 : context) (input1 : typeidx) : Call localtype
  | «$init_local» (input0 : context) (input1 : typeidx) : Call context
  | «$init_locals» (input0 : context) (input1 : (_root_.List typeidx)) : Call context
  | «$init_valtypes» (input0 : inferresulttype) (input1 : _root_.Nat) (input2 : _root_.Nat) : Call (_root_.List valtype)
  | Numtype_ok (input0 : context) (input1 : numtype) : Call _root_.Unit
  | Vectype_ok (input0 : context) (input1 : vectype) : Call _root_.Unit
  | Limits_ok (input0 : context) (input1 : range) (input2 : limits) : Call _root_.Unit
  | «Instr_ok:br_table:iter:3» (input0 : context) (input1 : (_root_.List idx)) : Call _root_.Unit
  | «$check_lane_index» (input0 : (_root_.List _root_.Nat)) : Call _root_.Bool
  | «Funcbody_ok:rule:iter:2» (input0 : (_root_.List valtype)) : Call (_root_.List localtype)
  | «$numtype_of_addrtype» (input0 : addrtype) : Call numtype
  | Memtype_ok (input0 : context) (input1 : memtype) : Call _root_.Unit
  | Vstoreop_ok (input0 : context) (input1 : vstoreop_) : Call vectype
  | Mem_ok (input0 : context) (input1 : memory) : Call context
  | Mems_ok (input0 : context) (input1 : (_root_.List memory)) : Call context
  | «$free_catch» (input0 : «catch») : Call free
  | «$push» (input0 : context) (input1 : (ellipses × resulttype)) (input2 : (ellipses × resulttype)) : Call (ellipses × resulttype)
  | «$free_exportdesc» (input0 : exportdesc) : Call free
  | «$free_export» (input0 : «export») : Call free
  | Export_ok (input0 : context) (input1 : nameset) (input2 : «export») : Call nameset
  | Exports_ok (input0 : context) (input1 : nameset) (input2 : (_root_.List «export»)) : Call nameset
  | «$type_externop» (input0 : externop_) : Call (heaptype × heaptype)
  | «$is_const» (input0 : context) (input1 : instr) : Call _root_.Bool
  | «Const_ok:rule:iter:0» (input0 : context) (input1 : (_root_.List instr)) : Call _root_.Unit
  | «$type_lane» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) : Call numtype
  | «$type_vec_lane» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) : Call numtype
  | «$lane_extractop» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) : Call _root_.Int
  | «$lane_replaceop» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) : Call _root_.Int
  | «$num_lanes» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) : Call _root_.Int
  | «$diff_reftype» (input0 : reftype) (input1 : reftype) : Call reftype
  | «$match_null» (input0 : null) (input1 : null) : Call _root_.Bool
  | «$type_num» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) : Call numtype
  | «$type_cvtop» (input0 : cvtop_) : Call (numtype × numtype)
  | «$check_uop_extends» (input0 : unop_) : Call _root_.Bool
  | «$pack_size» (input0 : packtype) : Call _root_.Int
  | Pack_ok (input0 : _root_.Int) (input1 : packtype) : Call _root_.Unit
  | Unop_ok (input0 : unop_) : Call _root_.Unit
  | Loadop_ok (input0 : context) (input1 : loadop_) : Call numtype
  | Storeop_ok (input0 : context) (input1 : storeop_) : Call numtype
  | Vloadop_ok (input0 : context) (input1 : vloadop_) : Call vectype
  | Vlaneop_ok (input0 : context) (input1 : vlaneop_) : Call vectype
  | «$unpacked_storage_type» (input0 : storagetype) : Call valtype
  | «$unpacked_field_type» (input0 : fieldtype) : Call valtype
  | «$is_packed_storage_type» (input0 : storagetype) : Call _root_.Bool
  | «Instr_ok:struct.new.explicit:iter:1» (input0 : (_root_.List fieldtype)) : Call (_root_.List valtype)
  | «$functype_of_strtype» (input0 : strtype) : Call functype
  | «$abs_of_str_type» (input0 : strtype) : Call heaptype
  | «$s_unroll» (input0 : typevar) (input1 : rectype) : Call heaptype
  | «$s_roll» (input0 : typevar) (input1 : (typeidx × typeidx)) : Call heaptype
  | «$free_typevar» (input0 : typevar) : Call free
  | «$subst_of» (input0 : typevar) (input1 : (_root_.List deftype)) : Call heaptype
  | «$is_num_type» (input0 : valtype) : Call _root_.Bool
  | «$peek_ref» (input0 : _root_.Nat) (input1 : inferresulttype) : Call reftype
  | «$is_vec_type» (input0 : valtype) : Call _root_.Bool
  | «$defaultable» (input0 : valtype) : Call _root_.Bool
  | «Instr_ok:struct.new.implicit:iter:1» (input0 : (_root_.List fieldtype)) : Call _root_.Unit
  | «$check_vbop_shuffle» (input0 : vbinop_) : Call _root_.Bool
  | Vecbinop_ok (input0 : vbinop_) : Call _root_.Unit
  | «$subst_heaptype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : heaptype) : Call heaptype
  | «$subst_subtype:case_1:iter:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List heaptype)) : Call (_root_.List heaptype)
  | «$subst_reftype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : reftype) : Call reftype
  | «$subst_valtype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : valtype) : Call valtype
  | «$subst_resulttype:case_1:iter:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List valtype)) : Call (_root_.List valtype)
  | «$subst_resulttype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : resulttype) : Call resulttype
  | «$subst_functype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : functype) : Call functype
  | «$subst_storagetype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : storagetype) : Call storagetype
  | «$subst_fieldtype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : fieldtype) : Call fieldtype
  | «$subst_structtype:case_1:iter:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List fieldtype)) : Call (_root_.List fieldtype)
  | «$subst_structtype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : structtype) : Call structtype
  | «$subst_arraytype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : arraytype) : Call arraytype
  | «$subst_strtype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : strtype) : Call strtype
  | «$subst_subtype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : subtype) : Call subtype
  | «$subst_rectype:case_1:iter:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List subtype)) : Call (_root_.List subtype)
  | «$subst_rectype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : rectype) : Call rectype
  | «$subst_deftype» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : deftype) : Call deftype
  | «$rollrt» (input0 : typeidx) (input1 : rectype) : Call rectype
  | «$unrollrt» (input0 : rectype) : Call rectype
  | «$rolldt» (input0 : typeidx) (input1 : rectype) : Call (_root_.List deftype)
  | «$unrolldt» (input0 : deftype) : Call subtype
  | «$expanddt» (input0 : deftype) : Call strtype
  | «$free_heaptype» (input0 : heaptype) : Call free
  | «$free_reftype» (input0 : reftype) : Call free
  | «$free_valtype» (input0 : valtype) : Call free
  | «$free_functype» (input0 : functype) : Call free
  | «$free_storagetype» (input0 : storagetype) : Call free
  | «$free_fieldtype» (input0 : fieldtype) : Call free
  | «$free_structtype» (input0 : structtype) : Call free
  | «$free_arraytype» (input0 : arraytype) : Call free
  | «$free_strtype» (input0 : strtype) : Call free
  | «$free_subtype» (input0 : subtype) : Call free
  | «$free_rectype» (input0 : rectype) : Call free
  | «$free_type_» (input0 : type) : Call free
  | «$free_globaltype» (input0 : globaltype) : Call free
  | «$free_blocktype» (input0 : blocktype) : Call free
  | «$free_instr» (input0 : instr) : Call free
  | «$free_block» (input0 : (_root_.List instr)) : Call free
  | «$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» (input0 : (_root_.List instr)) : Call free
  | «$free_const» (input0 : const) : Call free
  | «$free_global» (input0 : global) : Call free
  | «$free_tabletype» (input0 : tabletype) : Call free
  | «$free_table» (input0 : table) : Call free
  | «$free_elemmode» (input0 : ((set tableidx) → (Call free))) (input1 : elemmode) : Call free
  | «$free_elem» (input0 : elem) : Call free
  | «$free_datamode» (input0 : ((set memidx) → (Call free))) (input1 : datamode) : Call free
  | «$free_data» (input0 : data) : Call free
  | «$free_importdesc» (input0 : importdesc) : Call free
  | «$free_import» (input0 : «import») : Call free
  | «$free_module» (input0 : module) : Call free
  | «$match_deftype» (input0 : (_root_.List deftype)) (input1 : deftype) (input2 : deftype) : Call _root_.Bool
  | «$match_heaptype» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : Call _root_.Bool
  | «$match_heaptype_exists» (input0 : (_root_.List deftype)) (input1 : (_root_.List heaptype)) (input2 : deftype) : Call _root_.Bool
  | «$match_reftype» (input0 : (_root_.List deftype)) (input1 : reftype) (input2 : reftype) : Call _root_.Bool
  | «$match_valtype» (input0 : (_root_.List deftype)) (input1 : valtype) (input2 : valtype) : Call _root_.Bool
  | «$match_storagetype» (input0 : (_root_.List deftype)) (input1 : storagetype) (input2 : storagetype) : Call _root_.Bool
  | «$match_fieldtype» (input0 : (_root_.List deftype)) (input1 : fieldtype) (input2 : fieldtype) : Call _root_.Bool
  | «$match_arraytype» (input0 : (_root_.List deftype)) (input1 : arraytype) (input2 : arraytype) : Call _root_.Bool
  | «$match_structtype:case_1:iter:0» (input0 : (_root_.List deftype)) (input1 : (_root_.List fieldtype)) (input2 : (_root_.List fieldtype)) : Call _root_.Unit
  | «$match_structtype» (input0 : (_root_.List deftype)) (input1 : structtype) (input2 : structtype) : Call _root_.Bool
  | «$match_resulttype:case_1:iter:0» (input0 : (_root_.List deftype)) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) : Call _root_.Unit
  | «$match_resulttype» (input0 : (_root_.List deftype)) (input1 : resulttype) (input2 : resulttype) : Call _root_.Bool
  | «$match_functype» (input0 : (_root_.List deftype)) (input1 : functype) (input2 : functype) : Call _root_.Bool
  | «$match_strtype» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) : Call _root_.Bool
  | «$top_of_str_type» (input0 : (_root_.List deftype)) (input1 : strtype) : Call heaptype
  | «$top_of_heap_type» (input0 : (_root_.List deftype)) (input1 : heaptype) : Call heaptype
  | «Match_resulttype:rule:iter:0» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) : Call _root_.Unit
  | Match_resulttype (input0 : context) (input1 : resulttype) (input2 : resulttype) : Call _root_.Unit
  | «$pop» (input0 : context) (input1 : (ellipses × resulttype)) (input2 : (ellipses × resulttype)) : Call (ellipses × resulttype)
  | Heaptype_ok (input0 : context) (input1 : heaptype) : Call _root_.Unit
  | Reftype_ok (input0 : context) (input1 : reftype) : Call _root_.Unit
  | Valtype_ok (input0 : context) (input1 : valtype) : Call _root_.Unit
  | «Resulttype_ok:rule:iter:0» (input0 : context) (input1 : (_root_.List valtype)) : Call _root_.Unit
  | Resulttype_ok (input0 : context) (input1 : resulttype) : Call _root_.Unit
  | Functype_ok (input0 : context) (input1 : functype) : Call _root_.Unit
  | «Subtype_ok:rule:iter:0» (input0 : context) (input1 : (_root_.List heaptype)) : Call _root_.Unit
  | Storagetype_ok (input0 : context) (input1 : storagetype) : Call _root_.Unit
  | Fieldtype_ok (input0 : context) (input1 : fieldtype) : Call _root_.Unit
  | «Structtype_ok:rule:iter:0» (input0 : context) (input1 : (_root_.List fieldtype)) : Call _root_.Unit
  | Structtype_ok (input0 : context) (input1 : structtype) : Call _root_.Unit
  | Arraytype_ok (input0 : context) (input1 : arraytype) : Call _root_.Unit
  | Strtype_ok (input0 : context) (input1 : strtype) : Call _root_.Unit
  | Subtype_ok (input0 : context) (input1 : subtype) : Call _root_.Unit
  | Subtype_sub_ok' (input0 : context) (input1 : typeidx) (input2 : strtype) (input3 : heaptype) : Call _root_.Unit
  | «Subtype_sub_ok:rule:iter:0» (input0 : context) (input1 : idx) (input2 : strtype) (input3 : (_root_.List heaptype)) : Call _root_.Unit
  | Subtype_sub_ok (input0 : context) (input1 : typeidx) (input2 : subtype) : Call _root_.Unit
  | «Rectype_ok:rule:iter:2» (input0 : context) (input1 : (_root_.List deftype)) : Call (_root_.List deftype)
  | «Rectype_ok:rule:iter:5» (input0 : context) (input1 : (_root_.List subtype)) : Call _root_.Unit
  | «Rectype_ok:rule:iter:6» (input0 : context) (input1 : idx) (input2 : (_root_.List n)) (input3 : (_root_.List subtype)) : Call _root_.Unit
  | Rectype_ok (input0 : context) (input1 : rectype) : Call context
  | Globaltype_ok (input0 : context) (input1 : globaltype) : Call _root_.Unit
  | Tagtype_ok (input0 : context) (input1 : tagtype) : Call _root_.Unit
  | Tabletype_ok (input0 : context) (input1 : tabletype) : Call _root_.Unit
  | «$array_type» (input0 : context) (input1 : typeidx) : Call arraytype
  | «$struct_type» (input0 : context) (input1 : typeidx) : Call structtype
  | «$func_type» (input0 : context) (input1 : typeidx) : Call functype
  | Blocktype_ok (input0 : context) (input1 : blocktype) : Call instrtype
  | Catch_ok (input0 : context) (input1 : resulttype) (input2 : «catch») : Call _root_.Unit
  | «Instr_ok:br_table:iter:4» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List idx)) : Call _root_.Unit
  | «Instr_ok:try_table:iter:0» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List «catch»)) : Call _root_.Unit
  | Instrs_ok (input0 : context) (input1 : inferresulttype) (input2 : (_root_.List instr)) : Call (inferresulttype × (_root_.List idx))
  | Instr_ok (input0 : context) (input1 : inferresulttype) (input2 : instr) : Call inferinstrtype
  | Block_ok (input0 : context) (input1 : instrtype) (input2 : const) : Call _root_.Unit
  | Type_ok (input0 : context) (input1 : type) : Call context
  | Types_ok (input0 : context) (input1 : (_root_.List type)) : Call context
  | Import_ok (input0 : context) (input1 : «import») : Call context
  | Imports_ok (input0 : context) (input1 : (_root_.List «import»)) : Call context
  | Func_ok (input0 : context) (input1 : func) : Call context
  | Funcs_ok (input0 : context) (input1 : (_root_.List func)) : Call context
  | Tag_ok (input0 : context) (input1 : tag) : Call context
  | Tags_ok (input0 : context) (input1 : (_root_.List tag)) : Call context
  | Start_ok (input0 : context) (input1 : (_root_.Option start)) : Call _root_.Unit
  | Const_ok (input0 : context) (input1 : valtype) (input2 : const) : Call _root_.Unit
  | Table_ok (input0 : context) (input1 : table) : Call context
  | Tables_ok (input0 : context) (input1 : (_root_.List table)) : Call context
  | Global_ok (input0 : context) (input1 : global) : Call context
  | Globals_ok (input0 : context) (input1 : (_root_.List global)) : Call context
  | «Elem_ok:rule:iter:0» (input0 : context) (input1 : reftype) (input2 : (_root_.List const)) : Call _root_.Unit
  | Elemmode_ok (input0 : context) (input1 : reftype) (input2 : elemmode) : Call _root_.Unit
  | Elem_ok (input0 : context) (input1 : elem) : Call context
  | Elems_ok (input0 : context) (input1 : (_root_.List elem)) : Call context
  | Datamode_ok (input0 : context) (input1 : datamode) : Call _root_.Unit
  | Data_ok (input0 : context) (input1 : data) : Call context
  | Datas_ok (input0 : context) (input1 : (_root_.List data)) : Call context
  | Local_ok (input0 : context) (input1 : «local») : Call localtype
  | «Funcbody_ok:rule:iter:1» (input0 : context) (input1 : (_root_.List «local»)) : Call (_root_.List localtype)
  | Funcbody_ok (input0 : context) (input1 : func) : Call _root_.Unit
  | «Module_ok:rule:iter:2» (input0 : context) (input1 : (_root_.List func)) : Call _root_.Unit
  | Module_ok (input0 : module) : Call _root_.Unit
noncomputable def toOriginal {α : Type} : Call α → SpecTecCall α
  | @Call.«$min_» input0 input1 => @SpecTecCall.«$min_» input0 input1
  | @Call.«$rev_» X input0 => @SpecTecCall.«$rev_» X input0
  | @Call.«$make_» X_T input0 input1 => @SpecTecCall.«$make_» X_T input0 input1
  | @Call.«$empty_set» K => @SpecTecCall.«$empty_set» K
  | @Call.«$in_set» K_T eq_K_T input0 input1 => @SpecTecCall.«$in_set» K_T eq_K_T input0 input1
  | @Call.«$map_set» X Y compare_Y input0 input1 => @SpecTecCall.«$map_set» X Y compare_Y (fun a0 => toOriginal (input0 a0)) input1
  | @Call.«$range» input0 => @SpecTecCall.«$range» input0
  | @Call.«$rolldt'» input0 input1 => @SpecTecCall.«$rolldt'» input0 input1
  | @Call.«$min_addrtype» input0 input1 => @SpecTecCall.«$min_addrtype» input0 input1
  | @Call.«$num_size» input0 => @SpecTecCall.«$num_size» input0
  | @Call.«$vec_size» input0 => @SpecTecCall.«$vec_size» input0
  | @Call.«$type_vecop» A input0 => @SpecTecCall.«$type_vecop» A input0
  | @Call.«$free_empty»  => @SpecTecCall.«$free_empty» 
  | @Call.«$fold_left» X_T Y input0 input1 input2 => @SpecTecCall.«$fold_left» X_T Y (fun a0 a1 => toOriginal (input0 a0 a1)) input1 input2
  | @Call.«$free_union» input0 input1 => @SpecTecCall.«$free_union» input0 input1
  | @Call.«$free_unions» input0 => @SpecTecCall.«$free_unions» input0
  | @Call.«$add_minus_one» input0 => @SpecTecCall.«$add_minus_one» input0
  | @Call.«$free_idx» input0 => @SpecTecCall.«$free_idx» input0
  | @Call.«$free_shift» input0 => @SpecTecCall.«$free_shift» input0
  | @Call.«$free_list» X input0 input1 => @SpecTecCall.«$free_list» X (fun a0 => toOriginal (input0 a0)) input1
  | @Call.«$free_opt» X_T input0 input1 => @SpecTecCall.«$free_opt» X_T (fun a0 => toOriginal (input0 a0)) input1
  | @Call.«$free_packtype» input0 => @SpecTecCall.«$free_packtype» input0
  | @Call.«$free_numtype» input0 => @SpecTecCall.«$free_numtype» input0
  | @Call.«$free_vectype» input0 => @SpecTecCall.«$free_vectype» input0
  | @Call.«$update_types» input0 => @SpecTecCall.«$update_types» input0
  | @Call.«$update_globals» input0 => @SpecTecCall.«$update_globals» input0
  | @Call.«$update_tables» input0 => @SpecTecCall.«$update_tables» input0
  | @Call.«$update_mems» input0 => @SpecTecCall.«$update_mems» input0
  | @Call.«$update_tags» input0 => @SpecTecCall.«$update_tags» input0
  | @Call.«$update_funcs» input0 => @SpecTecCall.«$update_funcs» input0
  | @Call.«$free_start» input0 => @SpecTecCall.«$free_start» input0
  | @Call.«$update_elems» input0 => @SpecTecCall.«$update_elems» input0
  | @Call.«$update_datas» input0 => @SpecTecCall.«$update_datas» input0
  | @Call.«$update_locals» input0 => @SpecTecCall.«$update_locals» input0
  | @Call.«$update_labels» input0 => @SpecTecCall.«$update_labels» input0
  | @Call.«$update_label» input0 => @SpecTecCall.«$update_label» input0
  | @Call.«$free_memtype» input0 => @SpecTecCall.«$free_memtype» input0
  | @Call.«$free_mem» input0 => @SpecTecCall.«$free_mem» input0
  | @Call.«$match_numtype» input0 input1 input2 => @SpecTecCall.«$match_numtype» input0 input1 input2
  | @Call.«$match_vectype» input0 input1 input2 => @SpecTecCall.«$match_vectype» input0 input1 input2
  | @Call.«$match_packtype» input0 input1 input2 => @SpecTecCall.«$match_packtype» input0 input1 input2
  | @Call.«$empty_context»  => @SpecTecCall.«$empty_context» 
  | @Call.«$stack» input0 => @SpecTecCall.«$stack» input0
  | @Call.«$peek» input0 input1 => @SpecTecCall.«$peek» input0 input1
  | @Call.«$local» input0 input1 => @SpecTecCall.«$local» input0 input1
  | @Call.«$init_local» input0 input1 => @SpecTecCall.«$init_local» input0 input1
  | @Call.«$init_locals» input0 input1 => @SpecTecCall.«$init_locals» input0 input1
  | @Call.«$init_valtypes» input0 input1 input2 => @SpecTecCall.«$init_valtypes» input0 input1 input2
  | @Call.Numtype_ok input0 input1 => @SpecTecCall.Numtype_ok input0 input1
  | @Call.Vectype_ok input0 input1 => @SpecTecCall.Vectype_ok input0 input1
  | @Call.Limits_ok input0 input1 input2 => @SpecTecCall.Limits_ok input0 input1 input2
  | @Call.«Instr_ok:br_table:iter:3» input0 input1 => @SpecTecCall.«Instr_ok:br_table:iter:3» input0 input1
  | @Call.«$check_lane_index» input0 => @SpecTecCall.«$check_lane_index» input0
  | @Call.«Funcbody_ok:rule:iter:2» input0 => @SpecTecCall.«Funcbody_ok:rule:iter:2» input0
  | @Call.«$numtype_of_addrtype» input0 => @SpecTecCall.«$numtype_of_addrtype» input0
  | @Call.Memtype_ok input0 input1 => @SpecTecCall.Memtype_ok input0 input1
  | @Call.Vstoreop_ok input0 input1 => @SpecTecCall.Vstoreop_ok input0 input1
  | @Call.Mem_ok input0 input1 => @SpecTecCall.Mem_ok input0 input1
  | @Call.Mems_ok input0 input1 => @SpecTecCall.Mems_ok input0 input1
  | @Call.«$free_catch» input0 => @SpecTecCall.«$free_catch» input0
  | @Call.«$push» input0 input1 input2 => @SpecTecCall.«$push» input0 input1 input2
  | @Call.«$free_exportdesc» input0 => @SpecTecCall.«$free_exportdesc» input0
  | @Call.«$free_export» input0 => @SpecTecCall.«$free_export» input0
  | @Call.Export_ok input0 input1 input2 => @SpecTecCall.Export_ok input0 input1 input2
  | @Call.Exports_ok input0 input1 input2 => @SpecTecCall.Exports_ok input0 input1 input2
  | @Call.«$type_externop» input0 => @SpecTecCall.«$type_externop» input0
  | @Call.«$is_const» input0 input1 => @SpecTecCall.«$is_const» input0 input1
  | @Call.«Const_ok:rule:iter:0» input0 input1 => @SpecTecCall.«Const_ok:rule:iter:0» input0 input1
  | @Call.«$type_lane» A B C D E F input0 => @SpecTecCall.«$type_lane» A B C D E F input0
  | @Call.«$type_vec_lane» A_T B_T C_T D_T E_T F_T input0 => @SpecTecCall.«$type_vec_lane» A_T B_T C_T D_T E_T F_T input0
  | @Call.«$lane_extractop» input0 => @SpecTecCall.«$lane_extractop» input0
  | @Call.«$lane_replaceop» input0 => @SpecTecCall.«$lane_replaceop» input0
  | @Call.«$num_lanes» A B C D E F input0 => @SpecTecCall.«$num_lanes» A B C D E F input0
  | @Call.«$diff_reftype» input0 input1 => @SpecTecCall.«$diff_reftype» input0 input1
  | @Call.«$match_null» input0 input1 => @SpecTecCall.«$match_null» input0 input1
  | @Call.«$type_num» A_T B_T C_T D_T input0 => @SpecTecCall.«$type_num» A_T B_T C_T D_T input0
  | @Call.«$type_cvtop» input0 => @SpecTecCall.«$type_cvtop» input0
  | @Call.«$check_uop_extends» input0 => @SpecTecCall.«$check_uop_extends» input0
  | @Call.«$pack_size» input0 => @SpecTecCall.«$pack_size» input0
  | @Call.Pack_ok input0 input1 => @SpecTecCall.Pack_ok input0 input1
  | @Call.Unop_ok input0 => @SpecTecCall.Unop_ok input0
  | @Call.Loadop_ok input0 input1 => @SpecTecCall.Loadop_ok input0 input1
  | @Call.Storeop_ok input0 input1 => @SpecTecCall.Storeop_ok input0 input1
  | @Call.Vloadop_ok input0 input1 => @SpecTecCall.Vloadop_ok input0 input1
  | @Call.Vlaneop_ok input0 input1 => @SpecTecCall.Vlaneop_ok input0 input1
  | @Call.«$unpacked_storage_type» input0 => @SpecTecCall.«$unpacked_storage_type» input0
  | @Call.«$unpacked_field_type» input0 => @SpecTecCall.«$unpacked_field_type» input0
  | @Call.«$is_packed_storage_type» input0 => @SpecTecCall.«$is_packed_storage_type» input0
  | @Call.«Instr_ok:struct.new.explicit:iter:1» input0 => @SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» input0
  | @Call.«$functype_of_strtype» input0 => @SpecTecCall.«$functype_of_strtype» input0
  | @Call.«$abs_of_str_type» input0 => @SpecTecCall.«$abs_of_str_type» input0
  | @Call.«$s_unroll» input0 input1 => @SpecTecCall.«$s_unroll» input0 input1
  | @Call.«$s_roll» input0 input1 => @SpecTecCall.«$s_roll» input0 input1
  | @Call.«$free_typevar» input0 => @SpecTecCall.«$free_typevar» input0
  | @Call.«$subst_of» input0 input1 => @SpecTecCall.«$subst_of» input0 input1
  | @Call.«$is_num_type» input0 => @SpecTecCall.«$is_num_type» input0
  | @Call.«$peek_ref» input0 input1 => @SpecTecCall.«$peek_ref» input0 input1
  | @Call.«$is_vec_type» input0 => @SpecTecCall.«$is_vec_type» input0
  | @Call.«$defaultable» input0 => @SpecTecCall.«$defaultable» input0
  | @Call.«Instr_ok:struct.new.implicit:iter:1» input0 => @SpecTecCall.«Instr_ok:struct.new.implicit:iter:1» input0
  | @Call.«$check_vbop_shuffle» input0 => @SpecTecCall.«$check_vbop_shuffle» input0
  | @Call.Vecbinop_ok input0 => @SpecTecCall.Vecbinop_ok input0
  | @Call.«$subst_heaptype» X_T input0 input1 input2 => @SpecTecCall.«$subst_heaptype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_subtype:case_1:iter:0» X_T input0 input1 input2 => @SpecTecCall.«$subst_subtype:case_1:iter:0» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_reftype» X_T input0 input1 input2 => @SpecTecCall.«$subst_reftype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_valtype» X_T input0 input1 input2 => @SpecTecCall.«$subst_valtype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_resulttype:case_1:iter:0» X_T input0 input1 input2 => @SpecTecCall.«$subst_resulttype:case_1:iter:0» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_resulttype» X_T input0 input1 input2 => @SpecTecCall.«$subst_resulttype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_functype» X_T input0 input1 input2 => @SpecTecCall.«$subst_functype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_storagetype» X_T input0 input1 input2 => @SpecTecCall.«$subst_storagetype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_fieldtype» X_T input0 input1 input2 => @SpecTecCall.«$subst_fieldtype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_structtype:case_1:iter:0» X_T input0 input1 input2 => @SpecTecCall.«$subst_structtype:case_1:iter:0» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_structtype» X_T input0 input1 input2 => @SpecTecCall.«$subst_structtype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_arraytype» X_T input0 input1 input2 => @SpecTecCall.«$subst_arraytype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_strtype» X_T input0 input1 input2 => @SpecTecCall.«$subst_strtype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_subtype» X_T input0 input1 input2 => @SpecTecCall.«$subst_subtype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_rectype:case_1:iter:0» X_T input0 input1 input2 => @SpecTecCall.«$subst_rectype:case_1:iter:0» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_rectype» X_T input0 input1 input2 => @SpecTecCall.«$subst_rectype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$subst_deftype» X_T input0 input1 input2 => @SpecTecCall.«$subst_deftype» X_T input0 (fun a0 a1 => toOriginal (input1 a0 a1)) input2
  | @Call.«$rollrt» input0 input1 => @SpecTecCall.«$rollrt» input0 input1
  | @Call.«$unrollrt» input0 => @SpecTecCall.«$unrollrt» input0
  | @Call.«$rolldt» input0 input1 => @SpecTecCall.«$rolldt» input0 input1
  | @Call.«$unrolldt» input0 => @SpecTecCall.«$unrolldt» input0
  | @Call.«$expanddt» input0 => @SpecTecCall.«$expanddt» input0
  | @Call.«$free_heaptype» input0 => @SpecTecCall.«$free_heaptype» input0
  | @Call.«$free_reftype» input0 => @SpecTecCall.«$free_reftype» input0
  | @Call.«$free_valtype» input0 => @SpecTecCall.«$free_valtype» input0
  | @Call.«$free_functype» input0 => @SpecTecCall.«$free_functype» input0
  | @Call.«$free_storagetype» input0 => @SpecTecCall.«$free_storagetype» input0
  | @Call.«$free_fieldtype» input0 => @SpecTecCall.«$free_fieldtype» input0
  | @Call.«$free_structtype» input0 => @SpecTecCall.«$free_structtype» input0
  | @Call.«$free_arraytype» input0 => @SpecTecCall.«$free_arraytype» input0
  | @Call.«$free_strtype» input0 => @SpecTecCall.«$free_strtype» input0
  | @Call.«$free_subtype» input0 => @SpecTecCall.«$free_subtype» input0
  | @Call.«$free_rectype» input0 => @SpecTecCall.«$free_rectype» input0
  | @Call.«$free_type_» input0 => @SpecTecCall.«$free_type_» input0
  | @Call.«$free_globaltype» input0 => @SpecTecCall.«$free_globaltype» input0
  | @Call.«$free_blocktype» input0 => @SpecTecCall.«$free_blocktype» input0
  | @Call.«$free_instr» input0 => @SpecTecCall.«$free_instr» input0
  | @Call.«$free_block» input0 => @SpecTecCall.«$free_block» input0
  | @Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» input0 => @SpecTecCall.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» input0
  | @Call.«$free_const» input0 => @SpecTecCall.«$free_const» input0
  | @Call.«$free_global» input0 => @SpecTecCall.«$free_global» input0
  | @Call.«$free_tabletype» input0 => @SpecTecCall.«$free_tabletype» input0
  | @Call.«$free_table» input0 => @SpecTecCall.«$free_table» input0
  | @Call.«$free_elemmode» input0 input1 => @SpecTecCall.«$free_elemmode» (fun a0 => toOriginal (input0 a0)) input1
  | @Call.«$free_elem» input0 => @SpecTecCall.«$free_elem» input0
  | @Call.«$free_datamode» input0 input1 => @SpecTecCall.«$free_datamode» (fun a0 => toOriginal (input0 a0)) input1
  | @Call.«$free_data» input0 => @SpecTecCall.«$free_data» input0
  | @Call.«$free_importdesc» input0 => @SpecTecCall.«$free_importdesc» input0
  | @Call.«$free_import» input0 => @SpecTecCall.«$free_import» input0
  | @Call.«$free_module» input0 => @SpecTecCall.«$free_module» input0
  | @Call.«$match_deftype» input0 input1 input2 => @SpecTecCall.«$match_deftype» input0 input1 input2
  | @Call.«$match_heaptype» input0 input1 input2 => @SpecTecCall.«$match_heaptype» input0 input1 input2
  | @Call.«$match_heaptype_exists» input0 input1 input2 => @SpecTecCall.«$match_heaptype_exists» input0 input1 input2
  | @Call.«$match_reftype» input0 input1 input2 => @SpecTecCall.«$match_reftype» input0 input1 input2
  | @Call.«$match_valtype» input0 input1 input2 => @SpecTecCall.«$match_valtype» input0 input1 input2
  | @Call.«$match_storagetype» input0 input1 input2 => @SpecTecCall.«$match_storagetype» input0 input1 input2
  | @Call.«$match_fieldtype» input0 input1 input2 => @SpecTecCall.«$match_fieldtype» input0 input1 input2
  | @Call.«$match_arraytype» input0 input1 input2 => @SpecTecCall.«$match_arraytype» input0 input1 input2
  | @Call.«$match_structtype:case_1:iter:0» input0 input1 input2 => @SpecTecCall.«$match_structtype:case_1:iter:0» input0 input1 input2
  | @Call.«$match_structtype» input0 input1 input2 => @SpecTecCall.«$match_structtype» input0 input1 input2
  | @Call.«$match_resulttype:case_1:iter:0» input0 input1 input2 => @SpecTecCall.«$match_resulttype:case_1:iter:0» input0 input1 input2
  | @Call.«$match_resulttype» input0 input1 input2 => @SpecTecCall.«$match_resulttype» input0 input1 input2
  | @Call.«$match_functype» input0 input1 input2 => @SpecTecCall.«$match_functype» input0 input1 input2
  | @Call.«$match_strtype» input0 input1 input2 => @SpecTecCall.«$match_strtype» input0 input1 input2
  | @Call.«$top_of_str_type» input0 input1 => @SpecTecCall.«$top_of_str_type» input0 input1
  | @Call.«$top_of_heap_type» input0 input1 => @SpecTecCall.«$top_of_heap_type» input0 input1
  | @Call.«Match_resulttype:rule:iter:0» input0 input1 input2 => @SpecTecCall.«Match_resulttype:rule:iter:0» input0 input1 input2
  | @Call.Match_resulttype input0 input1 input2 => @SpecTecCall.Match_resulttype input0 input1 input2
  | @Call.«$pop» input0 input1 input2 => @SpecTecCall.«$pop» input0 input1 input2
  | @Call.Heaptype_ok input0 input1 => @SpecTecCall.Heaptype_ok input0 input1
  | @Call.Reftype_ok input0 input1 => @SpecTecCall.Reftype_ok input0 input1
  | @Call.Valtype_ok input0 input1 => @SpecTecCall.Valtype_ok input0 input1
  | @Call.«Resulttype_ok:rule:iter:0» input0 input1 => @SpecTecCall.«Resulttype_ok:rule:iter:0» input0 input1
  | @Call.Resulttype_ok input0 input1 => @SpecTecCall.Resulttype_ok input0 input1
  | @Call.Functype_ok input0 input1 => @SpecTecCall.Functype_ok input0 input1
  | @Call.«Subtype_ok:rule:iter:0» input0 input1 => @SpecTecCall.«Subtype_ok:rule:iter:0» input0 input1
  | @Call.Storagetype_ok input0 input1 => @SpecTecCall.Storagetype_ok input0 input1
  | @Call.Fieldtype_ok input0 input1 => @SpecTecCall.Fieldtype_ok input0 input1
  | @Call.«Structtype_ok:rule:iter:0» input0 input1 => @SpecTecCall.«Structtype_ok:rule:iter:0» input0 input1
  | @Call.Structtype_ok input0 input1 => @SpecTecCall.Structtype_ok input0 input1
  | @Call.Arraytype_ok input0 input1 => @SpecTecCall.Arraytype_ok input0 input1
  | @Call.Strtype_ok input0 input1 => @SpecTecCall.Strtype_ok input0 input1
  | @Call.Subtype_ok input0 input1 => @SpecTecCall.Subtype_ok input0 input1
  | @Call.Subtype_sub_ok' input0 input1 input2 input3 => @SpecTecCall.Subtype_sub_ok' input0 input1 input2 input3
  | @Call.«Subtype_sub_ok:rule:iter:0» input0 input1 input2 input3 => @SpecTecCall.«Subtype_sub_ok:rule:iter:0» input0 input1 input2 input3
  | @Call.Subtype_sub_ok input0 input1 input2 => @SpecTecCall.Subtype_sub_ok input0 input1 input2
  | @Call.«Rectype_ok:rule:iter:2» input0 input1 => @SpecTecCall.«Rectype_ok:rule:iter:2» input0 input1
  | @Call.«Rectype_ok:rule:iter:5» input0 input1 => @SpecTecCall.«Rectype_ok:rule:iter:5» input0 input1
  | @Call.«Rectype_ok:rule:iter:6» input0 input1 input2 input3 => @SpecTecCall.«Rectype_ok:rule:iter:6» input0 input1 input2 input3
  | @Call.Rectype_ok input0 input1 => @SpecTecCall.Rectype_ok input0 input1
  | @Call.Globaltype_ok input0 input1 => @SpecTecCall.Globaltype_ok input0 input1
  | @Call.Tagtype_ok input0 input1 => @SpecTecCall.Tagtype_ok input0 input1
  | @Call.Tabletype_ok input0 input1 => @SpecTecCall.Tabletype_ok input0 input1
  | @Call.«$array_type» input0 input1 => @SpecTecCall.«$array_type» input0 input1
  | @Call.«$struct_type» input0 input1 => @SpecTecCall.«$struct_type» input0 input1
  | @Call.«$func_type» input0 input1 => @SpecTecCall.«$func_type» input0 input1
  | @Call.Blocktype_ok input0 input1 => @SpecTecCall.Blocktype_ok input0 input1
  | @Call.Catch_ok input0 input1 input2 => @SpecTecCall.Catch_ok input0 input1 input2
  | @Call.«Instr_ok:br_table:iter:4» input0 input1 input2 => @SpecTecCall.«Instr_ok:br_table:iter:4» input0 input1 input2
  | @Call.«Instr_ok:try_table:iter:0» input0 input1 input2 => @SpecTecCall.«Instr_ok:try_table:iter:0» input0 input1 input2
  | @Call.Instrs_ok input0 input1 input2 => @SpecTecCall.Instrs_ok input0 input1 input2
  | @Call.Instr_ok input0 input1 input2 => @SpecTecCall.Instr_ok input0 input1 input2
  | @Call.Block_ok input0 input1 input2 => @SpecTecCall.Block_ok input0 input1 input2
  | @Call.Type_ok input0 input1 => @SpecTecCall.Type_ok input0 input1
  | @Call.Types_ok input0 input1 => @SpecTecCall.Types_ok input0 input1
  | @Call.Import_ok input0 input1 => @SpecTecCall.Import_ok input0 input1
  | @Call.Imports_ok input0 input1 => @SpecTecCall.Imports_ok input0 input1
  | @Call.Func_ok input0 input1 => @SpecTecCall.Func_ok input0 input1
  | @Call.Funcs_ok input0 input1 => @SpecTecCall.Funcs_ok input0 input1
  | @Call.Tag_ok input0 input1 => @SpecTecCall.Tag_ok input0 input1
  | @Call.Tags_ok input0 input1 => @SpecTecCall.Tags_ok input0 input1
  | @Call.Start_ok input0 input1 => @SpecTecCall.Start_ok input0 input1
  | @Call.Const_ok input0 input1 input2 => @SpecTecCall.Const_ok input0 input1 input2
  | @Call.Table_ok input0 input1 => @SpecTecCall.Table_ok input0 input1
  | @Call.Tables_ok input0 input1 => @SpecTecCall.Tables_ok input0 input1
  | @Call.Global_ok input0 input1 => @SpecTecCall.Global_ok input0 input1
  | @Call.Globals_ok input0 input1 => @SpecTecCall.Globals_ok input0 input1
  | @Call.«Elem_ok:rule:iter:0» input0 input1 input2 => @SpecTecCall.«Elem_ok:rule:iter:0» input0 input1 input2
  | @Call.Elemmode_ok input0 input1 input2 => @SpecTecCall.Elemmode_ok input0 input1 input2
  | @Call.Elem_ok input0 input1 => @SpecTecCall.Elem_ok input0 input1
  | @Call.Elems_ok input0 input1 => @SpecTecCall.Elems_ok input0 input1
  | @Call.Datamode_ok input0 input1 => @SpecTecCall.Datamode_ok input0 input1
  | @Call.Data_ok input0 input1 => @SpecTecCall.Data_ok input0 input1
  | @Call.Datas_ok input0 input1 => @SpecTecCall.Datas_ok input0 input1
  | @Call.Local_ok input0 input1 => @SpecTecCall.Local_ok input0 input1
  | @Call.«Funcbody_ok:rule:iter:1» input0 input1 => @SpecTecCall.«Funcbody_ok:rule:iter:1» input0 input1
  | @Call.Funcbody_ok input0 input1 => @SpecTecCall.Funcbody_ok input0 input1
  | @Call.«Module_ok:rule:iter:2» input0 input1 => @SpecTecCall.«Module_ok:rule:iter:2» input0 input1
  | @Call.Module_ok input0 => @SpecTecCall.Module_ok input0
end properties.wasm_module_ok.PositiveRuntime
