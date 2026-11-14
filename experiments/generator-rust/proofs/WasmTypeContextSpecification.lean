import WasmGroundEvaluation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace RustWasm
open GroundEvaluation

def typeContextEmptyModule : SpecTec.module :=
  { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], TAGS := [],
    START := none, ELEMS := [], DATAS := [], IMPORTS := [], EXPORTS := [] }

def typeContextIndexedRef (index : Nat) : SpecTec.valtype :=
  .RefT (.«% %» .Null (.VarHT (.StatX index)))

def typeContextVoidType : SpecTec.subtype := .SubT .Final [] (.DefFuncT (.FuncT [] []))

def recursiveParentModule : SpecTec.module :=
  { typeContextEmptyModule with TYPES := [.RecT
      [.SubT .NoFinal [] (.DefFuncT (.FuncT [typeContextIndexedRef 0] [])),
       .SubT .Final [.VarHT (.StatX 0)] (.DefFuncT (.FuncT [typeContextIndexedRef 0] []))]] }

def mutualGroupModule : SpecTec.module :=
  { typeContextEmptyModule with TYPES := [.RecT
      [.SubT .Final [] (.DefFuncT (.FuncT [typeContextIndexedRef 1] [])),
       .SubT .Final [] (.DefFuncT (.FuncT [typeContextIndexedRef 0] []))]] }

def rawAliasModule : SpecTec.module :=
  { typeContextEmptyModule with
    TYPES := [.RecT [typeContextVoidType], .RecT [typeContextVoidType],
      .RecT [.SubT .Final [] (.DefFuncT (.FuncT [typeContextIndexedRef 0] [typeContextIndexedRef 1]))]]
    FUNCS := [⟨2, [], [.«LOCAL.GET» 0]⟩] }

def exportedRefModule : SpecTec.module :=
  { typeContextEmptyModule with
    TYPES := [.RecT [typeContextVoidType]]
    FUNCS := [⟨0, [], [.«REF.FUNC» 0, .DROP]⟩]
    EXPORTS := [⟨[101, 48], .FuncExport 0⟩] }

theorem recursive_parent_module_ok : SpecTec.Module_ok recursiveParentModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

theorem mutual_group_module_ok : SpecTec.Module_ok mutualGroupModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

theorem raw_alias_module_ok : SpecTec.Module_ok rawAliasModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

theorem exported_ref_module_ok : SpecTec.Module_ok exportedRefModule := by
  refine ⟨0, ?_⟩
  ground_spec_run

end RustWasm
