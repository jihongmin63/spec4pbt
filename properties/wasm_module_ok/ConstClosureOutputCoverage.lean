import properties.wasm_module_ok.ConstOutputCoverage
import properties.wasm_module_ok.ConstExternConvertClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstClosureOutputCoverage

theorem covered_mem_step (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (h : ConstOutputCoverage.Covered c s u) :
    u ∈ ConstExternConvertClosure.externClosureStep c s := by
  cases h with
  | basic hbase =>
    have hbasic : u ∈ ConstBasicClosure.basicStep c s :=
      Finset.mem_union_left _ (Finset.mem_union_right _ hbase)
    have hfixed : u ∈ ConstFixedZeroClosure.fixedZeroStep c s :=
      Finset.mem_union_left _ hbasic
    have himplicit : u ∈ ConstStructImplicitClosure.structImplicitStep c s :=
      Finset.mem_union_left _ hfixed
    have hexplicit : u ∈
        ConstStructExplicitClosure.structExplicitClosureStep c s :=
      Finset.mem_union_left _ himplicit
    exact Finset.mem_union_left _ hexplicit
  | structImplicit hstruct =>
    have himplicit : u ∈ ConstStructImplicitClosure.structImplicitStep c s :=
      Finset.mem_union_right _ hstruct
    have hexplicit : u ∈
        ConstStructExplicitClosure.structExplicitClosureStep c s :=
      Finset.mem_union_left _ himplicit
    exact Finset.mem_union_left _ hexplicit
  | array harray =>
    have hfixed : u ∈ ConstFixedZeroClosure.fixedZeroStep c s :=
      Finset.mem_union_right _ harray
    have himplicit : u ∈ ConstStructImplicitClosure.structImplicitStep c s :=
      Finset.mem_union_left _ hfixed
    have hexplicit : u ∈
        ConstStructExplicitClosure.structExplicitClosureStep c s :=
      Finset.mem_union_left _ himplicit
    exact Finset.mem_union_left _ hexplicit
  | i31 hi31 =>
    have hbasic : u ∈ ConstBasicClosure.basicStep c s :=
      Finset.mem_union_right _
        ((ConstI31Production.i31_outputs_mem_iff c s u).2 hi31)
    have hfixed : u ∈ ConstFixedZeroClosure.fixedZeroStep c s :=
      Finset.mem_union_left _ hbasic
    have himplicit : u ∈ ConstStructImplicitClosure.structImplicitStep c s :=
      Finset.mem_union_left _ hfixed
    have hexplicit : u ∈
        ConstStructExplicitClosure.structExplicitClosureStep c s :=
      Finset.mem_union_left _ himplicit
    exact Finset.mem_union_left _ hexplicit
  | structExplicit hstruct =>
    have hexplicit : u ∈
        ConstStructExplicitClosure.structExplicitClosureStep c s :=
      Finset.mem_union_right _
        ((ConstStructExplicitProduction.struct_explicit_outputs_mem_iff
          c s u).2 hstruct)
    exact Finset.mem_union_left _ hexplicit
  | externConvert hextern =>
    exact Finset.mem_union_right _
      ((ConstExternConvertProduction.extern_type_outputs_mem_iff
        c s u).2 hextern)

theorem step_of_is_const
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (i : SpecTec.instr)
    (iit : SpecTec.inferinstrtype) (u : SpecTec.valtype)
    (start middle fin : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt i⟩)
      middle (.success (.of iit)) fin)
    (hinputs : ∀ t ∈ iit.1.INS.2, t ∈ s)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ ConstExternConvertClosure.externClosureStep c s := by
  have hsyntax :=
    (ConstSyntaxClassification.is_const_success_iff
      c i start middle).1 hconst |>.1
  exact covered_mem_step c s u
    (ConstOutputCoverage.covered_of_syntax
      c irt s i iit u middle fin hsyntax hcall hinputs houts)

end properties.wasm_module_ok.ConstClosureOutputCoverage
