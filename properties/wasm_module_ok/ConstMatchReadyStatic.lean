import properties.wasm_module_ok.CandidateProvenanceElemDataFuncs
import properties.wasm_module_ok.LocalInitStatic

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstMatchReadyStatic

/-- Local initialization changes only local state, so the established matcher
type table remains ready. -/
theorem init_locals_ready
    (c d : SpecTec.context) (indices : List SpecTec.idx)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c indices⟩)
      start (.success (.of d)) finish)
    (hready : CandidateTypeReady.Ready c) :
    CandidateTypeReady.Ready d := by
  exact CandidateProvenanceElemDataFuncs.ready_of_types_eq c d
    (LocalInitStatic.init_locals_static_fields c d indices
      start finish hcall).1 hready

/-- The same static type-table equality preserves heap membership for an
individual stack value. -/
theorem init_locals_in_table_val
    (c d : SpecTec.context) (indices : List SpecTec.idx)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c indices⟩)
      start (.success (.of d)) finish)
    (t : SpecTec.valtype)
    (h : CandidateValMatch.InTableVal c t) :
    CandidateValMatch.InTableVal d t := by
  exact CandidateProvenanceSteps.in_table_val_of_types_eq c d t
    (LocalInitStatic.init_locals_static_fields c d indices
      start finish hcall).1 h

end properties.wasm_module_ok.ConstMatchReadyStatic
