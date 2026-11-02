import properties.wasm_module_ok.ConstructiveModuleModeRules
import properties.wasm_module_ok.ConstructiveModuleRefsBounds
import properties.wasm_module_ok.ConstructivePreludeRefs
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleModeRefs
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs ConstructiveBodyEvalReduction

abbrev Available (refs : SpecTec.free) (xs : List instr) :=
  ∀x,instr.«REF.FUNC» x∈xs → FreeUnionValidation.HasFunc refs x
abbrev DataAvailable (refs : SpecTec.free) : datamode → Prop
  | .Passive => True | .Active a => Available refs a.OFFSET
abbrev ElemAvailable (refs : SpecTec.free) : elemmode → Prop
  | .Passive | .Declarative => True | .Active a => Available refs a.OFFSET

theorem data_replace (refs : SpecTec.free) (c : context) (mode : datamode) (n finish : Nat)
    (ha : DataAvailable refs mode)
    (h : Eval Body (.call ⟨Unit,Call.Datamode_ok c mode⟩) n (.success (.of ())) finish) :
    Eval Body (.call ⟨Unit,Call.Datamode_ok (replace refs c) mode⟩) n (.success (.of ())) finish := by
  cases mode with
  | Passive =>
    have hn := (properties.wasm_module_ok.Execution.eval_deterministic h (ConstructiveModuleModeRules.data_passive c n)).2
    subst finish;exact ConstructiveModuleModeRules.data_passive _ n
  | Active a =>
    obtain ⟨addr,lim,hx,hc⟩ := ConstructiveModuleModeRules.data_active_original c a n finish h
    exact ConstructiveModuleModeRules.data_active (replace refs c) a addr lim hx n finish
      (ConstructiveRefs.const_ok_replace_refs c refs _ a.OFFSET n finish ha hc)

theorem elem_replace (refs : SpecTec.free) (c : context) (rt : reftype) (mode : elemmode) (n finish : Nat)
    (ha : ElemAvailable refs mode)
    (h : Eval Body (.call ⟨Unit,Call.Elemmode_ok c rt mode⟩) n (.success (.of ())) finish) :
    Eval Body (.call ⟨Unit,Call.Elemmode_ok (replace refs c) rt mode⟩) n (.success (.of ())) finish := by
  cases mode with
  | Passive =>
    have hn := (ElemModeBaseDecision.passive_success_iff c rt n finish).1 h
    subst finish;exact ElemModeBaseDecision.passive_total _ rt n
  | Declarative =>
    have hn := (ElemModeBaseDecision.declarative_success_iff c rt n finish).1 h
    subst finish;exact ElemModeBaseDecision.declarative_total _ rt n
  | Active a =>
    cases h with | call h =>
      obtain ⟨_,hs⟩ := (tryClauses_success_iff (SpecTec.Elemmode_ok_clauses c rt (.Active a)) n (.of ()) finish).1 h
      cases hs with
      | here h =>
        unfold SpecTec.«Elemmode_ok:clause:0» at h
        obtain ⟨hg,_⟩ := (bind_guard _ _ _ _ _).1 h
        cases hg
      | next _ hs => cases hs with
        | here h =>
          unfold SpecTec.«Elemmode_ok:clause:1» at h
          obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
          obtain ⟨hb,h⟩ := (bind_guard _ _ _ _ _).1 h
          cases hx : c.TABLES[a.INDEX]? with
          | none => rw [hx] at h;cases h
          | some tt =>
            rw [hx] at h
            cases tt with | TableT addr lim tr =>
              cases h with | bind_success hmatch h =>
                rename_i n1 matched
                obtain ⟨hm,h⟩ := (bind_guard _ _ _ _ _).1 h
                cases h with | bind_success hnum h =>
                  rename_i n2 nt
                  cases h with | bind_success hc hp =>
                    cases hp
                    apply Eval.call
                    change Eval Body (tryClauses (SpecTec.Elemmode_ok_clauses (replace refs c) rt (.Active a))) n _ finish
                    apply tryClauses_cons_unmatch
                    · unfold SpecTec.«Elemmode_ok:clause:0»
                      exact Eval.bind_unmatch (Eval.guard_false (by simp [SpecTec.«exec:match:elemmode:Passive»]))
                    apply tryClauses_cons_success
                    unfold SpecTec.«Elemmode_ok:clause:1»
                    apply Eval.bind_success (Eval.guard_true rfl)
                    apply Eval.bind_success (Eval.guard_true hb)
                    rw [show (replace refs c).TABLES[a.INDEX]?=some (.TableT addr lim tr) from hx]
                    apply Eval.bind_success hmatch
                    apply Eval.bind_success (Eval.guard_true hm)
                    apply Eval.bind_success hnum
                    apply Eval.bind_success (ConstructiveRefs.const_ok_replace_refs c refs (.NumT nt) a.OFFSET n2 finish ha hc)
                    exact Eval.pure _
        | next _ hs => cases hs with
          | here h =>
            unfold SpecTec.«Elemmode_ok:clause:2» at h
            obtain ⟨hg,_⟩ := (bind_guard _ _ _ _ _).1 h
            cases hg
          | next _ hs => cases hs
#print axioms elem_replace
#print axioms data_replace
end properties.wasm_module_ok.ConstructiveModuleModeRefs
