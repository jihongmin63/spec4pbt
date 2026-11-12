import properties.wasm_module_ok.UnrollInterface
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.StructTypeDecision

def structTypeResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.structtype :=
  match c.TYPES[x]? with
  | none => none
  | some dt =>
      match UnrollInterface.expandResult dt with
      | some (.DefStructT strct) => some strct
      | _ => none

theorem struct_type_success_iff
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (strct : SpecTec.structtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$struct_type» c x⟩)
      n (.success (.of strct)) finalSupply ↔
    ∃ dt : SpecTec.deftype,
      c.TYPES[x]? = some dt ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.strtype,
          SpecTec.Call.«$expanddt» dt⟩)
        n (.success (.of (SpecTec.strtype.DefStructT strct))) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«$struct_type:clause:0» c x)
          (fun _ => .unmatch))
        n (.success (.of strct)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«$struct_type:clause:0» at hclause
        cases hclause with
        | bind_success hbound htail =>
          cases hbound with
          | guard_true _ =>
            cases hget : c.TYPES[x]? with
            | none =>
              rw [hget] at htail
              cases htail
            | some dt =>
              rw [hget] at htail
              cases htail with
              | bind_success hexpand htail =>
                rename_i middle st
                cases htail with
                | bind_success hshape htail =>
                  cases hshape with
                  | guard_true hcond =>
                    cases st with
                    | DefFuncT _ =>
                      simp [SpecTec.«exec:match:strtype:DefStructT»] at hcond
                    | DefArrayT _ =>
                      simp [SpecTec.«exec:match:strtype:DefStructT»] at hcond
                    | DefStructT actual =>
                      cases htail with
                      | pure => exact ⟨dt, rfl, hexpand⟩
      | orElse_unmatch hfailedSupply hlast => restore_supply hfailedSupply at hlast; cases hlast
  · rintro ⟨dt, hget, hexpand⟩
    have hindex : x < c.TYPES.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$struct_type_clauses» c x))
      n (.success (.of strct)) finalSupply
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$struct_type:clause:0» c x)
      n (.success (.of strct)) finalSupply
    unfold SpecTec.«$struct_type:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hindex
    · rw [hget]
      apply SpecTecExecution.Eval.bind_success hexpand
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure strct

theorem struct_type_success_iff_result
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (strct : SpecTec.structtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$struct_type» c x⟩)
      n (.success (.of strct)) finalSupply ↔
    structTypeResult c x = some strct ∧ finalSupply = n := by
  rw [struct_type_success_iff]
  constructor
  · rintro ⟨dt, hget, hexpand⟩
    obtain ⟨hresult, hsupply⟩ :=
      (UnrollInterface.expanddt_success_iff_result
        dt (.DefStructT strct) n finalSupply).1 hexpand
    exact ⟨by simp [structTypeResult, hget, hresult], hsupply⟩
  · rintro ⟨hresult, hsupply⟩
    cases hget : c.TYPES[x]? with
    | none => simp [structTypeResult, hget] at hresult
    | some dt =>
      cases hexp : UnrollInterface.expandResult dt with
      | none => simp [structTypeResult, hget, hexp] at hresult
      | some st =>
        cases st with
        | DefFuncT _ =>
          simp [structTypeResult, hget, hexp] at hresult
        | DefArrayT _ =>
          simp [structTypeResult, hget, hexp] at hresult
        | DefStructT actual =>
          have heq : actual = strct := by
            simpa [structTypeResult, hget, hexp] using hresult
          subst actual
          exact ⟨dt, rfl,
            (UnrollInterface.expanddt_success_iff_result
              dt (.DefStructT strct) n finalSupply).2
                ⟨hexp, hsupply⟩⟩

end properties.wasm_module_ok.StructTypeDecision
