import properties.wasm_module_ok.UnrollInterface
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ArrayTypeDecision

def arrayTypeResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.arraytype :=
  match c.TYPES[x]? with
  | none => none
  | some dt =>
      match UnrollInterface.expandResult dt with
      | some (.DefArrayT arr) => some arr
      | _ => none

theorem array_type_success_iff
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (arr : SpecTec.arraytype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$array_type» c x⟩)
      n (.success (.of arr)) finalSupply ↔
    ∃ dt : SpecTec.deftype,
      c.TYPES[x]? = some dt ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.strtype,
          SpecTec.Call.«$expanddt» dt⟩)
        n (.success (.of (SpecTec.strtype.DefArrayT arr))) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«$array_type:clause:0» c x)
          (fun _ => .unmatch))
        n (.success (.of arr)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«$array_type:clause:0» at hclause
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
                rename_i middle strt
                cases htail with
                | bind_success hshape htail =>
                  cases hshape with
                  | guard_true hcond =>
                    cases strt with
                    | DefFuncT _ =>
                      simp [SpecTec.«exec:match:strtype:DefArrayT»] at hcond
                    | DefStructT _ =>
                      simp [SpecTec.«exec:match:strtype:DefArrayT»] at hcond
                    | DefArrayT arr' =>
                      cases htail with
                      | pure => exact ⟨dt, rfl, hexpand⟩
      | orElse_unmatch hfailedSupply hlast => restore_supply hfailedSupply at hlast; cases hlast
  · rintro ⟨dt, hget, hexpand⟩
    have hindex : x < c.TYPES.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$array_type_clauses» c x))
      n (.success (.of arr)) finalSupply
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$array_type:clause:0» c x)
      n (.success (.of arr)) finalSupply
    unfold SpecTec.«$array_type:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hindex
    · rw [hget]
      apply SpecTecExecution.Eval.bind_success hexpand
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure arr

theorem array_type_success_iff_result
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (arr : SpecTec.arraytype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$array_type» c x⟩)
      n (.success (.of arr)) finalSupply ↔
    arrayTypeResult c x = some arr ∧ finalSupply = n := by
  rw [array_type_success_iff]
  constructor
  · rintro ⟨dt, hget, hexpand⟩
    obtain ⟨hresult, hsupply⟩ :=
      (UnrollInterface.expanddt_success_iff_result
        dt (.DefArrayT arr) n finalSupply).1 hexpand
    exact ⟨by simp [arrayTypeResult, hget, hresult], hsupply⟩
  · rintro ⟨hresult, hsupply⟩
    cases hget : c.TYPES[x]? with
    | none => simp [arrayTypeResult, hget] at hresult
    | some dt =>
      cases hexp : UnrollInterface.expandResult dt with
      | none => simp [arrayTypeResult, hget, hexp] at hresult
      | some st =>
        cases st with
        | DefFuncT _ =>
          simp [arrayTypeResult, hget, hexp] at hresult
        | DefStructT _ =>
          simp [arrayTypeResult, hget, hexp] at hresult
        | DefArrayT actual =>
          have heq : actual = arr := by
            simpa [arrayTypeResult, hget, hexp] using hresult
          subst actual
          exact ⟨dt, rfl,
            (UnrollInterface.expanddt_success_iff_result
              dt (.DefArrayT arr) n finalSupply).2
                ⟨hexp, hsupply⟩⟩

end properties.wasm_module_ok.ArrayTypeDecision
