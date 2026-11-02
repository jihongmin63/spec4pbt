import properties.wasm_module_ok.LocalValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.LocalListValidation

def allLocalsValid (c : SpecTec.context) :
    List SpecTec.«local» → Bool
  | [] => true
  | l :: ls => ValtypeValidation.valtypeValid c l.LTYPE &&
      allLocalsValid c ls

def localTypes (ls : List SpecTec.«local») :
    List SpecTec.localtype :=
  ls.map LocalValidation.localType

theorem local_iter_nil_success (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.localtype,
        SpecTec.Call.«Funcbody_ok:rule:iter:1» c []⟩)
      n (.success (.of ([] : List SpecTec.localtype))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«Funcbody_ok:rule:iter:1_clauses» c []))
    n (.success (.of ([] : List SpecTec.localtype))) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Funcbody_ok:rule:iter:1:clause:0» c [])
    n (.success (.of ([] : List SpecTec.localtype))) n
  exact SpecTecExecution.Eval.pure []

theorem local_iter_cons_success_iff
    (c : SpecTec.context) (l : SpecTec.«local»)
    (ls : List SpecTec.«local»)
    (result : List SpecTec.localtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.localtype,
        SpecTec.Call.«Funcbody_ok:rule:iter:1» c (l :: ls)⟩)
      n (.success (.of result)) finalSupply ↔
    ∃ (lt : SpecTec.localtype) (rest : List SpecTec.localtype)
      (middle : Nat),
      result = lt :: rest ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.localtype, SpecTec.Call.Local_ok c l⟩)
        n (.success (.of lt)) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨List SpecTec.localtype,
          SpecTec.Call.«Funcbody_ok:rule:iter:1» c ls⟩)
        middle (.success (.of rest)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Funcbody_ok:rule:iter:1:clause:0» c (l :: ls))
          (fun _ => SpecTecExecution.tryClauses
            [fun _ => SpecTec.«Funcbody_ok:rule:iter:1:clause:1» c (l :: ls)]))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        change SpecTecExecution.Eval SpecTec.Body
          (.unmatch) n (.success (.of result)) finalSupply at hfirst
        cases hfirst
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Funcbody_ok:rule:iter:1:clause:1» c (l :: ls))
            (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Funcbody_ok:rule:iter:1:clause:1» at hsecond
          cases hsecond with
          | bind_success hlocal htail =>
            rename_i middle lt
            cases htail with
            | bind_success hrest hpure =>
              rename_i rest
              cases hpure with
              | pure => exact ⟨lt, rest, middle, rfl, hlocal, hrest⟩
        | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨lt, rest, middle, rfl, hlocal, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«Funcbody_ok:rule:iter:1_clauses» c (l :: ls)))
      n (.success (.of (lt :: rest))) finalSupply
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Funcbody_ok:rule:iter:1:clause:0» c (l :: ls))
        n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Funcbody_ok:rule:iter:1:clause:1» c (l :: ls))
        n (.success (.of (lt :: rest))) finalSupply
      unfold SpecTec.«Funcbody_ok:rule:iter:1:clause:1»
      apply SpecTecExecution.Eval.bind_success hlocal
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure (lt :: rest)

theorem local_iter_success_iff_valid
    (c : SpecTec.context) (ls : List SpecTec.«local»)
    (result : List SpecTec.localtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.localtype,
        SpecTec.Call.«Funcbody_ok:rule:iter:1» c ls⟩)
      n (.success (.of result)) finalSupply ↔
    allLocalsValid c ls = true ∧
    result = localTypes ls ∧ finalSupply = n := by
  induction ls generalizing result n finalSupply with
  | nil =>
    constructor
    · intro h
      obtain ⟨hout, hsupply⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic h
          (local_iter_nil_success c n)
      cases hout
      exact ⟨rfl, rfl, hsupply⟩
    · rintro ⟨_, hresult, hsupply⟩
      cases hresult
      cases hsupply
      exact local_iter_nil_success c n
  | cons l ls ih =>
    constructor
    · intro h
      obtain ⟨lt, rest, middle, hresult, hlocal, htail⟩ :=
        (local_iter_cons_success_iff c l ls result n finalSupply).1 h
      obtain ⟨hheadValid, hlt, hmiddle⟩ :=
        (LocalValidation.local_success_iff_valid
          c l lt n middle).1 hlocal
      obtain ⟨htailValid, hrest, hsupply⟩ :=
        (ih rest middle finalSupply).1 htail
      subst lt
      subst rest
      subst middle
      subst result
      exact ⟨by simp [allLocalsValid, hheadValid, htailValid],
        rfl, hsupply⟩
    · rintro ⟨hall, hresult, hsupply⟩
      have hparts : ValtypeValidation.valtypeValid c l.LTYPE = true ∧
          allLocalsValid c ls = true := by
        simpa [allLocalsValid] using hall
      obtain ⟨hheadValid, htailValid⟩ := hparts
      cases hresult
      cases hsupply
      apply (local_iter_cons_success_iff c l ls
        (localTypes (l :: ls)) n n).2
      exact ⟨LocalValidation.localType l, localTypes ls,
        n, rfl,
        (LocalValidation.local_success_iff_valid
          c l (LocalValidation.localType l)
          n n).2 ⟨hheadValid, rfl, rfl⟩,
        (ih (localTypes ls) n n).2
          ⟨htailValid, rfl, rfl⟩⟩

end properties.wasm_module_ok.LocalListValidation
