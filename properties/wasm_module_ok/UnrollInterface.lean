import properties.wasm_module_not_ok.UnrolldtValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.UnrollInterface

open properties.wasm_module_not_ok.Rejection

theorem unrolldt_success_iff
    (dt : SpecTec.deftype) (st : SpecTec.subtype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dt⟩)
      n (.success (.of st)) finalSupply ↔
    unrollDeftypeResult dt = some st ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      unrolldt_deterministic dt n finalSupply
        (.success (.of st)) h
    cases hresult : unrollDeftypeResult dt with
    | none =>
      simp [unrollDeftypeOutcome, hresult] at hout
    | some result =>
      simp [unrollDeftypeOutcome, hresult] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hresult, rfl⟩
    simpa [unrollDeftypeOutcome, hresult] using
      unrolldt_total dt finalSupply

def deftypeFunctype (dt : SpecTec.deftype) : Option SpecTec.functype :=
  match unrollDeftypeResult dt with
  | some (.SubT _ _ (.DefFuncT ft)) => some ft
  | _ => none

theorem unroll_functype_success_iff
    (dt : SpecTec.deftype) (ft : SpecTec.functype)
    (n finalSupply : Nat) :
    (∃ (fin : SpecTec.final) (supers : List SpecTec.heaptype),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dt⟩)
        n (.success (.of (SpecTec.subtype.SubT fin supers
          (SpecTec.strtype.DefFuncT ft)))) finalSupply) ↔
    deftypeFunctype dt = some ft ∧ finalSupply = n := by
  constructor
  · rintro ⟨fin, supers, h⟩
    obtain ⟨hresult, hsupply⟩ :=
      (unrolldt_success_iff dt (.SubT fin supers (.DefFuncT ft))
        n finalSupply).1 h
    exact ⟨by simp [deftypeFunctype, hresult], hsupply⟩
  · rintro ⟨hfun, rfl⟩
    cases hresult : unrollDeftypeResult dt with
    | none => simp [deftypeFunctype, hresult] at hfun
    | some st =>
      cases st with
      | SubT fin supers strt =>
        cases strt with
        | DefStructT _ => simp [deftypeFunctype, hresult] at hfun
        | DefArrayT _ => simp [deftypeFunctype, hresult] at hfun
        | DefFuncT ft' =>
          simp [deftypeFunctype, hresult] at hfun
          cases hfun
          exact ⟨fin, supers,
            (unrolldt_success_iff dt
              (.SubT fin supers (.DefFuncT ft))
              finalSupply finalSupply).2 ⟨hresult, rfl⟩⟩

def expandResult (dt : SpecTec.deftype) : Option SpecTec.strtype :=
  match unrollDeftypeResult dt with
  | none => none
  | some (.SubT _ _ st) => some st

def expandOutcome (dt : SpecTec.deftype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match expandResult dt with
  | none => .unmatch
  | some st => .success (.of st)

theorem expanddt_total (dt : SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (expandOutcome dt) n := by
  cases hresult : unrollDeftypeResult dt with
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$expanddt_clauses» dt) ())
      n (expandOutcome dt) n
    simp only [expandOutcome, expandResult, hresult]
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$expanddt:clause:0» dt) n .unmatch n
      unfold SpecTec.«$expanddt:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      simpa [unrollDeftypeOutcome, hresult] using
        unrolldt_total dt n
    · exact SpecTecExecution.firstSuccess_nil () n
  | some subtype =>
    cases subtype with
    | SubT fin supers strt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$expanddt_clauses» dt) ())
        n (expandOutcome dt) n
      simp only [expandOutcome, expandResult, hresult]
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$expanddt:clause:0» dt)
        n (.success (.of strt)) n
      unfold SpecTec.«$expanddt:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · simpa [unrollDeftypeOutcome, hresult] using
          unrolldt_total dt n
      · exact SpecTecExecution.Eval.pure strt

theorem expanddt_deterministic (dt : SpecTec.deftype)
    (n finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n outcome finalSupply) :
    outcome = expandOutcome dt ∧ finalSupply = n := by
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request x y hp
    cases hp
  exact SpecTecExecution.eval_deterministic hdet h
    (expanddt_total dt n)

theorem expanddt_success_iff_result (dt : SpecTec.deftype)
    (st : SpecTec.strtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of st)) finalSupply ↔
    expandResult dt = some st ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      expanddt_deterministic dt n finalSupply _ h
    cases hresult : expandResult dt with
    | none => simp [expandOutcome, hresult] at hout
    | some actual =>
        simp only [expandOutcome, hresult] at hout
        cases hout
        exact ⟨rfl, hsupply⟩
  · rintro ⟨hresult, rfl⟩
    simpa [expandOutcome, hresult] using
      expanddt_total dt finalSupply

end properties.wasm_module_ok.UnrollInterface
