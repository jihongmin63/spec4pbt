import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.FuncsValidation
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.FuncHeadersStageGenerator

def headerFunction (x : SpecTec.typeidx) : SpecTec.func :=
  { FTYPE := x, LOCALS := [], BODY := [] }

def headerResult (c : SpecTec.context)
    (xs : List SpecTec.typeidx) : Option SpecTec.context :=
  FuncsValidation.funcsResult c (xs.map headerFunction)

theorem func_decl_header_invariant
    (c : SpecTec.context) (f : SpecTec.func) :
    FuncDeclValidation.funcDeclResult c f =
      FuncDeclValidation.funcDeclResult c
        (headerFunction f.FTYPE) := by
  rfl

theorem funcs_header_invariant
    (c : SpecTec.context) (fs : List SpecTec.func) :
    FuncsValidation.funcsResult c fs =
      headerResult c (fs.map (·.FTYPE)) := by
  induction fs generalizing c with
  | nil => rfl
  | cons f fs ih =>
      simp only [headerResult, List.map_cons,
        FuncsValidation.funcsResult]
      rw [func_decl_header_invariant]
      cases h : FuncDeclValidation.funcDeclResult c
          (headerFunction f.FTYPE) with
      | none => rfl
      | some c₁ => exact ih c₁

theorem funcs_success_iff_header_result
    (c : SpecTec.context) (fs : List SpecTec.func)
    (out : SpecTec.context) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Funcs_ok c fs⟩)
      n (.success (.of out)) finalSupply ↔
      headerResult c (fs.map (·.FTYPE)) = some out ∧
        finalSupply = n := by
  rw [FuncsValidation.funcs_success_iff_result]
  rw [funcs_header_invariant]

def headersValid (c : SpecTec.context)
    (xs : List SpecTec.typeidx) : Bool :=
  (headerResult c xs).isSome

def headersCorrect (c : SpecTec.context) :
    CorrectGen (fun xs : List SpecTec.typeidx =>
      headersValid c xs = true) :=
  IndexedListStage.correct (headersValid c)

theorem headersCorrect_nonempty (c : SpecTec.context) :
    Gen.support (headersCorrect c).val [] := by
  rw [(headersCorrect c).property]
  rfl

theorem headersCandidates_mono
    (c : SpecTec.context) (n k : Nat)
    (xs : List SpecTec.typeidx)
    (h : xs ∈ IndexedListStage.candidates (headersValid c) n) :
    xs ∈ IndexedListStage.candidates (headersValid c) (n + k) :=
  IndexedListStage.candidates_mono (headersValid c) n k xs h

theorem headersCorrect_sound
    (c : SpecTec.context) (xs : List SpecTec.typeidx)
    (h : Gen.support (headersCorrect c).val xs) :
    ∃ out : SpecTec.context,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context,
          SpecTec.Call.Funcs_ok c
            (xs.map headerFunction)⟩)
        0 (.success (.of out)) 0 := by
  rw [(headersCorrect c).property] at h
  cases hr : headerResult c xs with
  | none => simp [headersValid, hr] at h
  | some out =>
      refine ⟨out, ?_⟩
      exact (FuncsValidation.funcs_success_iff_result
        c (xs.map headerFunction) out 0 0).2
          ⟨hr, rfl⟩

theorem headersCorrect_complete
    (c : SpecTec.context) (fs : List SpecTec.func)
    (out : SpecTec.context) (n finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Funcs_ok c fs⟩)
      n (.success (.of out)) finalSupply) :
    Gen.support (headersCorrect c).val
      (fs.map (·.FTYPE)) := by
  have hr := (funcs_success_iff_header_result
    c fs out n finalSupply).1 h
  rw [(headersCorrect c).property]
  simp [headersValid, hr.1]

def headersStage : Staged.Stage SpecTec.context
    (List SpecTec.typeidx) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c xs => headersValid c xs = true
  generate := fun c => (headersCorrect c).val
  always := by
    intro c _
    exact ⟨[], rfl, trivial⟩
  sound := by
    intro c xs _ h
    rw [(headersCorrect c).property] at h
    exact ⟨h, trivial⟩
  complete := by
    intro c xs _ hv _
    rw [(headersCorrect c).property]
    exact hv

def headersStateGen (c : SpecTec.context) :
    Gen (List SpecTec.typeidx × SpecTec.context) :=
  (headersCorrect c).val >>= fun xs =>
    pure (xs, (headerResult c xs).getD c)

theorem headersState_support_iff
    (c : SpecTec.context) (xs : List SpecTec.typeidx)
    (out : SpecTec.context) :
    Gen.support (headersStateGen c) (xs, out) ↔
      headerResult c xs = some out := by
  simp only [headersStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    rw [(headersCorrect c).property] at hchosen
    cases hr : headerResult c chosen with
    | none => simp [headersValid, hr] at hchosen
    | some result =>
        simp only [hr, Option.getD_some] at hpure
        cases hpure
        exact hr
  · intro hr
    refine ⟨xs, ?_, ?_⟩
    · rw [(headersCorrect c).property]
      simp [headersValid, hr]
    · simp [hr]

def headersStateStage :
    Staged.Stage SpecTec.context
      (List SpecTec.typeidx × SpecTec.context) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c output =>
    headerResult c output.1 = some output.2
  generate := headersStateGen
  always := by
    intro c _
    exact ⟨([], c), rfl, trivial⟩
  sound := by
    intro c output _ h
    exact ⟨(headersState_support_iff c output.1 output.2).1 h, trivial⟩
  complete := by
    intro c output _ hv _
    exact (headersState_support_iff c output.1 output.2).2 hv

end properties.wasm_module_ok.FuncHeadersStageGenerator
