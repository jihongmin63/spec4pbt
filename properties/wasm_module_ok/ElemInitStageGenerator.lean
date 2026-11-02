import properties.wasm_module_ok.ElemInitDecision
import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.ElemInitStageGenerator

def elemInitCorrect (c : SpecTec.context) (rt : SpecTec.reftype) :
    CorrectGen (fun inits : List SpecTec.const =>
      ElemInitDecision.elemInitValid c rt inits = true) :=
  IndexedListStage.correct (ElemInitDecision.elemInitValid c rt)

theorem elemInitCandidates_mono
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (n k : Nat) (inits : List SpecTec.const)
    (h : inits ∈ IndexedListStage.candidates
      (ElemInitDecision.elemInitValid c rt) n) :
    inits ∈ IndexedListStage.candidates
      (ElemInitDecision.elemInitValid c rt) (n + k) :=
  IndexedListStage.candidates_mono
    (ElemInitDecision.elemInitValid c rt) n k inits h

theorem elemInitCorrect_nonempty
    (c : SpecTec.context) (rt : SpecTec.reftype) :
    Gen.support (elemInitCorrect c rt).val [] := by
  rw [(elemInitCorrect c rt).property]
  rfl

theorem elemInitCorrect_sound
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (inits : List SpecTec.const) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htarget : CandidateValMatch.InTableVal c (.RefT rt))
    (hsupport : Gen.support (elemInitCorrect c rt).val inits) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Elem_ok:rule:iter:0»
        c rt inits⟩)
      n (.success (.of ())) n := by
  rw [(elemInitCorrect c rt).property] at hsupport
  exact (ElemInitDecision.elem_init_valid_iff_iter
    c rt inits n n hready hprov hnested htarget).1
    ⟨hsupport, rfl⟩

theorem elemInitCorrect_complete
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (inits : List SpecTec.const) (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htarget : CandidateValMatch.InTableVal c (.RefT rt))
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Elem_ok:rule:iter:0»
        c rt inits⟩)
      start (.success (.of ())) finish) :
    Gen.support (elemInitCorrect c rt).val inits := by
  rw [(elemInitCorrect c rt).property]
  exact ((ElemInitDecision.elem_init_valid_iff_iter
    c rt inits start finish hready hprov hnested htarget).2 hcall).1

def elemInitStage :
    Staged.Stage (SpecTec.context × SpecTec.reftype)
      (List SpecTec.const) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun input inits =>
    ElemInitDecision.elemInitValid input.1 input.2 inits = true
  generate := fun input => (elemInitCorrect input.1 input.2).val
  always := by
    intro input _
    exact ⟨[], rfl, trivial⟩
  sound := by
    intro input inits _ hsupport
    rw [(elemInitCorrect input.1 input.2).property] at hsupport
    exact ⟨hsupport, trivial⟩
  complete := by
    intro input inits _ hvalid _
    rw [(elemInitCorrect input.1 input.2).property]
    exact hvalid

end properties.wasm_module_ok.ElemInitStageGenerator
