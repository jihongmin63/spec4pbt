import properties.wasm_module_ok.ReadyHeapMatchReachable
import properties.wasm_module_ok.SubtypeReadyMatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyStaticSubtypeMatch

/-- The static supertype guard computed from the actual unrolled target and
the safe finite heap matcher. -/
def staticSuperMatch (c : SpecTec.context) (x y : SpecTec.typeidx)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype) : Bool :=
  match properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt with
  | none => false
  | some (.SubT fin _ strtU) =>
      decide ((y < x ∧ fin = .NoFinal) ∧
        MatchStrtypeConditional.strMatch
          (fun h1 h2 => (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false)
          strt strtU = true)

theorem static_subtype_sub_ok_result_of_ready
    (c : SpecTec.context) (x y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish n : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[y]? = some dt) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_sub_ok' c x strt
          (.VarHT (.StatX y))⟩)
      n (if staticSuperMatch c x y strt dt = true then
        .success (.of ()) else .unmatch) n := by
  obtain ⟨fin, hts, strtU, hunroll, hmatch⟩ :=
    ReadyHeapMatchReachable.static_structural_match_result
      c y sourceFin sourceHts strt dt subStart subFinish n
      hsub hnested hready hlookup
  let result := MatchStrtypeConditional.strMatch
    (fun h1 h2 => (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false)
    strt strtU
  have hguard : staticSuperMatch c x y strt dt = true ↔
      (y < x ∧ fin = .NoFinal) ∧ result = true := by
    simp [staticSuperMatch, hunroll, result]
  by_cases hg : (y < x ∧ fin = .NoFinal) ∧ result = true
  · have htrue := hguard.mpr hg
    rw [if_pos htrue]
    have hr : MatchStrtypeConditional.strMatch
        (fun h1 h2 => (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false)
        strt strtU = true := by
      simpa [result] using hg.2
    rw [hr] at hmatch
    exact SubtypeReadyMatch.static_subtype_sub_ok_success_of_match
      c x y strt strtU dt fin hts n hlookup hunroll hmatch
      hg.1.1 hg.1.2
  · have hfalse : ¬ staticSuperMatch c x y strt dt = true :=
      fun h => hg (hguard.mp h)
    rw [if_neg hfalse]
    exact SubtypeReadyMatch.static_subtype_sub_ok_unmatch_of_guard_false
      c x y strt strtU dt fin hts result n
      hlookup hunroll hmatch hg

end properties.wasm_module_ok.ReadyStaticSubtypeMatch
