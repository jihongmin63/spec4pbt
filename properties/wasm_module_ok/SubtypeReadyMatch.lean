import properties.wasm_module_ok.ReadyStructuralMatch

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeReadyMatch

theorem static_subtype_sub_ok_success_of_match
    (c : SpecTec.context) (x y : SpecTec.typeidx)
    (strt strtU : SpecTec.strtype) (dt : SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype) (n : Nat)
    (hlookup : c.TYPES[y]? = some dt)
    (hunroll : properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
      some (.SubT fin hts strtU))
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype» c.TYPES strt strtU⟩)
      n (.success (.of true)) n)
    (hlt : y < x) (hfin : fin = .NoFinal) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok' c x strt
          (.VarHT (.StatX y))⟩)
      n (.success (.of ())) n := by
  have hy : y < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  have hunrollEval :=
    (UnrollInterface.unrolldt_success_iff dt
      (.SubT fin hts strtU) n n).2 ⟨hunroll, rfl⟩
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.Subtype_sub_ok'_clauses c x strt (.VarHT (.StatX y))) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Subtype_sub_ok':clause:0» c x strt (.VarHT (.StatX y)))
    n (.success (.of ())) n
  unfold SpecTec.«Subtype_sub_ok':clause:0»
  simp only [SpecTec.«sub:heaptype:heaptypeVar»,
    SpecTec.«Subtype_sub_ok':rule:downcast:0»,
    SpecTec.«exec:match:typevar:StatX»]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true trivial
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true trivial
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true hy
      · simp only [hlookup]
        apply SpecTecExecution.Eval.bind_success
        · exact hunrollEval
        · apply SpecTecExecution.Eval.bind_success
          · exact hmatch
          · exact SpecTecExecution.Eval.bind_success
              (SpecTecExecution.Eval.guard_true (by simp [hlt, hfin]))
              (SpecTecExecution.Eval.pure ())

theorem static_subtype_sub_ok_unmatch_of_guard_false
    (c : SpecTec.context) (x y : SpecTec.typeidx)
    (strt strtU : SpecTec.strtype) (dt : SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (result : Bool) (n : Nat)
    (hlookup : c.TYPES[y]? = some dt)
    (hunroll : properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
      some (.SubT fin hts strtU))
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype» c.TYPES strt strtU⟩)
      n (.success (.of result)) n)
    (hguard : ¬ ((y < x ∧ fin = .NoFinal) ∧ result = true)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok' c x strt
          (.VarHT (.StatX y))⟩)
      n .unmatch n := by
  have hy : y < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  have hunrollEval :=
    (UnrollInterface.unrolldt_success_iff dt
      (.SubT fin hts strtU) n n).2 ⟨hunroll, rfl⟩
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.Subtype_sub_ok'_clauses c x strt (.VarHT (.StatX y))) ())
    n .unmatch n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_sub_ok':clause:0» c x strt (.VarHT (.StatX y)))
      n .unmatch n
    unfold SpecTec.«Subtype_sub_ok':clause:0»
    simp only [SpecTec.«sub:heaptype:heaptypeVar»,
      SpecTec.«Subtype_sub_ok':rule:downcast:0»,
      SpecTec.«exec:match:typevar:StatX»]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true trivial
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true trivial
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hy
        · simp only [hlookup]
          apply SpecTecExecution.Eval.bind_success
          · exact hunrollEval
          · apply SpecTecExecution.Eval.bind_success
            · exact hmatch
            · exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false hguard)
  · exact SpecTecExecution.firstSuccess_nil () n

theorem static_subtype_sub_ok_total_of_ready
    (c : SpecTec.context) (x y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish n : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_ok c
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[y]? = some dt) :
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ result : Bool,
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT fin hts strtU) ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.Subtype_sub_ok' c x strt
            (.VarHT (.StatX y))⟩)
        n (if (y < x ∧ fin = .NoFinal) ∧ result = true then
          .success (.of ()) else .unmatch) n := by
  classical
  obtain ⟨fin, hts, strtU, hunroll, result, hmatch⟩ :=
    ReadyStructuralMatch.static_structural_match_total
      c y sourceFin sourceHts strt dt subStart subFinish n
      hsub hnested hready hlookup
  refine ⟨fin, hts, strtU, result, hunroll, ?_⟩
  by_cases hg : (y < x ∧ fin = .NoFinal) ∧ result = true
  · simp only [if_pos hg]
    have hr : result = true := hg.2
    subst result
    exact static_subtype_sub_ok_success_of_match
      c x y strt strtU dt fin hts n hlookup hunroll hmatch
      hg.1.1 hg.1.2
  · simp only [if_neg hg]
    exact static_subtype_sub_ok_unmatch_of_guard_false
      c x y strt strtU dt fin hts result n
      hlookup hunroll hmatch hg

end properties.wasm_module_ok.SubtypeReadyMatch
