import properties.wasm_module_ok.MatchSpecialBaseTotal
import properties.wasm_module_ok.CandidateTypeReady
import properties.wasm_module_ok.UnrollInterface

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchReadyDefFixed

theorem ready_indexed_expanddt_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    ∃ strt : SpecTec.strtype,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
        n (.success (.of strt)) n := by
  have hq : q < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  obtain ⟨dt', fin, hts, strt, hget, hunroll, _⟩ :=
    hready.unrolledPredecessors q hq
  have heq : dt' = dt := Option.some.inj (hget.symm.trans hlookup)
  subst dt'
  refine ⟨strt, ?_⟩
  simpa [UnrollInterface.expandOutcome, UnrollInterface.expandResult,
    hunroll] using UnrollInterface.expanddt_total dt n

theorem ready_indexed_expandResult_some
    (c : SpecTec.context) (q : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    ∃ strt : SpecTec.strtype,
      UnrollInterface.expandResult dt = some strt := by
  have hq : q < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  obtain ⟨dt', fin, hts, strt, hget, hunroll, _⟩ :=
    hready.unrolledPredecessors q hq
  have heq : dt' = dt := Option.some.inj (hget.symm.trans hlookup)
  subst dt'
  exact ⟨strt, by simp [UnrollInterface.expandResult, hunroll]⟩

theorem def_clause9_unmatch_of_target
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype) (target : SpecTec.heaptype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n)
    (htarget : target ≠ .AnyHT ∧ target ≠ .EqHT ∧
      target ≠ .StructHT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts (.DefHT dt) target)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:9»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · cases strt with
      | DefStructT fields =>
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by
            simp [SpecTec.«exec:match:strtype:DefStructT»])
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by
              simp [htarget.1, htarget.2.1, htarget.2.2]))
      | DefArrayT field =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefStructT»]))
      | DefFuncT ft =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefStructT»]))

theorem def_clause10_unmatch_of_target
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype) (target : SpecTec.heaptype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n)
    (htarget : target ≠ .AnyHT ∧ target ≠ .EqHT ∧
      target ≠ .ArrayHT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts (.DefHT dt) target)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:10»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · cases strt with
      | DefArrayT field =>
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by
            simp [SpecTec.«exec:match:strtype:DefArrayT»])
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by
              simp [htarget.1, htarget.2.1, htarget.2.2]))
      | DefStructT fields =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefArrayT»]))
      | DefFuncT ft =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefArrayT»]))

theorem def_clause11_unmatch_of_target
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype) (n : Nat)
    (htarget : SpecTec.«exec:match:heaptype:FuncHT» target = false) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» dts (.DefHT dt) target)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:11»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [htarget]))

theorem def_clause11_func_success
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (ft : SpecTec.functype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of (SpecTec.strtype.DefFuncT ft))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» dts (.DefHT dt) .FuncHT)
      n (.success (.of true)) n := by
  unfold SpecTec.«$match_heaptype:clause:11»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:FuncHT»])
    · apply SpecTecExecution.Eval.bind_success
      · exact hexpand
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by
            simp [SpecTec.«exec:match:strtype:DefFuncT»])
        · exact SpecTecExecution.Eval.pure true

theorem def_clause11_nonfunc_unmatch
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n)
    (hnonfunc : ∀ ft, strt ≠ .DefFuncT ft) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» dts (.DefHT dt) .FuncHT)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:11»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:FuncHT»])
    · apply SpecTecExecution.Eval.bind_success
      · exact hexpand
      · cases strt with
        | DefStructT fields =>
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by
              simp [SpecTec.«exec:match:strtype:DefFuncT»]))
        | DefArrayT field =>
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by
              simp [SpecTec.«exec:match:strtype:DefFuncT»]))
        | DefFuncT ft =>
          exact False.elim (hnonfunc ft rfl)

theorem def_clause9_struct_any_success
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (fields : SpecTec.structtype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of (SpecTec.strtype.DefStructT fields))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts (.DefHT dt) .AnyHT)
      n (.success (.of true)) n := by
  unfold SpecTec.«$match_heaptype:clause:9»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by
          simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by decide)
        · exact SpecTecExecution.Eval.pure true

theorem def_clause9_nonstruct_any_unmatch
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n)
    (hnonstruct : ∀ fields, strt ≠ .DefStructT fields) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts (.DefHT dt) .AnyHT)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:9»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · cases strt with
      | DefStructT fields => exact False.elim (hnonstruct fields rfl)
      | DefArrayT field =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefStructT»]))
      | DefFuncT ft =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefStructT»]))

theorem def_clause9_nonstruct_unmatch
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype) (target : SpecTec.heaptype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n)
    (hnonstruct : ∀ fields, strt ≠ .DefStructT fields) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts (.DefHT dt) target)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:9»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · cases strt with
      | DefStructT fields => exact False.elim (hnonstruct fields rfl)
      | DefArrayT field =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefStructT»]))
      | DefFuncT ft =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefStructT»]))

theorem def_clause10_array_any_success
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (field : SpecTec.arraytype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of (SpecTec.strtype.DefArrayT field))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts (.DefHT dt) .AnyHT)
      n (.success (.of true)) n := by
  unfold SpecTec.«$match_heaptype:clause:10»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by
          simp [SpecTec.«exec:match:strtype:DefArrayT»])
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by decide)
        · exact SpecTecExecution.Eval.pure true

theorem def_clause9_struct_class_success
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (fields : SpecTec.structtype) (target : SpecTec.heaptype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of (SpecTec.strtype.DefStructT fields))) n)
    (htarget : target = .AnyHT ∨ target = .EqHT ∨
      target = .StructHT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts (.DefHT dt) target)
      n (.success (.of true)) n := by
  unfold SpecTec.«$match_heaptype:clause:9»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by
          simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by
            rcases htarget with rfl | rfl | rfl <;> decide)
        · exact SpecTecExecution.Eval.pure true

theorem def_clause10_array_class_success
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (field : SpecTec.arraytype) (target : SpecTec.heaptype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of (SpecTec.strtype.DefArrayT field))) n)
    (htarget : target = .AnyHT ∨ target = .EqHT ∨
      target = .ArrayHT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts (.DefHT dt) target)
      n (.success (.of true)) n := by
  unfold SpecTec.«$match_heaptype:clause:10»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by
          simp [SpecTec.«exec:match:strtype:DefArrayT»])
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by
            rcases htarget with rfl | rfl | rfl <;> decide)
        · exact SpecTecExecution.Eval.pure true

theorem def_clause10_nonarray_any_unmatch
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n)
    (hnonarray : ∀ field, strt ≠ .DefArrayT field) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts (.DefHT dt) .AnyHT)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:10»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · cases strt with
      | DefArrayT field => exact False.elim (hnonarray field rfl)
      | DefStructT fields =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefArrayT»]))
      | DefFuncT ft =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefArrayT»]))

theorem def_clause10_nonarray_unmatch
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype) (target : SpecTec.heaptype) (n : Nat)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n)
    (hnonarray : ∀ field, strt ≠ .DefArrayT field) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts (.DefHT dt) target)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:10»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by
      simp [SpecTec.«exec:match:heaptype:DefHT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact hexpand
    · cases strt with
      | DefArrayT field => exact False.elim (hnonarray field rfl)
      | DefStructT fields =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefArrayT»]))
      | DefFuncT ft =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefArrayT»]))

def nonstructuralBaseTargets : List SpecTec.heaptype :=
  [.I31HT, .NoneHT, .NoFuncHT, .NoExnHT,
    .NoExternHT, .BotHT, .ExnHT, .ExternHT]

theorem ready_def_nonstructural_base_false
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (htarget : target ∈ nonstructuralBaseTargets) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) target⟩)
      n (.success (.of false)) n := by
  obtain ⟨strt, hexpand⟩ :=
    ready_indexed_expanddt_total c q n dt hready hlookup
  have hcases : target = .I31HT ∨ target = .NoneHT ∨
      target = .NoFuncHT ∨ target = .NoExnHT ∨
      target = .NoExternHT ∨ target = .BotHT ∨
      target = .ExnHT ∨ target = .ExternHT := by
    simpa [nonstructuralBaseTargets] using htarget
  have h9 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» c.TYPES (.DefHT dt) target)
      n .unmatch n :=
    def_clause9_unmatch_of_target c.TYPES dt strt target n hexpand (by
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide)
  have h10 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» c.TYPES (.DefHT dt) target)
      n .unmatch n :=
    def_clause10_unmatch_of_target c.TYPES dt strt target n hexpand (by
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide)
  have h11 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» c.TYPES (.DefHT dt) target)
      n .unmatch n :=
    def_clause11_unmatch_of_target c.TYPES dt target n (by
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [SpecTec.«exec:match:heaptype:FuncHT»])
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» c.TYPES (.DefHT dt) target) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [SpecTec.«exec:match:heaptype:EqHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoneHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp [SpecTec.«exec:match:heaptype:DefHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h9
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h10
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h11
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:BotHT»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) target)
    n (.success (.of false)) n
  unfold SpecTec.«$match_heaptype:clause:13»
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact SpecTecExecution.Eval.pure false

theorem ready_def_exn_extern_false
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (htarget : target = .ExnHT ∨ target = .ExternHT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) target⟩)
      n (.success (.of false)) n := by
  apply ready_def_nonstructural_base_false c q n dt target hready hlookup
  rcases htarget with rfl | rfl <;> simp [nonstructuralBaseTargets]

private def funcShapeResult (strt : SpecTec.strtype) : Bool :=
  match strt with
  | .DefFuncT _ => true
  | _ => false

def funcBaseMatch (dt : SpecTec.deftype) : Bool :=
  match UnrollInterface.expandResult dt with
  | some strt => funcShapeResult strt
  | none => false

theorem ready_def_func_result_of_expand
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .FuncHT⟩)
      n (.success (.of (funcShapeResult strt))) n := by
  have h9 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n :=
    def_clause9_unmatch_of_target c.TYPES dt strt .FuncHT n hexpand
      (by decide)
  have h10 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n :=
    def_clause10_unmatch_of_target c.TYPES dt strt .FuncHT n hexpand
      (by decide)
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» c.TYPES (.DefHT dt) .FuncHT) ())
    n (.success (.of (funcShapeResult strt))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:EqHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoneHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» c.TYPES (.DefHT dt) .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:DefHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h9
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h10
  cases strt with
  | DefFuncT ft =>
    apply SpecTecExecution.firstSuccess_cons_success
    simpa [funcShapeResult] using
      def_clause11_func_success c.TYPES dt ft n hexpand
  | DefStructT fields =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause11_nonfunc_unmatch c.TYPES dt (.DefStructT fields)
        n hexpand (by intro ft h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) .FuncHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:12»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:BotHT»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) .FuncHT)
      n (.success (.of false)) n
    unfold SpecTec.«$match_heaptype:clause:13»
    simpa [funcShapeResult] using
      (SpecTecExecution.Eval.pure false :
        SpecTecExecution.Eval SpecTec.specTecProgram (.pure false)
          n (.success (.of false)) n)
  | DefArrayT field =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause11_nonfunc_unmatch c.TYPES dt (.DefArrayT field)
        n hexpand (by intro ft h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) .FuncHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:12»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:BotHT»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) .FuncHT)
      n (.success (.of false)) n
    unfold SpecTec.«$match_heaptype:clause:13»
    simpa [funcShapeResult] using
      (SpecTecExecution.Eval.pure false :
        SpecTecExecution.Eval SpecTec.specTecProgram (.pure false)
          n (.success (.of false)) n)

theorem ready_def_func_result
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .FuncHT⟩)
      n (.success (.of (funcBaseMatch dt))) n := by
  obtain ⟨strt, hresult⟩ :=
    ready_indexed_expandResult_some c q dt hready hlookup
  have hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n := by
    simpa [UnrollInterface.expandOutcome, hresult] using
      UnrollInterface.expanddt_total dt n
  simpa [funcBaseMatch, hresult] using
    (ready_def_func_result_of_expand
      c q n dt strt hready hlookup hexpand)

theorem ready_def_func_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES (.DefHT dt) .FuncHT⟩)
        n (.success (.of r)) n :=
  ⟨funcBaseMatch dt, ready_def_func_result c q n dt hready hlookup⟩

private def anyShapeResult (strt : SpecTec.strtype) : Bool :=
  match strt with
  | .DefFuncT _ => false
  | _ => true

def anyBaseMatch (dt : SpecTec.deftype) : Bool :=
  match UnrollInterface.expandResult dt with
  | some strt => anyShapeResult strt
  | none => false

theorem ready_def_any_result_of_expand
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .AnyHT⟩)
      n (.success (.of (anyShapeResult strt))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» c.TYPES (.DefHT dt) .AnyHT) ())
    n (.success (.of (anyShapeResult strt))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:AnyHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:EqHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoneHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» c.TYPES (.DefHT dt) .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:DefHT»]))
  cases strt with
  | DefStructT fields =>
    apply SpecTecExecution.firstSuccess_cons_success
    simpa [anyShapeResult] using
      def_clause9_struct_any_success c.TYPES dt fields n hexpand
  | DefArrayT field =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause9_nonstruct_any_unmatch c.TYPES dt (.DefArrayT field)
        n hexpand (by intro fields h; cases h)
    apply SpecTecExecution.firstSuccess_cons_success
    simpa [anyShapeResult] using
      def_clause10_array_any_success c.TYPES dt field n hexpand
  | DefFuncT ft =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause9_nonstruct_any_unmatch c.TYPES dt (.DefFuncT ft)
        n hexpand (by intro fields h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause10_nonarray_any_unmatch c.TYPES dt (.DefFuncT ft)
        n hexpand (by intro field h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause11_unmatch_of_target c.TYPES dt .AnyHT n (by
        simp [SpecTec.«exec:match:heaptype:FuncHT»])
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) .AnyHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:12»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:BotHT»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) .AnyHT)
      n (.success (.of false)) n
    unfold SpecTec.«$match_heaptype:clause:13»
    simpa [anyShapeResult] using
      (SpecTecExecution.Eval.pure false :
        SpecTecExecution.Eval SpecTec.specTecProgram (.pure false)
          n (.success (.of false)) n)

theorem ready_def_any_result
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .AnyHT⟩)
      n (.success (.of (anyBaseMatch dt))) n := by
  obtain ⟨strt, hresult⟩ :=
    ready_indexed_expandResult_some c q dt hready hlookup
  have hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n := by
    simpa [UnrollInterface.expandOutcome, hresult] using
      UnrollInterface.expanddt_total dt n
  simpa [anyBaseMatch, hresult] using
    (ready_def_any_result_of_expand
      c q n dt strt hready hlookup hexpand)

theorem ready_def_any_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES (.DefHT dt) .AnyHT⟩)
        n (.success (.of r)) n :=
  ⟨anyBaseMatch dt, ready_def_any_result c q n dt hready hlookup⟩

theorem ready_def_fixed_match_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (htarget : target ∈ MatchSpecialBaseTotal.fixedBaseTargets) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES (.DefHT dt) target⟩)
        n (.success (.of r)) n := by
  simp [MatchSpecialBaseTotal.fixedBaseTargets] at htarget
  rcases htarget with rfl | rfl | rfl | rfl
  · exact ready_def_any_total c q n dt hready hlookup
  · exact ready_def_func_total c q n dt hready hlookup
  · exact ⟨false, ready_def_exn_extern_false c q n dt .ExnHT
      hready hlookup (Or.inl rfl)⟩
  · exact ⟨false, ready_def_exn_extern_false c q n dt .ExternHT
      hready hlookup (Or.inr rfl)⟩


private def structShapeResult (strt : SpecTec.strtype) : Bool :=
  match strt with
  | .DefStructT _ => true
  | _ => false

def structBaseMatch (dt : SpecTec.deftype) : Bool :=
  match UnrollInterface.expandResult dt with
  | some strt => structShapeResult strt
  | none => false

theorem ready_def_struct_result_of_expand
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .StructHT⟩)
      n (.success (.of (structShapeResult strt))) n := by
  have h10 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n :=
    def_clause10_unmatch_of_target c.TYPES dt strt .StructHT n hexpand
      (by decide)
  have h11 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n :=
    def_clause11_unmatch_of_target c.TYPES dt .StructHT n (by
      simp [SpecTec.«exec:match:heaptype:FuncHT»])
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» c.TYPES (.DefHT dt) .StructHT) ())
    n (.success (.of (structShapeResult strt))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:EqHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoneHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» c.TYPES (.DefHT dt) .StructHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:DefHT»]))
  cases strt with
  | DefStructT fields =>
    apply SpecTecExecution.firstSuccess_cons_success
    simpa [structShapeResult] using
      def_clause9_struct_class_success c.TYPES dt fields .StructHT n
        hexpand (Or.inr (Or.inr rfl))
  | DefArrayT field =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause9_nonstruct_unmatch c.TYPES dt (.DefArrayT field)
        .StructHT n hexpand (by intro fields h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h10
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h11
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) .StructHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:12»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:BotHT»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) .StructHT)
      n (.success (.of false)) n
    unfold SpecTec.«$match_heaptype:clause:13»
    simpa [structShapeResult] using
      (SpecTecExecution.Eval.pure false :
        SpecTecExecution.Eval SpecTec.specTecProgram (.pure false)
          n (.success (.of false)) n)
  | DefFuncT ft =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause9_nonstruct_unmatch c.TYPES dt (.DefFuncT ft)
        .StructHT n hexpand (by intro fields h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h10
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h11
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) .StructHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:12»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:BotHT»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) .StructHT)
      n (.success (.of false)) n
    unfold SpecTec.«$match_heaptype:clause:13»
    simpa [structShapeResult] using
      (SpecTecExecution.Eval.pure false :
        SpecTecExecution.Eval SpecTec.specTecProgram (.pure false)
          n (.success (.of false)) n)



theorem ready_def_struct_result
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .StructHT⟩)
      n (.success (.of (structBaseMatch dt))) n := by
  obtain ⟨strt, hresult⟩ :=
    ready_indexed_expandResult_some c q dt hready hlookup
  have hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n := by
    simpa [UnrollInterface.expandOutcome, hresult] using
      UnrollInterface.expanddt_total dt n
  simpa [structBaseMatch, hresult] using
    (ready_def_struct_result_of_expand
      c q n dt strt hready hlookup hexpand)

theorem ready_def_struct_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES (.DefHT dt) .StructHT⟩)
        n (.success (.of r)) n :=
  ⟨structBaseMatch dt, ready_def_struct_result c q n dt hready hlookup⟩

private def arrayShapeResult (strt : SpecTec.strtype) : Bool :=
  match strt with
  | .DefArrayT _ => true
  | _ => false

def arrayBaseMatch (dt : SpecTec.deftype) : Bool :=
  match UnrollInterface.expandResult dt with
  | some strt => arrayShapeResult strt
  | none => false

theorem ready_def_array_result_of_expand
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .ArrayHT⟩)
      n (.success (.of (arrayShapeResult strt))) n := by
  have h9 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n :=
    def_clause9_unmatch_of_target c.TYPES dt strt .ArrayHT n hexpand
      (by decide)
  have h11 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n :=
    def_clause11_unmatch_of_target c.TYPES dt .ArrayHT n (by
      simp [SpecTec.«exec:match:heaptype:FuncHT»])
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» c.TYPES (.DefHT dt) .ArrayHT) ())
    n (.success (.of (arrayShapeResult strt))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:EqHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoneHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» c.TYPES (.DefHT dt) .ArrayHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:DefHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h9
  cases strt with
  | DefArrayT field =>
    apply SpecTecExecution.firstSuccess_cons_success
    simpa [arrayShapeResult] using
      def_clause10_array_class_success c.TYPES dt field .ArrayHT n
        hexpand (Or.inr (Or.inr rfl))
  | DefStructT fields =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause10_nonarray_unmatch c.TYPES dt (.DefStructT fields)
        .ArrayHT n hexpand (by intro field h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h11
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) .ArrayHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:12»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:BotHT»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) .ArrayHT)
      n (.success (.of false)) n
    unfold SpecTec.«$match_heaptype:clause:13»
    simpa [arrayShapeResult] using
      (SpecTecExecution.Eval.pure false :
        SpecTecExecution.Eval SpecTec.specTecProgram (.pure false)
          n (.success (.of false)) n)
  | DefFuncT ft =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause10_nonarray_unmatch c.TYPES dt (.DefFuncT ft)
        .ArrayHT n hexpand (by intro field h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h11
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) .ArrayHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:12»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:BotHT»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) .ArrayHT)
      n (.success (.of false)) n
    unfold SpecTec.«$match_heaptype:clause:13»
    simpa [arrayShapeResult] using
      (SpecTecExecution.Eval.pure false :
        SpecTecExecution.Eval SpecTec.specTecProgram (.pure false)
          n (.success (.of false)) n)



theorem ready_def_array_result
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .ArrayHT⟩)
      n (.success (.of (arrayBaseMatch dt))) n := by
  obtain ⟨strt, hresult⟩ :=
    ready_indexed_expandResult_some c q dt hready hlookup
  have hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n := by
    simpa [UnrollInterface.expandOutcome, hresult] using
      UnrollInterface.expanddt_total dt n
  simpa [arrayBaseMatch, hresult] using
    (ready_def_array_result_of_expand
      c q n dt strt hready hlookup hexpand)

theorem ready_def_array_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES (.DefHT dt) .ArrayHT⟩)
        n (.success (.of r)) n :=
  ⟨arrayBaseMatch dt, ready_def_array_result c q n dt hready hlookup⟩

private def eqShapeResult (strt : SpecTec.strtype) : Bool :=
  match strt with
  | .DefFuncT _ => false
  | _ => true

def eqBaseMatch (dt : SpecTec.deftype) : Bool :=
  match UnrollInterface.expandResult dt with
  | some strt => eqShapeResult strt
  | none => false

theorem ready_def_eq_result_of_expand
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (strt : SpecTec.strtype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .EqHT⟩)
      n (.success (.of (eqShapeResult strt))) n := by
  have h11 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n :=
    def_clause11_unmatch_of_target c.TYPES dt .EqHT n (by
      simp [SpecTec.«exec:match:heaptype:FuncHT»])
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» c.TYPES (.DefHT dt) .EqHT) ())
    n (.success (.of (eqShapeResult strt))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:EqHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoneHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» c.TYPES (.DefHT dt) .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by
        simp [SpecTec.«exec:match:heaptype:DefHT»])
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:DefHT»]))
  cases strt with
  | DefStructT fields =>
    apply SpecTecExecution.firstSuccess_cons_success
    simpa [eqShapeResult] using
      def_clause9_struct_class_success c.TYPES dt fields .EqHT n
        hexpand (Or.inr (Or.inl rfl))
  | DefArrayT field =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause9_nonstruct_unmatch c.TYPES dt (.DefArrayT field)
        .EqHT n hexpand (by intro fields h; cases h)
    apply SpecTecExecution.firstSuccess_cons_success
    simpa [eqShapeResult] using
      def_clause10_array_class_success c.TYPES dt field .EqHT n
        hexpand (Or.inr (Or.inl rfl))
  | DefFuncT ft =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause9_nonstruct_unmatch c.TYPES dt (.DefFuncT ft)
        .EqHT n hexpand (by intro fields h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact def_clause10_nonarray_unmatch c.TYPES dt (.DefFuncT ft)
        .EqHT n hexpand (by intro field h; cases h)
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h11
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:12» c.TYPES (.DefHT dt) .EqHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:12»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:heaptype:BotHT»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:13» c.TYPES (.DefHT dt) .EqHT)
      n (.success (.of false)) n
    unfold SpecTec.«$match_heaptype:clause:13»
    simpa [eqShapeResult] using
      (SpecTecExecution.Eval.pure false :
        SpecTecExecution.Eval SpecTec.specTecProgram (.pure false)
          n (.success (.of false)) n)

theorem ready_def_eq_result
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES (.DefHT dt) .EqHT⟩)
      n (.success (.of (eqBaseMatch dt))) n := by
  obtain ⟨strt, hresult⟩ :=
    ready_indexed_expandResult_some c q dt hready hlookup
  have hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of strt)) n := by
    simpa [UnrollInterface.expandOutcome, hresult] using
      UnrollInterface.expanddt_total dt n
  simpa [eqBaseMatch, hresult] using
    (ready_def_eq_result_of_expand
      c q n dt strt hready hlookup hexpand)

theorem ready_def_eq_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES (.DefHT dt) .EqHT⟩)
        n (.success (.of r)) n :=
  ⟨eqBaseMatch dt, ready_def_eq_result c q n dt hready hlookup⟩

theorem ready_def_all_base_total
    (c : SpecTec.context) (q n : Nat) (dt : SpecTec.deftype)
    (target : SpecTec.heaptype)
    (hready : CandidateTypeReady.Ready c)
    (hlookup : c.TYPES[q]? = some dt)
    (hbase : target ∈ HeaptypeValidation.baseHeaptypes) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          c.TYPES (.DefHT dt) target⟩)
        n (.success (.of r)) n := by
  simp [HeaptypeValidation.baseHeaptypes] at hbase
  rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact ready_def_any_total c q n dt hready hlookup
  · exact ⟨false, ready_def_nonstructural_base_false c q n dt .NoneHT
      hready hlookup (by simp [nonstructuralBaseTargets])⟩
  · exact ready_def_eq_total c q n dt hready hlookup
  · exact ⟨false, ready_def_nonstructural_base_false c q n dt .I31HT
      hready hlookup (by simp [nonstructuralBaseTargets])⟩
  · exact ready_def_struct_total c q n dt hready hlookup
  · exact ready_def_array_total c q n dt hready hlookup
  · exact ready_def_func_total c q n dt hready hlookup
  · exact ⟨false, ready_def_nonstructural_base_false c q n dt .NoFuncHT
      hready hlookup (by simp [nonstructuralBaseTargets])⟩
  · exact ⟨false, ready_def_nonstructural_base_false c q n dt .ExnHT
      hready hlookup (by simp [nonstructuralBaseTargets])⟩
  · exact ⟨false, ready_def_nonstructural_base_false c q n dt .NoExnHT
      hready hlookup (by simp [nonstructuralBaseTargets])⟩
  · exact ⟨false, ready_def_nonstructural_base_false c q n dt .ExternHT
      hready hlookup (by simp [nonstructuralBaseTargets])⟩
  · exact ⟨false, ready_def_nonstructural_base_false c q n dt .NoExternHT
      hready hlookup (by simp [nonstructuralBaseTargets])⟩
  · exact ⟨false, ready_def_nonstructural_base_false c q n dt .BotHT
      hready hlookup (by simp [nonstructuralBaseTargets])⟩


end properties.wasm_module_ok.MatchReadyDefFixed
