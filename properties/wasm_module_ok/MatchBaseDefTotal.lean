import properties.wasm_module_ok.MatchHeaptypeBasic

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchBaseDefTotal

theorem match_i31_def_false
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts .I31HT (.DefHT dt)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .I31HT (.DefHT dt)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:11»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:12» dts .I31HT (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_heaptype:clause:13» dts .I31HT (.DefHT dt))
    n (.success (.of false)) n
  unfold SpecTec.«$match_heaptype:clause:13»
  exact SpecTecExecution.Eval.pure false


theorem match_nonrecursive_def_false
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype)
    (dt : SpecTec.deftype) (n : Nat)
    (hnone : SpecTec.«exec:match:heaptype:NoneHT» ht = false)
    (hnofunc : SpecTec.«exec:match:heaptype:NoFuncHT» ht = false)
    (hnoexn : SpecTec.«exec:match:heaptype:NoExnHT» ht = false)
    (hnoextern : SpecTec.«exec:match:heaptype:NoExternHT» ht = false)
    (hvar : SpecTec.«sub:heaptype:heaptypeVar» ht = false)
    (hdef : SpecTec.«exec:match:heaptype:DefHT» ht = false)
    (hbot : SpecTec.«exec:match:heaptype:BotHT» ht = false)
    (hne : ht ≠ .DefHT dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht (.DefHT dt)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts ht (.DefHT dt)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnone]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnofunc]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnoexn]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnoextern]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hvar]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:11»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:12» dts ht (.DefHT dt))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hbot]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_heaptype:clause:13» dts ht (.DefHT dt))
    n (.success (.of false)) n
  unfold SpecTec.«$match_heaptype:clause:13»
  simpa [hne] using (SpecTecExecution.Eval.pure false :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.pure false) n (.success (.of false)) n)

def simpleBaseHeaptypes : List SpecTec.heaptype :=
  [.AnyHT, .EqHT, .I31HT, .StructHT, .ArrayHT,
    .FuncHT, .ExnHT, .ExternHT]

theorem match_simple_base_def_false
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype)
    (dt : SpecTec.deftype) (n : Nat)
    (hmem : ht ∈ simpleBaseHeaptypes) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht (.DefHT dt)⟩)
      n (.success (.of false)) n := by
  simp [simpleBaseHeaptypes] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply match_nonrecursive_def_false dts _ dt n
      <;> simp [SpecTec.«exec:match:heaptype:NoneHT»,
        SpecTec.«exec:match:heaptype:NoFuncHT»,
        SpecTec.«exec:match:heaptype:NoExnHT»,
        SpecTec.«exec:match:heaptype:NoExternHT»,
        SpecTec.«sub:heaptype:heaptypeVar»,
        SpecTec.«exec:match:heaptype:DefHT»,
        SpecTec.«exec:match:heaptype:BotHT»]


theorem match_nonrecursive_target_eq
    (dts : List SpecTec.deftype) (ht target : SpecTec.heaptype) (n : Nat)
    (hany : SpecTec.«exec:match:heaptype:AnyHT» target = false)
    (heq : SpecTec.«exec:match:heaptype:EqHT» target = false)
    (hnone : SpecTec.«exec:match:heaptype:NoneHT» ht = false)
    (hnofunc : SpecTec.«exec:match:heaptype:NoFuncHT» ht = false)
    (hnoexn : SpecTec.«exec:match:heaptype:NoExnHT» ht = false)
    (hnoextern : SpecTec.«exec:match:heaptype:NoExternHT» ht = false)
    (hvar : SpecTec.«sub:heaptype:heaptypeVar» ht = false)
    (hdef : SpecTec.«exec:match:heaptype:DefHT» ht = false)
    (hbot : SpecTec.«exec:match:heaptype:BotHT» ht = false) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht target⟩)
      n (.success (.of (decide (ht = target)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts ht target) ())
    n (.success (.of (decide (ht = target)))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hany]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [heq]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnone]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnofunc]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnoexn]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnoextern]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hvar]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:11»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:12» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hbot]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_heaptype:clause:13» dts ht target)
    n (.success (.of (decide (ht = target)))) n
  unfold SpecTec.«$match_heaptype:clause:13»
  exact SpecTecExecution.Eval.pure _

theorem match_simple_base_target_eq
    (dts : List SpecTec.deftype) (ht target : SpecTec.heaptype) (n : Nat)
    (hmem : ht ∈ simpleBaseHeaptypes)
    (hany : SpecTec.«exec:match:heaptype:AnyHT» target = false)
    (heq : SpecTec.«exec:match:heaptype:EqHT» target = false) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht target⟩)
      n (.success (.of (decide (ht = target)))) n := by
  simp [simpleBaseHeaptypes] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply match_nonrecursive_target_eq dts _ target n hany heq
      <;> simp [SpecTec.«exec:match:heaptype:NoneHT»,
        SpecTec.«exec:match:heaptype:NoFuncHT»,
        SpecTec.«exec:match:heaptype:NoExnHT»,
        SpecTec.«exec:match:heaptype:NoExternHT»,
        SpecTec.«sub:heaptype:heaptypeVar»,
        SpecTec.«exec:match:heaptype:DefHT»,
        SpecTec.«exec:match:heaptype:BotHT»]

theorem match_core_any_true
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat)
    (hcore : ht = .EqHT ∨ ht = .StructHT ∨
      ht = .ArrayHT ∨ ht = .I31HT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht .AnyHT⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts ht .AnyHT) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_heaptype:clause:0» dts ht .AnyHT)
    n (.success (.of true)) n
  unfold SpecTec.«$match_heaptype:clause:0»
  exact SpecTecExecution.Eval.bind_success
    (SpecTecExecution.Eval.guard_true rfl)
    (SpecTecExecution.Eval.bind_success
      (SpecTecExecution.Eval.guard_true
        (by simpa only [or_assoc] using hcore))
      (SpecTecExecution.Eval.pure true))

theorem match_core_eq_true
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat)
    (hcore : ht = .I31HT ∨ ht = .StructHT ∨ ht = .ArrayHT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht .EqHT⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts ht .EqHT) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts ht .EqHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts ht .EqHT)
      n (.success (.of true)) n
    unfold SpecTec.«$match_heaptype:clause:1»
    exact SpecTecExecution.Eval.bind_success
      (SpecTecExecution.Eval.guard_true rfl)
      (SpecTecExecution.Eval.bind_success
        (SpecTecExecution.Eval.guard_true
          (by simpa only [or_assoc] using hcore))
        (SpecTecExecution.Eval.pure true))


theorem match_nonrecursive_after_first_two
    (dts : List SpecTec.deftype) (ht target : SpecTec.heaptype) (n : Nat)
    (h0 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts ht target)
      n .unmatch n)
    (h1 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts ht target)
      n .unmatch n)
    (hnone : SpecTec.«exec:match:heaptype:NoneHT» ht = false)
    (hnofunc : SpecTec.«exec:match:heaptype:NoFuncHT» ht = false)
    (hnoexn : SpecTec.«exec:match:heaptype:NoExnHT» ht = false)
    (hnoextern : SpecTec.«exec:match:heaptype:NoExternHT» ht = false)
    (hvar : SpecTec.«sub:heaptype:heaptypeVar» ht = false)
    (hdef : SpecTec.«exec:match:heaptype:DefHT» ht = false)
    (hbot : SpecTec.«exec:match:heaptype:BotHT» ht = false) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht target⟩)
      n (.success (.of (decide (ht = target)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts ht target) ())
    n (.success (.of (decide (ht = target)))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h0
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h1
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:2» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnone]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:3» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnofunc]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:4» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnoexn]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:5» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hnoextern]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:6» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hvar]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:7» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:8» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:9» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:10» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:11» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:11»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hdef]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:12» dts ht target)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [hbot]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_heaptype:clause:13» dts ht target)
    n (.success (.of (decide (ht = target)))) n
  unfold SpecTec.«$match_heaptype:clause:13»
  exact SpecTecExecution.Eval.pure _

theorem clause0_any_unmatch
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat)
    (hnot : ¬ (ht = .EqHT ∨ ht = .StructHT ∨
      ht = .ArrayHT ∨ ht = .I31HT)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts ht .AnyHT)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:0»
  exact SpecTecExecution.Eval.bind_success
    (SpecTecExecution.Eval.guard_true rfl)
    (SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simpa only [or_assoc] using hnot)))

theorem clause1_eq_unmatch
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat)
    (hnot : ¬ (ht = .I31HT ∨ ht = .StructHT ∨ ht = .ArrayHT)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts ht .EqHT)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:1»
  exact SpecTecExecution.Eval.bind_success
    (SpecTecExecution.Eval.guard_true rfl)
    (SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simpa only [or_assoc] using hnot)))

theorem clause0_eq_unmatch
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts ht .EqHT)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:0»
  exact SpecTecExecution.Eval.bind_unmatch
    (SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))

theorem clause1_any_unmatch
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts ht .AnyHT)
      n .unmatch n := by
  unfold SpecTec.«$match_heaptype:clause:1»
  exact SpecTecExecution.Eval.bind_unmatch
    (SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:heaptype:EqHT»]))

def anyFallbackSources : List SpecTec.heaptype :=
  [.AnyHT, .FuncHT, .ExnHT, .ExternHT]

theorem match_simple_any_fallback
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat)
    (hmem : ht ∈ anyFallbackSources) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht .AnyHT⟩)
      n (.success (.of (decide (ht = .AnyHT)))) n := by
  simp [anyFallbackSources] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  all_goals
    apply match_nonrecursive_after_first_two dts _ .AnyHT n
      (clause0_any_unmatch dts _ n (by simp))
      (clause1_any_unmatch dts _ n)
      <;> simp [SpecTec.«exec:match:heaptype:NoneHT»,
        SpecTec.«exec:match:heaptype:NoFuncHT»,
        SpecTec.«exec:match:heaptype:NoExnHT»,
        SpecTec.«exec:match:heaptype:NoExternHT»,
        SpecTec.«sub:heaptype:heaptypeVar»,
        SpecTec.«exec:match:heaptype:DefHT»,
        SpecTec.«exec:match:heaptype:BotHT»]

def eqFallbackSources : List SpecTec.heaptype :=
  [.AnyHT, .EqHT, .FuncHT, .ExnHT, .ExternHT]

theorem match_simple_eq_fallback
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat)
    (hmem : ht ∈ eqFallbackSources) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts ht .EqHT⟩)
      n (.success (.of (decide (ht = .EqHT)))) n := by
  simp [eqFallbackSources] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply match_nonrecursive_after_first_two dts _ .EqHT n
      (clause0_eq_unmatch dts _ n)
      (clause1_eq_unmatch dts _ n (by simp))
      <;> simp [SpecTec.«exec:match:heaptype:NoneHT»,
        SpecTec.«exec:match:heaptype:NoFuncHT»,
        SpecTec.«exec:match:heaptype:NoExnHT»,
        SpecTec.«exec:match:heaptype:NoExternHT»,
        SpecTec.«sub:heaptype:heaptypeVar»,
        SpecTec.«exec:match:heaptype:DefHT»,
        SpecTec.«exec:match:heaptype:BotHT»]

theorem match_simple_base_any_total
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat)
    (hmem : ht ∈ simpleBaseHeaptypes) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts ht .AnyHT⟩)
        n (.success (.of r)) n := by
  simp [simpleBaseHeaptypes] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, match_simple_any_fallback dts _ n
      (by simp [anyFallbackSources])⟩
  · exact ⟨true, match_core_any_true dts _ n (by simp)⟩
  · exact ⟨true, match_core_any_true dts _ n (by simp)⟩
  · exact ⟨true, match_core_any_true dts _ n (by simp)⟩
  · exact ⟨true, match_core_any_true dts _ n (by simp)⟩
  · exact ⟨_, match_simple_any_fallback dts _ n
      (by simp [anyFallbackSources])⟩
  · exact ⟨_, match_simple_any_fallback dts _ n
      (by simp [anyFallbackSources])⟩
  · exact ⟨_, match_simple_any_fallback dts _ n
      (by simp [anyFallbackSources])⟩

theorem match_simple_base_eq_total
    (dts : List SpecTec.deftype) (ht : SpecTec.heaptype) (n : Nat)
    (hmem : ht ∈ simpleBaseHeaptypes) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts ht .EqHT⟩)
        n (.success (.of r)) n := by
  simp [simpleBaseHeaptypes] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, match_simple_eq_fallback dts _ n
      (by simp [eqFallbackSources])⟩
  · exact ⟨_, match_simple_eq_fallback dts _ n
      (by simp [eqFallbackSources])⟩
  · exact ⟨true, match_core_eq_true dts _ n (by simp)⟩
  · exact ⟨true, match_core_eq_true dts _ n (by simp)⟩
  · exact ⟨true, match_core_eq_true dts _ n (by simp)⟩
  · exact ⟨_, match_simple_eq_fallback dts _ n
      (by simp [eqFallbackSources])⟩
  · exact ⟨_, match_simple_eq_fallback dts _ n
      (by simp [eqFallbackSources])⟩
  · exact ⟨_, match_simple_eq_fallback dts _ n
      (by simp [eqFallbackSources])⟩

theorem match_simple_base_total
    (dts : List SpecTec.deftype) (ht target : SpecTec.heaptype)
    (n : Nat) (hmem : ht ∈ simpleBaseHeaptypes) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
          dts ht target⟩)
        n (.success (.of r)) n := by
  by_cases hAny : target = .AnyHT
  · subst target
    exact match_simple_base_any_total dts ht n hmem
  by_cases hEq : target = .EqHT
  · subst target
    exact match_simple_base_eq_total dts ht n hmem
  have hAnyGuard : SpecTec.«exec:match:heaptype:AnyHT» target = false := by
    cases target <;> simp_all [SpecTec.«exec:match:heaptype:AnyHT»]
  have hEqGuard : SpecTec.«exec:match:heaptype:EqHT» target = false := by
    cases target <;> simp_all [SpecTec.«exec:match:heaptype:EqHT»]
  exact ⟨_, match_simple_base_target_eq dts ht target n
    hmem hAnyGuard hEqGuard⟩

end properties.wasm_module_ok.MatchBaseDefTotal
