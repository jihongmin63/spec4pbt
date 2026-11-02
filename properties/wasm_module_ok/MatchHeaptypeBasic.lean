import properties.wasm_module_ok.MatchValtypeConditional

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchHeaptypeBasic

theorem match_heaptype_bot_bot_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .BotHT .BotHT⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .BotHT .BotHT) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .BotHT .BotHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  ·
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:1» dts .BotHT .BotHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
    ·
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .BotHT .BotHT)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      ·
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts .BotHT .BotHT)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        ·
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts .BotHT .BotHT)
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          ·
            apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts .BotHT .BotHT)
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            ·
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:6» dts .BotHT .BotHT)
                  n .unmatch n
                unfold SpecTec.«$match_heaptype:clause:6»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false
                    (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
              ·
                apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$match_heaptype:clause:7» dts .BotHT .BotHT)
                    n .unmatch n
                  unfold SpecTec.«$match_heaptype:clause:7»
                  exact SpecTecExecution.Eval.bind_unmatch
                    (SpecTecExecution.Eval.guard_false
                      (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                ·
                  apply SpecTecExecution.firstSuccess_cons_unmatch
                  · change SpecTecExecution.Eval SpecTec.specTecProgram
                      (SpecTec.«$match_heaptype:clause:8» dts .BotHT .BotHT)
                      n .unmatch n
                    unfold SpecTec.«$match_heaptype:clause:8»
                    exact SpecTecExecution.Eval.bind_unmatch
                      (SpecTecExecution.Eval.guard_false
                        (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                  ·
                    apply SpecTecExecution.firstSuccess_cons_unmatch
                    · change SpecTecExecution.Eval SpecTec.specTecProgram
                        (SpecTec.«$match_heaptype:clause:9» dts .BotHT .BotHT)
                        n .unmatch n
                      unfold SpecTec.«$match_heaptype:clause:9»
                      exact SpecTecExecution.Eval.bind_unmatch
                        (SpecTecExecution.Eval.guard_false
                          (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                    ·
                      apply SpecTecExecution.firstSuccess_cons_unmatch
                      · change SpecTecExecution.Eval SpecTec.specTecProgram
                          (SpecTec.«$match_heaptype:clause:10» dts .BotHT .BotHT)
                          n .unmatch n
                        unfold SpecTec.«$match_heaptype:clause:10»
                        exact SpecTecExecution.Eval.bind_unmatch
                          (SpecTecExecution.Eval.guard_false
                            (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                      ·
                        apply SpecTecExecution.firstSuccess_cons_unmatch
                        · change SpecTecExecution.Eval SpecTec.specTecProgram
                            (SpecTec.«$match_heaptype:clause:11» dts .BotHT .BotHT)
                            n .unmatch n
                          unfold SpecTec.«$match_heaptype:clause:11»
                          exact SpecTecExecution.Eval.bind_unmatch
                            (SpecTecExecution.Eval.guard_false
                              (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                        ·
                          apply SpecTecExecution.firstSuccess_cons_success
                          change SpecTecExecution.Eval SpecTec.specTecProgram
                            (SpecTec.«$match_heaptype:clause:12» dts .BotHT .BotHT)
                            n (.success (.of true)) n
                          unfold SpecTec.«$match_heaptype:clause:12»
                          exact SpecTecExecution.Eval.bind_success
                            (SpecTecExecution.Eval.guard_true rfl)
                            (SpecTecExecution.Eval.pure true)


theorem match_heaptype_bot_total
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .BotHT t⟩)
      n (.success (.of true)) n := by
  have h0 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .BotHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:0»
    by_cases h : SpecTec.«exec:match:heaptype:AnyHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  have h1 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts .BotHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:1»
    by_cases h : SpecTec.«exec:match:heaptype:EqHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .BotHT t) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h0
  ·
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h1
    ·
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .BotHT t)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      ·
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts .BotHT t)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        ·
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts .BotHT t)
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          ·
            apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts .BotHT t)
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            ·
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:6» dts .BotHT t)
                  n .unmatch n
                unfold SpecTec.«$match_heaptype:clause:6»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false
                    (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
              ·
                apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$match_heaptype:clause:7» dts .BotHT t)
                    n .unmatch n
                  unfold SpecTec.«$match_heaptype:clause:7»
                  exact SpecTecExecution.Eval.bind_unmatch
                    (SpecTecExecution.Eval.guard_false
                      (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                ·
                  apply SpecTecExecution.firstSuccess_cons_unmatch
                  · change SpecTecExecution.Eval SpecTec.specTecProgram
                      (SpecTec.«$match_heaptype:clause:8» dts .BotHT t)
                      n .unmatch n
                    unfold SpecTec.«$match_heaptype:clause:8»
                    exact SpecTecExecution.Eval.bind_unmatch
                      (SpecTecExecution.Eval.guard_false
                        (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                  ·
                    apply SpecTecExecution.firstSuccess_cons_unmatch
                    · change SpecTecExecution.Eval SpecTec.specTecProgram
                        (SpecTec.«$match_heaptype:clause:9» dts .BotHT t)
                        n .unmatch n
                      unfold SpecTec.«$match_heaptype:clause:9»
                      exact SpecTecExecution.Eval.bind_unmatch
                        (SpecTecExecution.Eval.guard_false
                          (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                    ·
                      apply SpecTecExecution.firstSuccess_cons_unmatch
                      · change SpecTecExecution.Eval SpecTec.specTecProgram
                          (SpecTec.«$match_heaptype:clause:10» dts .BotHT t)
                          n .unmatch n
                        unfold SpecTec.«$match_heaptype:clause:10»
                        exact SpecTecExecution.Eval.bind_unmatch
                          (SpecTecExecution.Eval.guard_false
                            (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                      ·
                        apply SpecTecExecution.firstSuccess_cons_unmatch
                        · change SpecTecExecution.Eval SpecTec.specTecProgram
                            (SpecTec.«$match_heaptype:clause:11» dts .BotHT t)
                            n .unmatch n
                          unfold SpecTec.«$match_heaptype:clause:11»
                          exact SpecTecExecution.Eval.bind_unmatch
                            (SpecTecExecution.Eval.guard_false
                              (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                        ·
                          apply SpecTecExecution.firstSuccess_cons_success
                          change SpecTecExecution.Eval SpecTec.specTecProgram
                            (SpecTec.«$match_heaptype:clause:12» dts .BotHT t)
                            n (.success (.of true)) n
                          unfold SpecTec.«$match_heaptype:clause:12»
                          exact SpecTecExecution.Eval.bind_success
                            (SpecTecExecution.Eval.guard_true rfl)
                            (SpecTecExecution.Eval.pure true)


theorem match_heaptype_any_any_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .AnyHT .AnyHT⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .AnyHT .AnyHT) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .AnyHT .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by decide))
  ·
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:1» dts .AnyHT .AnyHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
    ·
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .AnyHT .AnyHT)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      ·
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts .AnyHT .AnyHT)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        ·
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts .AnyHT .AnyHT)
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          ·
            apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts .AnyHT .AnyHT)
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            ·
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:6» dts .AnyHT .AnyHT)
                  n .unmatch n
                unfold SpecTec.«$match_heaptype:clause:6»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false
                    (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
              ·
                apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$match_heaptype:clause:7» dts .AnyHT .AnyHT)
                    n .unmatch n
                  unfold SpecTec.«$match_heaptype:clause:7»
                  exact SpecTecExecution.Eval.bind_unmatch
                    (SpecTecExecution.Eval.guard_false
                      (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                ·
                  apply SpecTecExecution.firstSuccess_cons_unmatch
                  · change SpecTecExecution.Eval SpecTec.specTecProgram
                      (SpecTec.«$match_heaptype:clause:8» dts .AnyHT .AnyHT)
                      n .unmatch n
                    unfold SpecTec.«$match_heaptype:clause:8»
                    exact SpecTecExecution.Eval.bind_unmatch
                      (SpecTecExecution.Eval.guard_false
                        (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                  ·
                    apply SpecTecExecution.firstSuccess_cons_unmatch
                    · change SpecTecExecution.Eval SpecTec.specTecProgram
                        (SpecTec.«$match_heaptype:clause:9» dts .AnyHT .AnyHT)
                        n .unmatch n
                      unfold SpecTec.«$match_heaptype:clause:9»
                      exact SpecTecExecution.Eval.bind_unmatch
                        (SpecTecExecution.Eval.guard_false
                          (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                    ·
                      apply SpecTecExecution.firstSuccess_cons_unmatch
                      · change SpecTecExecution.Eval SpecTec.specTecProgram
                          (SpecTec.«$match_heaptype:clause:10» dts .AnyHT .AnyHT)
                          n .unmatch n
                        unfold SpecTec.«$match_heaptype:clause:10»
                        exact SpecTecExecution.Eval.bind_unmatch
                          (SpecTecExecution.Eval.guard_false
                            (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                      ·
                        apply SpecTecExecution.firstSuccess_cons_unmatch
                        · change SpecTecExecution.Eval SpecTec.specTecProgram
                            (SpecTec.«$match_heaptype:clause:11» dts .AnyHT .AnyHT)
                            n .unmatch n
                          unfold SpecTec.«$match_heaptype:clause:11»
                          exact SpecTecExecution.Eval.bind_unmatch
                            (SpecTecExecution.Eval.guard_false
                              (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                        ·
                          apply SpecTecExecution.firstSuccess_cons_unmatch
                          · change SpecTecExecution.Eval SpecTec.specTecProgram
                              (SpecTec.«$match_heaptype:clause:12» dts .AnyHT .AnyHT)
                              n .unmatch n
                            unfold SpecTec.«$match_heaptype:clause:12»
                            exact SpecTecExecution.Eval.bind_unmatch
                              (SpecTecExecution.Eval.guard_false
                                (by simp [SpecTec.«exec:match:heaptype:BotHT»]))
                          ·
                            apply SpecTecExecution.firstSuccess_cons_success
                            change SpecTecExecution.Eval SpecTec.specTecProgram
                              (SpecTec.«$match_heaptype:clause:13» dts .AnyHT .AnyHT)
                              n (.success (.of true)) n
                            unfold SpecTec.«$match_heaptype:clause:13»
                            exact SpecTecExecution.Eval.pure true

theorem match_heaptype_func_func_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .FuncHT .FuncHT⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .FuncHT .FuncHT) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .FuncHT .FuncHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  ·
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:1» dts .FuncHT .FuncHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
    ·
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .FuncHT .FuncHT)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      ·
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts .FuncHT .FuncHT)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        ·
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts .FuncHT .FuncHT)
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          ·
            apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts .FuncHT .FuncHT)
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            ·
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:6» dts .FuncHT .FuncHT)
                  n .unmatch n
                unfold SpecTec.«$match_heaptype:clause:6»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false
                    (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
              ·
                apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$match_heaptype:clause:7» dts .FuncHT .FuncHT)
                    n .unmatch n
                  unfold SpecTec.«$match_heaptype:clause:7»
                  exact SpecTecExecution.Eval.bind_unmatch
                    (SpecTecExecution.Eval.guard_false
                      (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                ·
                  apply SpecTecExecution.firstSuccess_cons_unmatch
                  · change SpecTecExecution.Eval SpecTec.specTecProgram
                      (SpecTec.«$match_heaptype:clause:8» dts .FuncHT .FuncHT)
                      n .unmatch n
                    unfold SpecTec.«$match_heaptype:clause:8»
                    exact SpecTecExecution.Eval.bind_unmatch
                      (SpecTecExecution.Eval.guard_false
                        (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                  ·
                    apply SpecTecExecution.firstSuccess_cons_unmatch
                    · change SpecTecExecution.Eval SpecTec.specTecProgram
                        (SpecTec.«$match_heaptype:clause:9» dts .FuncHT .FuncHT)
                        n .unmatch n
                      unfold SpecTec.«$match_heaptype:clause:9»
                      exact SpecTecExecution.Eval.bind_unmatch
                        (SpecTecExecution.Eval.guard_false
                          (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                    ·
                      apply SpecTecExecution.firstSuccess_cons_unmatch
                      · change SpecTecExecution.Eval SpecTec.specTecProgram
                          (SpecTec.«$match_heaptype:clause:10» dts .FuncHT .FuncHT)
                          n .unmatch n
                        unfold SpecTec.«$match_heaptype:clause:10»
                        exact SpecTecExecution.Eval.bind_unmatch
                          (SpecTecExecution.Eval.guard_false
                            (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                      ·
                        apply SpecTecExecution.firstSuccess_cons_unmatch
                        · change SpecTecExecution.Eval SpecTec.specTecProgram
                            (SpecTec.«$match_heaptype:clause:11» dts .FuncHT .FuncHT)
                            n .unmatch n
                          unfold SpecTec.«$match_heaptype:clause:11»
                          exact SpecTecExecution.Eval.bind_unmatch
                            (SpecTecExecution.Eval.guard_false
                              (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                        ·
                          apply SpecTecExecution.firstSuccess_cons_unmatch
                          · change SpecTecExecution.Eval SpecTec.specTecProgram
                              (SpecTec.«$match_heaptype:clause:12» dts .FuncHT .FuncHT)
                              n .unmatch n
                            unfold SpecTec.«$match_heaptype:clause:12»
                            exact SpecTecExecution.Eval.bind_unmatch
                              (SpecTecExecution.Eval.guard_false
                                (by simp [SpecTec.«exec:match:heaptype:BotHT»]))
                          ·
                            apply SpecTecExecution.firstSuccess_cons_success
                            change SpecTecExecution.Eval SpecTec.specTecProgram
                              (SpecTec.«$match_heaptype:clause:13» dts .FuncHT .FuncHT)
                              n (.success (.of true)) n
                            unfold SpecTec.«$match_heaptype:clause:13»
                            exact SpecTecExecution.Eval.pure true

theorem match_heaptype_exn_exn_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .ExnHT .ExnHT⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .ExnHT .ExnHT) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .ExnHT .ExnHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  ·
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:1» dts .ExnHT .ExnHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
    ·
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .ExnHT .ExnHT)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      ·
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts .ExnHT .ExnHT)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        ·
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts .ExnHT .ExnHT)
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          ·
            apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts .ExnHT .ExnHT)
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            ·
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:6» dts .ExnHT .ExnHT)
                  n .unmatch n
                unfold SpecTec.«$match_heaptype:clause:6»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false
                    (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
              ·
                apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$match_heaptype:clause:7» dts .ExnHT .ExnHT)
                    n .unmatch n
                  unfold SpecTec.«$match_heaptype:clause:7»
                  exact SpecTecExecution.Eval.bind_unmatch
                    (SpecTecExecution.Eval.guard_false
                      (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                ·
                  apply SpecTecExecution.firstSuccess_cons_unmatch
                  · change SpecTecExecution.Eval SpecTec.specTecProgram
                      (SpecTec.«$match_heaptype:clause:8» dts .ExnHT .ExnHT)
                      n .unmatch n
                    unfold SpecTec.«$match_heaptype:clause:8»
                    exact SpecTecExecution.Eval.bind_unmatch
                      (SpecTecExecution.Eval.guard_false
                        (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                  ·
                    apply SpecTecExecution.firstSuccess_cons_unmatch
                    · change SpecTecExecution.Eval SpecTec.specTecProgram
                        (SpecTec.«$match_heaptype:clause:9» dts .ExnHT .ExnHT)
                        n .unmatch n
                      unfold SpecTec.«$match_heaptype:clause:9»
                      exact SpecTecExecution.Eval.bind_unmatch
                        (SpecTecExecution.Eval.guard_false
                          (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                    ·
                      apply SpecTecExecution.firstSuccess_cons_unmatch
                      · change SpecTecExecution.Eval SpecTec.specTecProgram
                          (SpecTec.«$match_heaptype:clause:10» dts .ExnHT .ExnHT)
                          n .unmatch n
                        unfold SpecTec.«$match_heaptype:clause:10»
                        exact SpecTecExecution.Eval.bind_unmatch
                          (SpecTecExecution.Eval.guard_false
                            (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                      ·
                        apply SpecTecExecution.firstSuccess_cons_unmatch
                        · change SpecTecExecution.Eval SpecTec.specTecProgram
                            (SpecTec.«$match_heaptype:clause:11» dts .ExnHT .ExnHT)
                            n .unmatch n
                          unfold SpecTec.«$match_heaptype:clause:11»
                          exact SpecTecExecution.Eval.bind_unmatch
                            (SpecTecExecution.Eval.guard_false
                              (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                        ·
                          apply SpecTecExecution.firstSuccess_cons_unmatch
                          · change SpecTecExecution.Eval SpecTec.specTecProgram
                              (SpecTec.«$match_heaptype:clause:12» dts .ExnHT .ExnHT)
                              n .unmatch n
                            unfold SpecTec.«$match_heaptype:clause:12»
                            exact SpecTecExecution.Eval.bind_unmatch
                              (SpecTecExecution.Eval.guard_false
                                (by simp [SpecTec.«exec:match:heaptype:BotHT»]))
                          ·
                            apply SpecTecExecution.firstSuccess_cons_success
                            change SpecTecExecution.Eval SpecTec.specTecProgram
                              (SpecTec.«$match_heaptype:clause:13» dts .ExnHT .ExnHT)
                              n (.success (.of true)) n
                            unfold SpecTec.«$match_heaptype:clause:13»
                            exact SpecTecExecution.Eval.pure true

theorem match_heaptype_extern_extern_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .ExternHT .ExternHT⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .ExternHT .ExternHT) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .ExternHT .ExternHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  ·
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:1» dts .ExternHT .ExternHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
    ·
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .ExternHT .ExternHT)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      ·
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts .ExternHT .ExternHT)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        ·
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts .ExternHT .ExternHT)
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          ·
            apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts .ExternHT .ExternHT)
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            ·
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:6» dts .ExternHT .ExternHT)
                  n .unmatch n
                unfold SpecTec.«$match_heaptype:clause:6»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false
                    (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
              ·
                apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$match_heaptype:clause:7» dts .ExternHT .ExternHT)
                    n .unmatch n
                  unfold SpecTec.«$match_heaptype:clause:7»
                  exact SpecTecExecution.Eval.bind_unmatch
                    (SpecTecExecution.Eval.guard_false
                      (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                ·
                  apply SpecTecExecution.firstSuccess_cons_unmatch
                  · change SpecTecExecution.Eval SpecTec.specTecProgram
                      (SpecTec.«$match_heaptype:clause:8» dts .ExternHT .ExternHT)
                      n .unmatch n
                    unfold SpecTec.«$match_heaptype:clause:8»
                    exact SpecTecExecution.Eval.bind_unmatch
                      (SpecTecExecution.Eval.guard_false
                        (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                  ·
                    apply SpecTecExecution.firstSuccess_cons_unmatch
                    · change SpecTecExecution.Eval SpecTec.specTecProgram
                        (SpecTec.«$match_heaptype:clause:9» dts .ExternHT .ExternHT)
                        n .unmatch n
                      unfold SpecTec.«$match_heaptype:clause:9»
                      exact SpecTecExecution.Eval.bind_unmatch
                        (SpecTecExecution.Eval.guard_false
                          (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                    ·
                      apply SpecTecExecution.firstSuccess_cons_unmatch
                      · change SpecTecExecution.Eval SpecTec.specTecProgram
                          (SpecTec.«$match_heaptype:clause:10» dts .ExternHT .ExternHT)
                          n .unmatch n
                        unfold SpecTec.«$match_heaptype:clause:10»
                        exact SpecTecExecution.Eval.bind_unmatch
                          (SpecTecExecution.Eval.guard_false
                            (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                      ·
                        apply SpecTecExecution.firstSuccess_cons_unmatch
                        · change SpecTecExecution.Eval SpecTec.specTecProgram
                            (SpecTec.«$match_heaptype:clause:11» dts .ExternHT .ExternHT)
                            n .unmatch n
                          unfold SpecTec.«$match_heaptype:clause:11»
                          exact SpecTecExecution.Eval.bind_unmatch
                            (SpecTecExecution.Eval.guard_false
                              (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
                        ·
                          apply SpecTecExecution.firstSuccess_cons_unmatch
                          · change SpecTecExecution.Eval SpecTec.specTecProgram
                              (SpecTec.«$match_heaptype:clause:12» dts .ExternHT .ExternHT)
                              n .unmatch n
                            unfold SpecTec.«$match_heaptype:clause:12»
                            exact SpecTecExecution.Eval.bind_unmatch
                              (SpecTecExecution.Eval.guard_false
                                (by simp [SpecTec.«exec:match:heaptype:BotHT»]))
                          ·
                            apply SpecTecExecution.firstSuccess_cons_success
                            change SpecTecExecution.Eval SpecTec.specTecProgram
                              (SpecTec.«$match_heaptype:clause:13» dts .ExternHT .ExternHT)
                              n (.success (.of true)) n
                            unfold SpecTec.«$match_heaptype:clause:13»
                            exact SpecTecExecution.Eval.pure true

theorem match_heaptype_none_any_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .NoneHT .AnyHT⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .NoneHT .AnyHT) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .NoneHT .AnyHT)
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by decide))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:1» dts .NoneHT .AnyHT)
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:2» dts .NoneHT .AnyHT)
        n (.success (.of true)) n
      unfold SpecTec.«$match_heaptype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact match_heaptype_any_any_total dts n
        · exact SpecTecExecution.Eval.pure true

theorem match_heaptype_none_total_of_any
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype)
    (r : Bool) (n : Nat)
    (hany : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts t .AnyHT⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .NoneHT t⟩)
      n (.success (.of r)) n := by
  have h0 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .NoneHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:0»
    by_cases h : SpecTec.«exec:match:heaptype:AnyHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  have h1 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts .NoneHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:1»
    by_cases h : SpecTec.«exec:match:heaptype:EqHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .NoneHT t) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h0
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h1
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:2» dts .NoneHT t)
        n (.success (.of r)) n
      unfold SpecTec.«$match_heaptype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact hany
        · exact SpecTecExecution.Eval.pure r

theorem match_heaptype_nofunc_total_of_func
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype)
    (r : Bool) (n : Nat)
    (hfunc : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts t .FuncHT⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .NoFuncHT t⟩)
      n (.success (.of r)) n := by
  have h0 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .NoFuncHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:0»
    by_cases h : SpecTec.«exec:match:heaptype:AnyHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  have h1 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts .NoFuncHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:1»
    by_cases h : SpecTec.«exec:match:heaptype:EqHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .NoFuncHT t) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h0
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h1
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .NoFuncHT t)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:3» dts .NoFuncHT t)
          n (.success (.of r)) n
        unfold SpecTec.«$match_heaptype:clause:3»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
          · exact hfunc
          · exact SpecTecExecution.Eval.pure r

theorem match_heaptype_noexn_total_of_exn
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype)
    (r : Bool) (n : Nat)
    (hexn : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts t .ExnHT⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .NoExnHT t⟩)
      n (.success (.of r)) n := by
  have h0 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .NoExnHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:0»
    by_cases h : SpecTec.«exec:match:heaptype:AnyHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  have h1 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts .NoExnHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:1»
    by_cases h : SpecTec.«exec:match:heaptype:EqHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .NoExnHT t) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h0
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h1
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .NoExnHT t)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts .NoExnHT t)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:4» dts .NoExnHT t)
            n (.success (.of r)) n
          unfold SpecTec.«$match_heaptype:clause:4»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · apply SpecTecExecution.Eval.bind_success
            · exact hexn
            · exact SpecTecExecution.Eval.pure r

theorem match_heaptype_noextern_total_of_extern
    (dts : List SpecTec.deftype) (t : SpecTec.heaptype)
    (r : Bool) (n : Nat)
    (hextern : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts t .ExternHT⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .NoExternHT t⟩)
      n (.success (.of r)) n := by
  have h0 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts .NoExternHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:0»
    by_cases h : SpecTec.«exec:match:heaptype:AnyHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  have h1 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts .NoExternHT t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:1»
    by_cases h : SpecTec.«exec:match:heaptype:EqHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts .NoExternHT t) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h0
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h1
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts .NoExternHT t)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts .NoExternHT t)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts .NoExternHT t)
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          · apply SpecTecExecution.firstSuccess_cons_success
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:5» dts .NoExternHT t)
              n (.success (.of r)) n
            unfold SpecTec.«$match_heaptype:clause:5»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · apply SpecTecExecution.Eval.bind_success
              · exact hextern
              · exact SpecTecExecution.Eval.pure r

theorem match_heaptype_nofunc_func_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .NoFuncHT .FuncHT⟩)
      n (.success (.of true)) n := by
  exact match_heaptype_nofunc_total_of_func dts .FuncHT true n
    (match_heaptype_func_func_total dts n)

theorem match_heaptype_noexn_exn_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .NoExnHT .ExnHT⟩)
      n (.success (.of true)) n := by
  exact match_heaptype_noexn_total_of_exn dts .ExnHT true n
    (match_heaptype_exn_exn_total dts n)

theorem match_heaptype_noextern_extern_total
    (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts .NoExternHT .ExternHT⟩)
      n (.success (.of true)) n := by
  exact match_heaptype_noextern_total_of_extern dts .ExternHT true n
    (match_heaptype_extern_extern_total dts n)

theorem match_heaptype_statx_total_of_def
    (dts : List SpecTec.deftype) (x : SpecTec.typeidx)
    (dt : SpecTec.deftype) (t : SpecTec.heaptype)
    (r : Bool) (n : Nat)
    (hlookup : dts[x]? = some dt)
    (hdef : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts (.DefHT dt) t⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts (.VarHT (.StatX x)) t⟩)
      n (.success (.of r)) n := by
  have hx : x < dts.length := by
    by_cases hx : x < dts.length
    · exact hx
    · have hnone : dts[x]? = none := by simp [hx]
      rw [hnone] at hlookup
      cases hlookup
  have h0 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts (.VarHT (.StatX x)) t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:0»
    by_cases h : SpecTec.«exec:match:heaptype:AnyHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  have h1 : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:1» dts (.VarHT (.StatX x)) t)
      n .unmatch n := by
    unfold SpecTec.«$match_heaptype:clause:1»
    by_cases h : SpecTec.«exec:match:heaptype:EqHT» t = true
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true h
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false h)
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts (.VarHT (.StatX x)) t) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · exact h0
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact h1
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts (.VarHT (.StatX x)) t)
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts (.VarHT (.StatX x)) t)
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts (.VarHT (.StatX x)) t)
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts (.VarHT (.StatX x)) t)
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            · apply SpecTecExecution.firstSuccess_cons_success
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:6» dts (.VarHT (.StatX x)) t)
                n (.success (.of r)) n
              unfold SpecTec.«$match_heaptype:clause:6»
              apply SpecTecExecution.Eval.bind_success
              · exact SpecTecExecution.Eval.guard_true rfl
              · apply SpecTecExecution.Eval.bind_success
                · exact SpecTecExecution.Eval.guard_true rfl
                · apply SpecTecExecution.Eval.bind_success
                  · exact SpecTecExecution.Eval.guard_true hx
                  · rw [hlookup]
                    apply SpecTecExecution.Eval.bind_success
                    · exact hdef
                    · exact SpecTecExecution.Eval.pure r

theorem match_heaptype_def_statx_total_of_defs
    (dts : List SpecTec.deftype) (x : SpecTec.typeidx)
    (dt₁ dt₂ : SpecTec.deftype) (r : Bool) (n : Nat)
    (hlookup : dts[x]? = some dt₂)
    (hdef : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts (.DefHT dt₁) (.DefHT dt₂)⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts (.DefHT dt₁) (.VarHT (.StatX x))⟩)
      n (.success (.of r)) n := by
  have hx : x < dts.length := by
    by_cases hx : x < dts.length
    · exact hx
    · have hnone : dts[x]? = none := by simp [hx]
      rw [hnone] at hlookup
      cases hlookup
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts (.DefHT dt₁) (.VarHT (.StatX x))) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts (.DefHT dt₁) (.VarHT (.StatX x)))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:1» dts (.DefHT dt₁) (.VarHT (.StatX x)))
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts (.DefHT dt₁) (.VarHT (.StatX x)))
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts (.DefHT dt₁) (.VarHT (.StatX x)))
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts (.DefHT dt₁) (.VarHT (.StatX x)))
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts (.DefHT dt₁) (.VarHT (.StatX x)))
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            · apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:6» dts (.DefHT dt₁) (.VarHT (.StatX x)))
                  n .unmatch n
                unfold SpecTec.«$match_heaptype:clause:6»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false
                    (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
              · apply SpecTecExecution.firstSuccess_cons_success
                change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:7» dts (.DefHT dt₁) (.VarHT (.StatX x)))
                  n (.success (.of r)) n
                unfold SpecTec.«$match_heaptype:clause:7»
                apply SpecTecExecution.Eval.bind_success
                · exact SpecTecExecution.Eval.guard_true rfl
                · apply SpecTecExecution.Eval.bind_success
                  · exact SpecTecExecution.Eval.guard_true rfl
                  · apply SpecTecExecution.Eval.bind_success
                    · exact SpecTecExecution.Eval.guard_true rfl
                    · apply SpecTecExecution.Eval.bind_success
                      · exact SpecTecExecution.Eval.guard_true hx
                      · rw [hlookup]
                        apply SpecTecExecution.Eval.bind_success
                        · exact hdef
                        · exact SpecTecExecution.Eval.pure r

theorem match_heaptype_def_def_total_of_match_deftype
    (dts : List SpecTec.deftype) (dt₁ dt₂ : SpecTec.deftype)
    (r : Bool) (n : Nat)
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_deftype» dts dt₁ dt₂⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts (.DefHT dt₁) (.DefHT dt₂)⟩)
      n (.success (.of r)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_clauses» dts (.DefHT dt₁) (.DefHT dt₂)) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype:clause:0» dts (.DefHT dt₁) (.DefHT dt₂))
      n .unmatch n
    unfold SpecTec.«$match_heaptype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:heaptype:AnyHT»]))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype:clause:1» dts (.DefHT dt₁) (.DefHT dt₂))
        n .unmatch n
      unfold SpecTec.«$match_heaptype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:EqHT»]))
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_heaptype:clause:2» dts (.DefHT dt₁) (.DefHT dt₂))
          n .unmatch n
        unfold SpecTec.«$match_heaptype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:heaptype:NoneHT»]))
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_heaptype:clause:3» dts (.DefHT dt₁) (.DefHT dt₂))
            n .unmatch n
          unfold SpecTec.«$match_heaptype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:heaptype:NoFuncHT»]))
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$match_heaptype:clause:4» dts (.DefHT dt₁) (.DefHT dt₂))
              n .unmatch n
            unfold SpecTec.«$match_heaptype:clause:4»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:heaptype:NoExnHT»]))
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$match_heaptype:clause:5» dts (.DefHT dt₁) (.DefHT dt₂))
                n .unmatch n
              unfold SpecTec.«$match_heaptype:clause:5»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:heaptype:NoExternHT»]))
            · apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$match_heaptype:clause:6» dts (.DefHT dt₁) (.DefHT dt₂))
                  n .unmatch n
                unfold SpecTec.«$match_heaptype:clause:6»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false
                    (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
              · apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$match_heaptype:clause:7» dts (.DefHT dt₁) (.DefHT dt₂))
                    n .unmatch n
                  unfold SpecTec.«$match_heaptype:clause:7»
                  apply SpecTecExecution.Eval.bind_success
                  · exact SpecTecExecution.Eval.guard_true rfl
                  · exact SpecTecExecution.Eval.bind_unmatch
                      (SpecTecExecution.Eval.guard_false
                        (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
                · apply SpecTecExecution.firstSuccess_cons_success
                  change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$match_heaptype:clause:8» dts (.DefHT dt₁) (.DefHT dt₂))
                    n (.success (.of r)) n
                  unfold SpecTec.«$match_heaptype:clause:8»
                  apply SpecTecExecution.Eval.bind_success
                  · exact SpecTecExecution.Eval.guard_true rfl
                  · apply SpecTecExecution.Eval.bind_success
                    · exact SpecTecExecution.Eval.guard_true rfl
                    · apply SpecTecExecution.Eval.bind_success
                      · exact hmatch
                      · exact SpecTecExecution.Eval.pure r

theorem match_deftype_refl_total
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_deftype» dts dt dt⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_deftype_clauses» dts dt dt) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_deftype:clause:0» dts dt dt)
    n (.success (.of true)) n
  unfold SpecTec.«$match_deftype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · exact SpecTecExecution.Eval.pure true

theorem match_heaptype_def_refl_total
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts (.DefHT dt) (.DefHT dt)⟩)
      n (.success (.of true)) n := by
  exact match_heaptype_def_def_total_of_match_deftype dts dt dt true n
    (match_deftype_refl_total dts dt n)

theorem match_deftype_neq_subst_eq_total
    (dts : List SpecTec.deftype) (dt₁ dt₂ s : SpecTec.deftype)
    (n : Nat) (hne : dt₁ ≠ dt₂)
    (hsubst₁ : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype» (List SpecTec.deftype)
          dts SpecTec.SpecTecCall.«$subst_of» dt₁⟩)
      n (.success (.of s)) n)
    (hsubst₂ : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype» (List SpecTec.deftype)
          dts SpecTec.SpecTecCall.«$subst_of» dt₂⟩)
      n (.success (.of s)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_deftype» dts dt₁ dt₂⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_deftype_clauses» dts dt₁ dt₂) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_deftype:clause:0» dts dt₁ dt₂)
      n .unmatch n
    unfold SpecTec.«$match_deftype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by intro h; exact hne h.symm))
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_deftype:clause:1» dts dt₁ dt₂)
      n (.success (.of true)) n
    unfold SpecTec.«$match_deftype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hne
    · apply SpecTecExecution.Eval.bind_success
      · exact hsubst₁
      · apply SpecTecExecution.Eval.bind_success
        · exact hsubst₂
        · apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · exact SpecTecExecution.Eval.pure true

theorem match_deftype_neq_subst_neq_total_of_exists
    (dts : List SpecTec.deftype) (dt₁ dt₂ s₁ s₂ : SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (r : Bool) (n : Nat)
    (hne : dt₁ ≠ dt₂)
    (hsubst₁ : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype» (List SpecTec.deftype)
          dts SpecTec.SpecTecCall.«$subst_of» dt₁⟩)
      n (.success (.of s₁)) n)
    (hsubst₂ : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype» (List SpecTec.deftype)
          dts SpecTec.SpecTecCall.«$subst_of» dt₂⟩)
      n (.success (.of s₂)) n)
    (hneq : s₁ ≠ s₂)
    (hunroll : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dt₁⟩)
      n (.success (.of (SpecTec.subtype.SubT fin hts strt))) n)
    (hexists : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» dts hts dt₂⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_deftype» dts dt₁ dt₂⟩)
      n (.success (.of r)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_deftype_clauses» dts dt₁ dt₂) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_deftype:clause:0» dts dt₁ dt₂)
      n .unmatch n
    unfold SpecTec.«$match_deftype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by intro h; exact hne h.symm))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_deftype:clause:1» dts dt₁ dt₂)
        n .unmatch n
      unfold SpecTec.«$match_deftype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true hne
      · apply SpecTecExecution.Eval.bind_success
        · exact hsubst₁
        · apply SpecTecExecution.Eval.bind_success
          · exact hsubst₂
          · exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false
                (by intro h; exact hneq h.symm))
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_deftype:clause:2» dts dt₁ dt₂)
        n (.success (.of r)) n
      unfold SpecTec.«$match_deftype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true hne
      · apply SpecTecExecution.Eval.bind_success
        · exact hsubst₁
        · apply SpecTecExecution.Eval.bind_success
          · exact hsubst₂
          · apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true hneq
            · apply SpecTecExecution.Eval.bind_success
              · exact hunroll
              · apply SpecTecExecution.Eval.bind_success
                · exact hexists
                · exact SpecTecExecution.Eval.pure r

theorem match_heaptype_exists_nil_total
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» dts [] dt⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_exists_clauses» dts [] dt) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_heaptype_exists:clause:0» dts [] dt)
    n (.success (.of false)) n
  unfold SpecTec.«$match_heaptype_exists:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · exact SpecTecExecution.Eval.pure false

theorem match_heaptype_exists_cons_true_total
    (dts : List SpecTec.deftype) (h : SpecTec.heaptype)
    (tl : List SpecTec.heaptype) (dt : SpecTec.deftype) (n : Nat)
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts h (.DefHT dt)⟩)
      n (.success (.of true)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» dts (h :: tl) dt⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_exists_clauses» dts (h :: tl) dt) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype_exists:clause:0» dts (h :: tl) dt)
      n .unmatch n
    unfold SpecTec.«$match_heaptype_exists:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype_exists:clause:1» dts (h :: tl) dt)
      n (.success (.of true)) n
    unfold SpecTec.«$match_heaptype_exists:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by simp)
    · apply SpecTecExecution.Eval.bind_success
      · exact hmatch
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · exact SpecTecExecution.Eval.pure true

theorem match_heaptype_exists_cons_false_total_of_tail
    (dts : List SpecTec.deftype) (h : SpecTec.heaptype)
    (tl : List SpecTec.heaptype) (dt : SpecTec.deftype)
    (r : Bool) (n : Nat)
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» dts h (.DefHT dt)⟩)
      n (.success (.of false)) n)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» dts tl dt⟩)
      n (.success (.of r)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» dts (h :: tl) dt⟩)
      n (.success (.of r)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_exists_clauses» dts (h :: tl) dt) ())
    n (.success (.of r)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype_exists:clause:0» dts (h :: tl) dt)
      n .unmatch n
    unfold SpecTec.«$match_heaptype_exists:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype_exists:clause:1» dts (h :: tl) dt)
        n .unmatch n
      unfold SpecTec.«$match_heaptype_exists:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simp)
      · apply SpecTecExecution.Eval.bind_success
        · exact hmatch
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by decide))
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype_exists:clause:2» dts (h :: tl) dt)
        n (.success (.of r)) n
      unfold SpecTec.«$match_heaptype_exists:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simp)
      · apply SpecTecExecution.Eval.bind_success
        · exact hmatch
        · apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true (by decide)
          · apply SpecTecExecution.Eval.bind_success
            · exact htail
            · exact SpecTecExecution.Eval.pure r

theorem match_heaptype_exists_total_of_heads
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (hts : List SpecTec.heaptype) (n : Nat)
    (hheads : ∀ h ∈ hts, ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» dts h (.DefHT dt)⟩)
        n (.success (.of r)) n) :
    ∃ r : Bool, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» dts hts dt⟩)
      n (.success (.of r)) n := by
  induction hts with
  | nil =>
      exact ⟨false, match_heaptype_exists_nil_total dts dt n⟩
  | cons h tl ih =>
      obtain ⟨r, hr⟩ := hheads h (by simp)
      cases r with
      | true =>
          exact ⟨true, match_heaptype_exists_cons_true_total dts h tl dt n hr⟩
      | false =>
          have htail : ∀ h' ∈ tl, ∃ r' : Bool,
              SpecTecExecution.Eval SpecTec.specTecProgram
                (.call ⟨Bool,
                  SpecTec.SpecTecCall.«$match_heaptype» dts h' (.DefHT dt)⟩)
                n (.success (.of r')) n := by
            intro h' hh
            exact hheads h' (by simp [hh])
          obtain ⟨r', hr'⟩ := ih htail
          exact ⟨r', match_heaptype_exists_cons_false_total_of_tail
            dts h tl dt r' n hr hr'⟩

theorem subtype_sub_ok_static_lt
    (c : SpecTec.context) (x y : SpecTec.typeidx)
    (strt : SpecTec.strtype) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok' c x strt (.VarHT (.StatX y))⟩)
      start (.success (.of ())) fin) :
    y < x := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Subtype_sub_ok'_clauses c x strt (.VarHT (.StatX y))) ())
      start (.success (.of ())) fin at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.firstSuccess_success_iff
        (SpecTec.Subtype_sub_ok'_clauses c x strt (.VarHT (.StatX y))) ()
        start (.of ()) fin).1 hbody
    unfold SpecTec.Subtype_sub_ok'_clauses at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«Subtype_sub_ok':clause:0» at h0
      simp only [SpecTec.«sub:heaptype:heaptypeVar»,
        SpecTec.«Subtype_sub_ok':rule:downcast:0»,
        SpecTec.«exec:match:typevar:StatX»] at h0
      cases h0 with
      | bind_success _ h1 =>
        cases h1 with
        | bind_success _ h2 =>
          cases h2 with
          | bind_success _ h3 =>
            split at h3
            · cases h3 with
              | bind_success _ h4 =>
                rename_i st hcall
                cases st
                cases h4 with
                | bind_success _ h5 =>
                  cases h5 with
                  | bind_success hguard _ =>
                    cases hguard with
                    | guard_true hg => exact hg.1.1
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                .unmatch _ (.success (.of ())) _ at h3
              cases h3
    | next _ hrest =>
      cases hrest

theorem subtype_sub_iter_static_lt
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (strt : SpecTec.strtype) (hts : List SpecTec.heaptype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt hts⟩)
      start (.success (.of ())) fin) :
    ∀ y : SpecTec.typeidx,
      .VarHT (.StatX y) ∈ hts → y < x := by
  induction hts generalizing start fin with
  | nil =>
      intro y hy
      cases hy
  | cons hd tl ih =>
      cases h with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» c x strt (hd :: tl)) ())
          start (.success (.of ())) fin at hbody
        obtain ⟨idx, hselected⟩ :=
          (SpecTecExecution.firstSuccess_success_iff
            (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» c x strt (hd :: tl)) ()
            start (.of ()) fin).1 hbody
        unfold SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» at hselected
        cases hselected with
        | here h0 =>
          unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:0» at h0
          cases h0
        | next _ hrest =>
          cases hrest with
          | here h1 =>
            unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1» at h1
            cases h1 with
            | bind_success hhead htailplan =>
              cases htailplan with
              | bind_success htail _ =>
                intro y hy
                rcases List.mem_cons.mp hy with heq | hmem
                · subst hd
                  exact subtype_sub_ok_static_lt c x y strt _ _ hhead
                · exact ih _ _ htail y hmem
          | next _ hrest => cases hrest

theorem subtype_subtype_static_lt
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok c x
          (SpecTec.subtype.SubT fin hts strt)⟩)
      start (.success (.of ())) finish) :
    ∀ y : SpecTec.typeidx,
      .VarHT (.StatX y) ∈ hts → y < x := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Subtype_sub_ok_clauses c x
          (SpecTec.subtype.SubT fin hts strt)) ())
      start (.success (.of ())) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.firstSuccess_success_iff
        (SpecTec.Subtype_sub_ok_clauses c x
          (SpecTec.subtype.SubT fin hts strt)) ()
        start (.of ()) finish).1 hbody
    unfold SpecTec.Subtype_sub_ok_clauses at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«Subtype_sub_ok:clause:0» at h0
      cases h0 with
      | bind_success hiter _ =>
        exact subtype_sub_iter_static_lt c x strt hts _ _ hiter
    | next _ hrest => cases hrest

theorem rectype_sub_iter_static_lt
    (c : SpecTec.context) (x : SpecTec.idx)
    (ns : List SpecTec.n) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x ns sts⟩)
      start (.success (.of ())) finish) :
    ∀ n fin hts strt,
      (n, SpecTec.subtype.SubT fin hts strt) ∈ List.zip ns sts →
      ∀ y : SpecTec.typeidx,
        .VarHT (.StatX y) ∈ hts → y < x + n := by
  induction ns generalizing sts start finish with
  | nil =>
      intro n fin hts strt hpair
      cases sts <;> cases hpair
  | cons n₀ ns ih =>
      cases sts with
      | nil =>
          intro n fin hts strt hpair
          cases hpair
      | cons st₀ sts =>
          cases h with
          | call hbody =>
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTecExecution.firstSuccess
                (SpecTec.«Rectype_ok:rule:iter:6_clauses»
                  c x (n₀ :: ns) (st₀ :: sts)) ())
              start (.success (.of ())) finish at hbody
            obtain ⟨idx, hselected⟩ :=
              (SpecTecExecution.firstSuccess_success_iff
                (SpecTec.«Rectype_ok:rule:iter:6_clauses»
                  c x (n₀ :: ns) (st₀ :: sts)) ()
                start (.of ()) finish).1 hbody
            unfold SpecTec.«Rectype_ok:rule:iter:6_clauses» at hselected
            cases hselected with
            | here h0 =>
                unfold SpecTec.«Rectype_ok:rule:iter:6:clause:0» at h0
                cases h0
            | next _ hrest =>
                cases hrest with
                | here h1 =>
                    unfold SpecTec.«Rectype_ok:rule:iter:6:clause:1» at h1
                    cases h1 with
                    | bind_success hhead htailplan =>
                        cases htailplan with
                        | bind_success htail _ =>
                            intro n fin hts strt hpair y hy
                            rcases List.mem_cons.mp hpair with heq | hmem
                            · cases st₀
                              cases Prod.mk.inj heq with
                              | intro hn hst =>
                                  cases hn
                                  cases hst
                                  exact subtype_subtype_static_lt
                                    c (x + n₀) fin hts strt _ _ hhead y hy
                            · exact ih _ _ _ htail n fin hts strt hmem y hy
                | next _ hrest => cases hrest

theorem rectype_ok_extract_sub_iter
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish) :
    ∃ ns : List SpecTec.n, ∃ dts : List SpecTec.deftype,
      c' = {c with TYPES := c.TYPES ++ dts} ∧
      ns.length = sts.length ∧
      (∃ before after : Nat,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit,
            SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6»
              {c with TYPES := c.TYPES ++ dts}
              c.TYPES.length ns sts⟩)
          before (.success (.of ())) after) := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Rectype_ok_clauses c (.RecT sts)) ())
      start (.success (.of c')) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.firstSuccess_success_iff
        (SpecTec.Rectype_ok_clauses c (.RecT sts)) ()
        start (.of c') finish).1 hbody
    unfold SpecTec.Rectype_ok_clauses at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«Rectype_ok:clause:0» at h0
      dsimp only at h0
      cases h0 with
      | bind_success hrange h1 =>
        rename_i ns
        dsimp only at h1
        cases h1 with
        | bind_success hroll h2 =>
          dsimp only at h2
          cases h2 with
          | bind_success hsubst h3 =>
            rename_i dts
            dsimp only at h3
            cases h3 with
            | bind_success hiter5 h4 =>
              dsimp only at h4
              cases h4 with
              | bind_success hguard h5 =>
                cases hguard with
                | guard_true hlen =>
                  dsimp only at h5
                  cases h5 with
                  | bind_success hiter6 h6 =>
                    rename_i v
                    cases h6
                    cases v
                    refine ⟨ns, dts, rfl, hlen.symm, ?_⟩
                    exact ⟨_, _, hiter6⟩
    | next _ hrest => cases hrest

theorem rectype_ok_pairs_static_lt
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish) :
    ∃ ns : List SpecTec.n, ∃ dts : List SpecTec.deftype,
      c' = {c with TYPES := c.TYPES ++ dts} ∧
      ns.length = sts.length ∧
      (∀ n fin hts strt,
        (n, SpecTec.subtype.SubT fin hts strt) ∈ List.zip ns sts →
        ∀ y : SpecTec.typeidx,
          .VarHT (.StatX y) ∈ hts → y < c.TYPES.length + n) := by
  obtain ⟨ns, dts, hc, hlen, before, after, hiter⟩ :=
    rectype_ok_extract_sub_iter c c' sts start finish h
  refine ⟨ns, dts, hc, hlen, ?_⟩
  intro n fin hts strt hpair y hy
  exact rectype_sub_iter_static_lt
    {c with TYPES := c.TYPES ++ dts} c.TYPES.length ns sts
    before after hiter n fin hts strt hpair y hy

theorem range_total (k n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List Nat, SpecTec.SpecTecCall.«$range» k⟩)
      n (.success (.of (List.range k))) n := by
  induction k with
  | zero =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$range_clauses» 0) ())
        n (.success (.of (List.range 0))) n
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$range:clause:0» 0)
        n (.success (.of (List.range 0))) n
      unfold SpecTec.«$range:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure []
  | succ k ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.«$range_clauses» (k+1)) ())
        n (.success (.of (List.range (k+1)))) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$range:clause:0» (k+1)) n .unmatch n
        unfold SpecTec.«$range:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$range:clause:1» (k+1))
          n (.success (.of (List.range (k+1)))) n
        unfold SpecTec.«$range:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by simp)
        · apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true (by simp)
          · simpa [List.range_succ, Int.toNat?] using
              (SpecTecExecution.Eval.bind_success ih
                (SpecTecExecution.Eval.pure (List.range k ++ [k])))

theorem range_success_eq
    (k : Nat) (ns : List Nat) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List Nat, SpecTec.SpecTecCall.«$range» k⟩)
      start (.success (.of ns)) finish) :
    ns = List.range k := by
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request x y hp
    cases hp
  obtain ⟨hout, _⟩ := SpecTecExecution.eval_deterministic hdet h
    (range_total k start)
  cases hout
  rfl

end properties.wasm_module_ok.MatchHeaptypeBasic
