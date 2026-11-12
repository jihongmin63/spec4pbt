import properties.wasm_module_not_ok.InitialContextValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FreeRefsValidation

private abbrev emptyFree :=
  properties.wasm_module_not_ok.Rejection.emptyFree

def singletonFuncFree (x : SpecTec.funcidx) : SpecTec.free :=
  { emptyFree with FUNCS := .«`{ % `}» [x] }

theorem free_idx_total (x : SpecTec.funcidx) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.set SpecTec.funcidx,
        SpecTec.Call.«$free_idx» x⟩)
      n (.success (.of (SpecTec.set.«`{ % `}» [x]))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$free_idx_clauses» x))
    n (.success (.of (SpecTec.set.«`{ % `}» [x]))) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$free_idx:clause:0» x)
    n (.success (.of (SpecTec.set.«`{ % `}» [x]))) n
  exact SpecTecExecution.Eval.pure _

theorem update_funcs_total (xs : List SpecTec.funcidx) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$update_funcs» (SpecTec.set.«`{ % `}» xs)⟩)
      n (.success (.of { emptyFree with FUNCS := .«`{ % `}» xs })) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$update_funcs_clauses» (SpecTec.set.«`{ % `}» xs)))
    n (.success (.of { emptyFree with FUNCS := .«`{ % `}» xs })) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$update_funcs:clause:0» (SpecTec.set.«`{ % `}» xs))
    n (.success (.of { emptyFree with FUNCS := .«`{ % `}» xs })) n
  unfold SpecTec.«$update_funcs:clause:0»
  apply SpecTecExecution.Eval.bind_success
    (properties.wasm_module_not_ok.Rejection.free_empty_total n)
  exact SpecTecExecution.Eval.pure _

theorem ref_func_free_clause_success (x : SpecTec.funcidx) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:51» (.«REF.FUNC» x))
      n (.success (.of (singletonFuncFree x))) n := by
  unfold SpecTec.«$free_instr:clause:51»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success (free_idx_total x n)
  apply SpecTecExecution.Eval.bind_success (update_funcs_total [x] n)
  exact SpecTecExecution.Eval.pure _

theorem in_singleton_func_free (x : SpecTec.funcidx) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$in_set»
        SpecTec.funcidx x (singletonFuncFree x).FUNCS⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$in_set_clauses» SpecTec.funcidx x
        (SpecTec.set.«`{ % `}» [x])))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$in_set:clause:0» SpecTec.funcidx x
      (SpecTec.set.«`{ % `}» [x]))
    n (.success (.of true)) n
  simpa [SpecTec.«$in_set:clause:0»] using
    (SpecTecExecution.Eval.pure true :
      SpecTecExecution.Eval SpecTec.Body
        (.pure true) n (.success (.of true)) n)

theorem ref_func_free_total (x : SpecTec.funcidx) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_instr» (.«REF.FUNC» x)⟩)
      n (.success (.of (singletonFuncFree x))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$free_instr_clauses» (.«REF.FUNC» x)))
    n (.success (.of (singletonFuncFree x))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:0» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:UNREACHABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:1» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:NOP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:2» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:3» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:4» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:SELECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:5» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BLOCK»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:6» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOOP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:7» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:IF % % ELSE %»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:8» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:9» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_IF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:10» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_TABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:11» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:11»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:12» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:13» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:13»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:14» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:14»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST_FAIL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:15» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:15»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:16» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:16»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:17» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:17»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_INDIRECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:18» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:18»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:19» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:19»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:20» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:20»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:21» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:21»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_INDIRECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:22» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:22»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:23» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:23»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:24» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:24»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TRY_TABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:25» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:25»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:26» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:26»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:27» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:27»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.TEE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:28» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:28»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:29» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:29»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:30» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:30»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:31» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:31»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:32» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:32»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SIZE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:33» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:33»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:34» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:34»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.FILL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:35» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:35»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.COPY»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:36» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:36»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.INIT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:37» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:37»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ELEM.DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:38» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:38»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOAD»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:39» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:39»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STORE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:40» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:40»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:41» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:41»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:42» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:42»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD_LANE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:43» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:43»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE_LANE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:44» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:44»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.SIZE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:45» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:45»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.GROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:46» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:46»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.FILL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:47» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:47»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.COPY»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:48» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:48»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.INIT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:49» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:49»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DATA.DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_instr:clause:50» (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$free_instr:clause:50»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_success
  exact ref_func_free_clause_success x n

end properties.wasm_module_ok.FreeRefsValidation
