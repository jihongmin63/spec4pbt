import properties.wasm_module_ok.RefFuncValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.InstrRefDispatch

theorem ref_func_dispatch_of_clause
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (result : SpecTec.inferinstrtype)
    (n finalSupply : Nat)
    (hclause : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:51» c irt (.«REF.FUNC» x))
      n (.success (.of result)) finalSupply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«REF.FUNC» x)⟩)
      n (.success (.of result)) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Instr_ok_clauses c irt (.«REF.FUNC» x)))
    n (.success (.of result)) finalSupply
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:0» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:UNREACHABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:1» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:NOP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:2» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:3» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:4» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:SELECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:5» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BLOCK»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:6» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOOP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:7» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:IF % % ELSE %»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:8» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:9» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_IF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:10» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_TABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:11» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:11»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:12» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:13» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:13»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:14» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:14»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST_FAIL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:15» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:15»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:16» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:16»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:17» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:17»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_INDIRECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:18» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:18»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:19» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:19»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:20» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:20»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:21» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:21»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_INDIRECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:22» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:22»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:23» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:23»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:24» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:24»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TRY_TABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:25» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:25»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:26» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:26»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:27» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:27»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.TEE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:28» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:28»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:29» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:29»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:30» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:30»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:31» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:31»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:32» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:32»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SIZE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:33» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:33»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:34» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:34»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.FILL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:35» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:35»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.COPY»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:36» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:36»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.INIT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:37» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:37»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ELEM.DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:38» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:38»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOAD»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:39» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:39»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STORE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:40» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:40»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:41» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:41»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:42» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:42»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD_LANE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:43» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:43»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE_LANE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:44» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:44»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.SIZE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:45» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:45»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.GROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:46» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:46»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.FILL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:47» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:47»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.COPY»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:48» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:48»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.INIT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:49» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:49»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DATA.DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:50» c irt (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:50»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  exact SpecTecExecution.tryClauses_cons_success hclause

theorem ref_func_clause_of_dispatch
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (result : SpecTec.inferinstrtype)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«REF.FUNC» x)⟩)
      n (.success (.of result)) finalSupply) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:51» c irt (.«REF.FUNC» x))
      n (.success (.of result)) finalSupply := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Instr_ok_clauses c irt (.«REF.FUNC» x)))
      n (.success (.of result)) finalSupply at hbody
    have hunmatch : SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Instr_ok:clause:0» c irt (.«REF.FUNC» x)) n .unmatch n := by
      unfold SpecTec.«Instr_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:UNREACHABLE»]))
    cases hbody with
    | orElse_success hfirst =>
        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
    | orElse_unmatch _ hbody =>
      have hunmatch : SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Instr_ok:clause:1» c irt (.«REF.FUNC» x)) n .unmatch n := by
        unfold SpecTec.«Instr_ok:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:NOP»]))
      cases hbody with
      | orElse_success hfirst =>
          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
      | orElse_unmatch _ hbody =>
        have hunmatch : SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«Instr_ok:clause:2» c irt (.«REF.FUNC» x)) n .unmatch n := by
          unfold SpecTec.«Instr_ok:clause:2»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DROP»]))
        cases hbody with
        | orElse_success hfirst =>
            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
        | orElse_unmatch _ hbody =>
          have hunmatch : SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«Instr_ok:clause:3» c irt (.«REF.FUNC» x)) n .unmatch n := by
            unfold SpecTec.«Instr_ok:clause:3»
            exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false (by simp))
          cases hbody with
          | orElse_success hfirst =>
              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
          | orElse_unmatch _ hbody =>
            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                (SpecTec.«Instr_ok:clause:4» c irt (.«REF.FUNC» x)) n .unmatch n := by
              unfold SpecTec.«Instr_ok:clause:4»
              exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:SELECT»]))
            cases hbody with
            | orElse_success hfirst =>
                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
            | orElse_unmatch _ hbody =>
              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                  (SpecTec.«Instr_ok:clause:5» c irt (.«REF.FUNC» x)) n .unmatch n := by
                unfold SpecTec.«Instr_ok:clause:5»
                exact SpecTecExecution.Eval.bind_unmatch
                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BLOCK»]))
              cases hbody with
              | orElse_success hfirst =>
                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
              | orElse_unmatch _ hbody =>
                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                    (SpecTec.«Instr_ok:clause:6» c irt (.«REF.FUNC» x)) n .unmatch n := by
                  unfold SpecTec.«Instr_ok:clause:6»
                  exact SpecTecExecution.Eval.bind_unmatch
                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOOP»]))
                cases hbody with
                | orElse_success hfirst =>
                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                | orElse_unmatch _ hbody =>
                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                      (SpecTec.«Instr_ok:clause:7» c irt (.«REF.FUNC» x)) n .unmatch n := by
                    unfold SpecTec.«Instr_ok:clause:7»
                    exact SpecTecExecution.Eval.bind_unmatch
                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:IF % % ELSE %»]))
                  cases hbody with
                  | orElse_success hfirst =>
                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                  | orElse_unmatch _ hbody =>
                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                        (SpecTec.«Instr_ok:clause:8» c irt (.«REF.FUNC» x)) n .unmatch n := by
                      unfold SpecTec.«Instr_ok:clause:8»
                      exact SpecTecExecution.Eval.bind_unmatch
                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR»]))
                    cases hbody with
                    | orElse_success hfirst =>
                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                    | orElse_unmatch _ hbody =>
                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                          (SpecTec.«Instr_ok:clause:9» c irt (.«REF.FUNC» x)) n .unmatch n := by
                        unfold SpecTec.«Instr_ok:clause:9»
                        exact SpecTecExecution.Eval.bind_unmatch
                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_IF»]))
                      cases hbody with
                      | orElse_success hfirst =>
                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                      | orElse_unmatch _ hbody =>
                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                            (SpecTec.«Instr_ok:clause:10» c irt (.«REF.FUNC» x)) n .unmatch n := by
                          unfold SpecTec.«Instr_ok:clause:10»
                          exact SpecTecExecution.Eval.bind_unmatch
                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_TABLE»]))
                        cases hbody with
                        | orElse_success hfirst =>
                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                        | orElse_unmatch _ hbody =>
                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                              (SpecTec.«Instr_ok:clause:11» c irt (.«REF.FUNC» x)) n .unmatch n := by
                            unfold SpecTec.«Instr_ok:clause:11»
                            exact SpecTecExecution.Eval.bind_unmatch
                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NULL»]))
                          cases hbody with
                          | orElse_success hfirst =>
                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                          | orElse_unmatch _ hbody =>
                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                (SpecTec.«Instr_ok:clause:12» c irt (.«REF.FUNC» x)) n .unmatch n := by
                              unfold SpecTec.«Instr_ok:clause:12»
                              exact SpecTecExecution.Eval.bind_unmatch
                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NON_NULL»]))
                            cases hbody with
                            | orElse_success hfirst =>
                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                            | orElse_unmatch _ hbody =>
                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                  (SpecTec.«Instr_ok:clause:13» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                unfold SpecTec.«Instr_ok:clause:13»
                                exact SpecTecExecution.Eval.bind_unmatch
                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST»]))
                              cases hbody with
                              | orElse_success hfirst =>
                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                              | orElse_unmatch _ hbody =>
                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                    (SpecTec.«Instr_ok:clause:14» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                  unfold SpecTec.«Instr_ok:clause:14»
                                  exact SpecTecExecution.Eval.bind_unmatch
                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST_FAIL»]))
                                cases hbody with
                                | orElse_success hfirst =>
                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                | orElse_unmatch _ hbody =>
                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                      (SpecTec.«Instr_ok:clause:15» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                    unfold SpecTec.«Instr_ok:clause:15»
                                    exact SpecTecExecution.Eval.bind_unmatch
                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL»]))
                                  cases hbody with
                                  | orElse_success hfirst =>
                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                  | orElse_unmatch _ hbody =>
                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                        (SpecTec.«Instr_ok:clause:16» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                      unfold SpecTec.«Instr_ok:clause:16»
                                      exact SpecTecExecution.Eval.bind_unmatch
                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_REF»]))
                                    cases hbody with
                                    | orElse_success hfirst =>
                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                    | orElse_unmatch _ hbody =>
                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                          (SpecTec.«Instr_ok:clause:17» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                        unfold SpecTec.«Instr_ok:clause:17»
                                        exact SpecTecExecution.Eval.bind_unmatch
                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_INDIRECT»]))
                                      cases hbody with
                                      | orElse_success hfirst =>
                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                      | orElse_unmatch _ hbody =>
                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                            (SpecTec.«Instr_ok:clause:18» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                          unfold SpecTec.«Instr_ok:clause:18»
                                          exact SpecTecExecution.Eval.bind_unmatch
                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN»]))
                                        cases hbody with
                                        | orElse_success hfirst =>
                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                        | orElse_unmatch _ hbody =>
                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                              (SpecTec.«Instr_ok:clause:19» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                            unfold SpecTec.«Instr_ok:clause:19»
                                            exact SpecTecExecution.Eval.bind_unmatch
                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL»]))
                                          cases hbody with
                                          | orElse_success hfirst =>
                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                          | orElse_unmatch _ hbody =>
                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                (SpecTec.«Instr_ok:clause:20» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                              unfold SpecTec.«Instr_ok:clause:20»
                                              exact SpecTecExecution.Eval.bind_unmatch
                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_REF»]))
                                            cases hbody with
                                            | orElse_success hfirst =>
                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                            | orElse_unmatch _ hbody =>
                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                  (SpecTec.«Instr_ok:clause:21» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                unfold SpecTec.«Instr_ok:clause:21»
                                                exact SpecTecExecution.Eval.bind_unmatch
                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_INDIRECT»]))
                                              cases hbody with
                                              | orElse_success hfirst =>
                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                              | orElse_unmatch _ hbody =>
                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                    (SpecTec.«Instr_ok:clause:22» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                  unfold SpecTec.«Instr_ok:clause:22»
                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW»]))
                                                cases hbody with
                                                | orElse_success hfirst =>
                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                | orElse_unmatch _ hbody =>
                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                      (SpecTec.«Instr_ok:clause:23» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                    unfold SpecTec.«Instr_ok:clause:23»
                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW_REF»]))
                                                  cases hbody with
                                                  | orElse_success hfirst =>
                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                  | orElse_unmatch _ hbody =>
                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                        (SpecTec.«Instr_ok:clause:24» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                      unfold SpecTec.«Instr_ok:clause:24»
                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TRY_TABLE»]))
                                                    cases hbody with
                                                    | orElse_success hfirst =>
                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                    | orElse_unmatch _ hbody =>
                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                          (SpecTec.«Instr_ok:clause:25» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                        unfold SpecTec.«Instr_ok:clause:25»
                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.GET»]))
                                                      cases hbody with
                                                      | orElse_success hfirst =>
                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                      | orElse_unmatch _ hbody =>
                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                            (SpecTec.«Instr_ok:clause:26» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                          unfold SpecTec.«Instr_ok:clause:26»
                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.SET»]))
                                                        cases hbody with
                                                        | orElse_success hfirst =>
                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                        | orElse_unmatch _ hbody =>
                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                              (SpecTec.«Instr_ok:clause:27» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                            unfold SpecTec.«Instr_ok:clause:27»
                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.TEE»]))
                                                          cases hbody with
                                                          | orElse_success hfirst =>
                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                          | orElse_unmatch _ hbody =>
                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                (SpecTec.«Instr_ok:clause:28» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                              unfold SpecTec.«Instr_ok:clause:28»
                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
                                                            cases hbody with
                                                            | orElse_success hfirst =>
                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                            | orElse_unmatch _ hbody =>
                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                  (SpecTec.«Instr_ok:clause:29» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                unfold SpecTec.«Instr_ok:clause:29»
                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.SET»]))
                                                              cases hbody with
                                                              | orElse_success hfirst =>
                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                              | orElse_unmatch _ hbody =>
                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                    (SpecTec.«Instr_ok:clause:30» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                  unfold SpecTec.«Instr_ok:clause:30»
                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GET»]))
                                                                cases hbody with
                                                                | orElse_success hfirst =>
                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                | orElse_unmatch _ hbody =>
                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                      (SpecTec.«Instr_ok:clause:31» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                    unfold SpecTec.«Instr_ok:clause:31»
                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SET»]))
                                                                  cases hbody with
                                                                  | orElse_success hfirst =>
                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                  | orElse_unmatch _ hbody =>
                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                        (SpecTec.«Instr_ok:clause:32» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                      unfold SpecTec.«Instr_ok:clause:32»
                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SIZE»]))
                                                                    cases hbody with
                                                                    | orElse_success hfirst =>
                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                    | orElse_unmatch _ hbody =>
                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                          (SpecTec.«Instr_ok:clause:33» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                        unfold SpecTec.«Instr_ok:clause:33»
                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GROW»]))
                                                                      cases hbody with
                                                                      | orElse_success hfirst =>
                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                      | orElse_unmatch _ hbody =>
                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                            (SpecTec.«Instr_ok:clause:34» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                          unfold SpecTec.«Instr_ok:clause:34»
                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.FILL»]))
                                                                        cases hbody with
                                                                        | orElse_success hfirst =>
                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                        | orElse_unmatch _ hbody =>
                                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                              (SpecTec.«Instr_ok:clause:35» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                            unfold SpecTec.«Instr_ok:clause:35»
                                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.COPY»]))
                                                                          cases hbody with
                                                                          | orElse_success hfirst =>
                                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                          | orElse_unmatch _ hbody =>
                                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                (SpecTec.«Instr_ok:clause:36» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                              unfold SpecTec.«Instr_ok:clause:36»
                                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.INIT»]))
                                                                            cases hbody with
                                                                            | orElse_success hfirst =>
                                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                            | orElse_unmatch _ hbody =>
                                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                  (SpecTec.«Instr_ok:clause:37» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                unfold SpecTec.«Instr_ok:clause:37»
                                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ELEM.DROP»]))
                                                                              cases hbody with
                                                                              | orElse_success hfirst =>
                                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                              | orElse_unmatch _ hbody =>
                                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                    (SpecTec.«Instr_ok:clause:38» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                  unfold SpecTec.«Instr_ok:clause:38»
                                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOAD»]))
                                                                                cases hbody with
                                                                                | orElse_success hfirst =>
                                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                | orElse_unmatch _ hbody =>
                                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                      (SpecTec.«Instr_ok:clause:39» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                    unfold SpecTec.«Instr_ok:clause:39»
                                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STORE»]))
                                                                                  cases hbody with
                                                                                  | orElse_success hfirst =>
                                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                  | orElse_unmatch _ hbody =>
                                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                        (SpecTec.«Instr_ok:clause:40» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                      unfold SpecTec.«Instr_ok:clause:40»
                                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD»]))
                                                                                    cases hbody with
                                                                                    | orElse_success hfirst =>
                                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                    | orElse_unmatch _ hbody =>
                                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                          (SpecTec.«Instr_ok:clause:41» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                        unfold SpecTec.«Instr_ok:clause:41»
                                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE»]))
                                                                                      cases hbody with
                                                                                      | orElse_success hfirst =>
                                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                      | orElse_unmatch _ hbody =>
                                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                            (SpecTec.«Instr_ok:clause:42» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                          unfold SpecTec.«Instr_ok:clause:42»
                                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD_LANE»]))
                                                                                        cases hbody with
                                                                                        | orElse_success hfirst =>
                                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                        | orElse_unmatch _ hbody =>
                                                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                              (SpecTec.«Instr_ok:clause:43» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                            unfold SpecTec.«Instr_ok:clause:43»
                                                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE_LANE»]))
                                                                                          cases hbody with
                                                                                          | orElse_success hfirst =>
                                                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                          | orElse_unmatch _ hbody =>
                                                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                (SpecTec.«Instr_ok:clause:44» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                              unfold SpecTec.«Instr_ok:clause:44»
                                                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.SIZE»]))
                                                                                            cases hbody with
                                                                                            | orElse_success hfirst =>
                                                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                            | orElse_unmatch _ hbody =>
                                                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                  (SpecTec.«Instr_ok:clause:45» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                unfold SpecTec.«Instr_ok:clause:45»
                                                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.GROW»]))
                                                                                              cases hbody with
                                                                                              | orElse_success hfirst =>
                                                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                              | orElse_unmatch _ hbody =>
                                                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                    (SpecTec.«Instr_ok:clause:46» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                  unfold SpecTec.«Instr_ok:clause:46»
                                                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.FILL»]))
                                                                                                cases hbody with
                                                                                                | orElse_success hfirst =>
                                                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                | orElse_unmatch _ hbody =>
                                                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                      (SpecTec.«Instr_ok:clause:47» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                    unfold SpecTec.«Instr_ok:clause:47»
                                                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.COPY»]))
                                                                                                  cases hbody with
                                                                                                  | orElse_success hfirst =>
                                                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                  | orElse_unmatch _ hbody =>
                                                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                        (SpecTec.«Instr_ok:clause:48» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                      unfold SpecTec.«Instr_ok:clause:48»
                                                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.INIT»]))
                                                                                                    cases hbody with
                                                                                                    | orElse_success hfirst =>
                                                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                    | orElse_unmatch _ hbody =>
                                                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                          (SpecTec.«Instr_ok:clause:49» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                        unfold SpecTec.«Instr_ok:clause:49»
                                                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DATA.DROP»]))
                                                                                                      cases hbody with
                                                                                                      | orElse_success hfirst =>
                                                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                      | orElse_unmatch _ hbody =>
                                                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                            (SpecTec.«Instr_ok:clause:50» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                          unfold SpecTec.«Instr_ok:clause:50»
                                                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
                                                                                                        cases hbody with
                                                                                                        | orElse_success hfirst =>
                                                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                        | orElse_unmatch _ hbody =>
                                                                                                          cases hbody with
                                                                                                          | orElse_success hclause => exact hclause
                                                                                                          | orElse_unmatch _ hbody =>
                                                                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                (SpecTec.«Instr_ok:clause:52» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                              unfold SpecTec.«Instr_ok:clause:52»
                                                                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.IS_NULL»]))
                                                                                                            cases hbody with
                                                                                                            | orElse_success hfirst =>
                                                                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                            | orElse_unmatch _ hbody =>
                                                                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                  (SpecTec.«Instr_ok:clause:53» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                unfold SpecTec.«Instr_ok:clause:53»
                                                                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.AS_NON_NULL»]))
                                                                                                              cases hbody with
                                                                                                              | orElse_success hfirst =>
                                                                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                              | orElse_unmatch _ hbody =>
                                                                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                    (SpecTec.«Instr_ok:clause:54» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                  unfold SpecTec.«Instr_ok:clause:54»
                                                                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.TEST»]))
                                                                                                                cases hbody with
                                                                                                                | orElse_success hfirst =>
                                                                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                | orElse_unmatch _ hbody =>
                                                                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                      (SpecTec.«Instr_ok:clause:55» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                    unfold SpecTec.«Instr_ok:clause:55»
                                                                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.CAST»]))
                                                                                                                  cases hbody with
                                                                                                                  | orElse_success hfirst =>
                                                                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                  | orElse_unmatch _ hbody =>
                                                                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                        (SpecTec.«Instr_ok:clause:56» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                      unfold SpecTec.«Instr_ok:clause:56»
                                                                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.EQ»]))
                                                                                                                    cases hbody with
                                                                                                                    | orElse_success hfirst =>
                                                                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                    | orElse_unmatch _ hbody =>
                                                                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                          (SpecTec.«Instr_ok:clause:57» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                        unfold SpecTec.«Instr_ok:clause:57»
                                                                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.I31»]))
                                                                                                                      cases hbody with
                                                                                                                      | orElse_success hfirst =>
                                                                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                      | orElse_unmatch _ hbody =>
                                                                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                            (SpecTec.«Instr_ok:clause:58» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                          unfold SpecTec.«Instr_ok:clause:58»
                                                                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:I31.GET»]))
                                                                                                                        cases hbody with
                                                                                                                        | orElse_success hfirst =>
                                                                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                        | orElse_unmatch _ hbody =>
                                                                                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                              (SpecTec.«Instr_ok:clause:59» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                            unfold SpecTec.«Instr_ok:clause:59»
                                                                                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
                                                                                                                          cases hbody with
                                                                                                                          | orElse_success hfirst =>
                                                                                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                          | orElse_unmatch _ hbody =>
                                                                                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                (SpecTec.«Instr_ok:clause:60» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                              unfold SpecTec.«Instr_ok:clause:60»
                                                                                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
                                                                                                                            cases hbody with
                                                                                                                            | orElse_success hfirst =>
                                                                                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                            | orElse_unmatch _ hbody =>
                                                                                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                  (SpecTec.«Instr_ok:clause:61» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                unfold SpecTec.«Instr_ok:clause:61»
                                                                                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.GET»]))
                                                                                                                              cases hbody with
                                                                                                                              | orElse_success hfirst =>
                                                                                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                              | orElse_unmatch _ hbody =>
                                                                                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                    (SpecTec.«Instr_ok:clause:62» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                  unfold SpecTec.«Instr_ok:clause:62»
                                                                                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.GET»]))
                                                                                                                                cases hbody with
                                                                                                                                | orElse_success hfirst =>
                                                                                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                | orElse_unmatch _ hbody =>
                                                                                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                      (SpecTec.«Instr_ok:clause:63» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                    unfold SpecTec.«Instr_ok:clause:63»
                                                                                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.SET»]))
                                                                                                                                  cases hbody with
                                                                                                                                  | orElse_success hfirst =>
                                                                                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                  | orElse_unmatch _ hbody =>
                                                                                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                        (SpecTec.«Instr_ok:clause:64» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                      unfold SpecTec.«Instr_ok:clause:64»
                                                                                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
                                                                                                                                    cases hbody with
                                                                                                                                    | orElse_success hfirst =>
                                                                                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                    | orElse_unmatch _ hbody =>
                                                                                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                          (SpecTec.«Instr_ok:clause:65» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                        unfold SpecTec.«Instr_ok:clause:65»
                                                                                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
                                                                                                                                      cases hbody with
                                                                                                                                      | orElse_success hfirst =>
                                                                                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                      | orElse_unmatch _ hbody =>
                                                                                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                            (SpecTec.«Instr_ok:clause:66» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                          unfold SpecTec.«Instr_ok:clause:66»
                                                                                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»]))
                                                                                                                                        cases hbody with
                                                                                                                                        | orElse_success hfirst =>
                                                                                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                        | orElse_unmatch _ hbody =>
                                                                                                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                              (SpecTec.«Instr_ok:clause:67» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                            unfold SpecTec.«Instr_ok:clause:67»
                                                                                                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_ELEM»]))
                                                                                                                                          cases hbody with
                                                                                                                                          | orElse_success hfirst =>
                                                                                                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                          | orElse_unmatch _ hbody =>
                                                                                                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                (SpecTec.«Instr_ok:clause:68» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                              unfold SpecTec.«Instr_ok:clause:68»
                                                                                                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_DATA»]))
                                                                                                                                            cases hbody with
                                                                                                                                            | orElse_success hfirst =>
                                                                                                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                            | orElse_unmatch _ hbody =>
                                                                                                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                  (SpecTec.«Instr_ok:clause:69» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                unfold SpecTec.«Instr_ok:clause:69»
                                                                                                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.GET»]))
                                                                                                                                              cases hbody with
                                                                                                                                              | orElse_success hfirst =>
                                                                                                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                              | orElse_unmatch _ hbody =>
                                                                                                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                    (SpecTec.«Instr_ok:clause:70» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                  unfold SpecTec.«Instr_ok:clause:70»
                                                                                                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.GET»]))
                                                                                                                                                cases hbody with
                                                                                                                                                | orElse_success hfirst =>
                                                                                                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                | orElse_unmatch _ hbody =>
                                                                                                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                      (SpecTec.«Instr_ok:clause:71» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                    unfold SpecTec.«Instr_ok:clause:71»
                                                                                                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.SET»]))
                                                                                                                                                  cases hbody with
                                                                                                                                                  | orElse_success hfirst =>
                                                                                                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                  | orElse_unmatch _ hbody =>
                                                                                                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                        (SpecTec.«Instr_ok:clause:72» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                      unfold SpecTec.«Instr_ok:clause:72»
                                                                                                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.LEN»]))
                                                                                                                                                    cases hbody with
                                                                                                                                                    | orElse_success hfirst =>
                                                                                                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                    | orElse_unmatch _ hbody =>
                                                                                                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                          (SpecTec.«Instr_ok:clause:73» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                        unfold SpecTec.«Instr_ok:clause:73»
                                                                                                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.COPY»]))
                                                                                                                                                      cases hbody with
                                                                                                                                                      | orElse_success hfirst =>
                                                                                                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                      | orElse_unmatch _ hbody =>
                                                                                                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                            (SpecTec.«Instr_ok:clause:74» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                          unfold SpecTec.«Instr_ok:clause:74»
                                                                                                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.FILL»]))
                                                                                                                                                        cases hbody with
                                                                                                                                                        | orElse_success hfirst =>
                                                                                                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                        | orElse_unmatch _ hbody =>
                                                                                                                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                              (SpecTec.«Instr_ok:clause:75» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                            unfold SpecTec.«Instr_ok:clause:75»
                                                                                                                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.INIT_DATA»]))
                                                                                                                                                          cases hbody with
                                                                                                                                                          | orElse_success hfirst =>
                                                                                                                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                          | orElse_unmatch _ hbody =>
                                                                                                                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                (SpecTec.«Instr_ok:clause:76» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                              unfold SpecTec.«Instr_ok:clause:76»
                                                                                                                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.INIT_ELEM»]))
                                                                                                                                                            cases hbody with
                                                                                                                                                            | orElse_success hfirst =>
                                                                                                                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                            | orElse_unmatch _ hbody =>
                                                                                                                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                  (SpecTec.«Instr_ok:clause:77» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                unfold SpecTec.«Instr_ok:clause:77»
                                                                                                                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:EXTERN.CONVERT»]))
                                                                                                                                                              cases hbody with
                                                                                                                                                              | orElse_success hfirst =>
                                                                                                                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                              | orElse_unmatch _ hbody =>
                                                                                                                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                    (SpecTec.«Instr_ok:clause:78» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                  unfold SpecTec.«Instr_ok:clause:78»
                                                                                                                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CONST»]))
                                                                                                                                                                cases hbody with
                                                                                                                                                                | orElse_success hfirst =>
                                                                                                                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                | orElse_unmatch _ hbody =>
                                                                                                                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                      (SpecTec.«Instr_ok:clause:79» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                    unfold SpecTec.«Instr_ok:clause:79»
                                                                                                                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TEST»]))
                                                                                                                                                                  cases hbody with
                                                                                                                                                                  | orElse_success hfirst =>
                                                                                                                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                  | orElse_unmatch _ hbody =>
                                                                                                                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                        (SpecTec.«Instr_ok:clause:80» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                      unfold SpecTec.«Instr_ok:clause:80»
                                                                                                                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:COMPARE»]))
                                                                                                                                                                    cases hbody with
                                                                                                                                                                    | orElse_success hfirst =>
                                                                                                                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                    | orElse_unmatch _ hbody =>
                                                                                                                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                          (SpecTec.«Instr_ok:clause:81» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                        unfold SpecTec.«Instr_ok:clause:81»
                                                                                                                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:UNARY»]))
                                                                                                                                                                      cases hbody with
                                                                                                                                                                      | orElse_success hfirst =>
                                                                                                                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                      | orElse_unmatch _ hbody =>
                                                                                                                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                            (SpecTec.«Instr_ok:clause:82» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                          unfold SpecTec.«Instr_ok:clause:82»
                                                                                                                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BINOP»]))
                                                                                                                                                                        cases hbody with
                                                                                                                                                                        | orElse_success hfirst =>
                                                                                                                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                        | orElse_unmatch _ hbody =>
                                                                                                                                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                              (SpecTec.«Instr_ok:clause:83» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                            unfold SpecTec.«Instr_ok:clause:83»
                                                                                                                                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CONVERT»]))
                                                                                                                                                                          cases hbody with
                                                                                                                                                                          | orElse_success hfirst =>
                                                                                                                                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                          | orElse_unmatch _ hbody =>
                                                                                                                                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                (SpecTec.«Instr_ok:clause:84» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                              unfold SpecTec.«Instr_ok:clause:84»
                                                                                                                                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
                                                                                                                                                                            cases hbody with
                                                                                                                                                                            | orElse_success hfirst =>
                                                                                                                                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                            | orElse_unmatch _ hbody =>
                                                                                                                                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                  (SpecTec.«Instr_ok:clause:85» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                unfold SpecTec.«Instr_ok:clause:85»
                                                                                                                                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.TEST»]))
                                                                                                                                                                              cases hbody with
                                                                                                                                                                              | orElse_success hfirst =>
                                                                                                                                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                              | orElse_unmatch _ hbody =>
                                                                                                                                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                    (SpecTec.«Instr_ok:clause:86» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                  unfold SpecTec.«Instr_ok:clause:86»
                                                                                                                                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.UNARY»]))
                                                                                                                                                                                cases hbody with
                                                                                                                                                                                | orElse_success hfirst =>
                                                                                                                                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                | orElse_unmatch _ hbody =>
                                                                                                                                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                      (SpecTec.«Instr_ok:clause:87» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                    unfold SpecTec.«Instr_ok:clause:87»
                                                                                                                                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.BINARY»]))
                                                                                                                                                                                  cases hbody with
                                                                                                                                                                                  | orElse_success hfirst =>
                                                                                                                                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                  | orElse_unmatch _ hbody =>
                                                                                                                                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                        (SpecTec.«Instr_ok:clause:88» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                      unfold SpecTec.«Instr_ok:clause:88»
                                                                                                                                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.TERNARY»]))
                                                                                                                                                                                    cases hbody with
                                                                                                                                                                                    | orElse_success hfirst =>
                                                                                                                                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                    | orElse_unmatch _ hbody =>
                                                                                                                                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                          (SpecTec.«Instr_ok:clause:89» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                        unfold SpecTec.«Instr_ok:clause:89»
                                                                                                                                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.COMPARE»]))
                                                                                                                                                                                      cases hbody with
                                                                                                                                                                                      | orElse_success hfirst =>
                                                                                                                                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                      | orElse_unmatch _ hbody =>
                                                                                                                                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                            (SpecTec.«Instr_ok:clause:90» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                          unfold SpecTec.«Instr_ok:clause:90»
                                                                                                                                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.CONVERT»]))
                                                                                                                                                                                        cases hbody with
                                                                                                                                                                                        | orElse_success hfirst =>
                                                                                                                                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                        | orElse_unmatch _ hbody =>
                                                                                                                                                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                              (SpecTec.«Instr_ok:clause:91» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                            unfold SpecTec.«Instr_ok:clause:91»
                                                                                                                                                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.SHIFT»]))
                                                                                                                                                                                          cases hbody with
                                                                                                                                                                                          | orElse_success hfirst =>
                                                                                                                                                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                          | orElse_unmatch _ hbody =>
                                                                                                                                                                                            have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                                (SpecTec.«Instr_ok:clause:92» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                              unfold SpecTec.«Instr_ok:clause:92»
                                                                                                                                                                                              exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                                (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.BITMASK»]))
                                                                                                                                                                                            cases hbody with
                                                                                                                                                                                            | orElse_success hfirst =>
                                                                                                                                                                                                exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                            | orElse_unmatch _ hbody =>
                                                                                                                                                                                              have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                                  (SpecTec.«Instr_ok:clause:93» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                                unfold SpecTec.«Instr_ok:clause:93»
                                                                                                                                                                                                exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                                  (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.TESTBITS»]))
                                                                                                                                                                                              cases hbody with
                                                                                                                                                                                              | orElse_success hfirst =>
                                                                                                                                                                                                  exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                              | orElse_unmatch _ hbody =>
                                                                                                                                                                                                have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                                    (SpecTec.«Instr_ok:clause:94» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                                  unfold SpecTec.«Instr_ok:clause:94»
                                                                                                                                                                                                  exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                                    (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.UNARYBITS»]))
                                                                                                                                                                                                cases hbody with
                                                                                                                                                                                                | orElse_success hfirst =>
                                                                                                                                                                                                    exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                                | orElse_unmatch _ hbody =>
                                                                                                                                                                                                  have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                                      (SpecTec.«Instr_ok:clause:95» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                                    unfold SpecTec.«Instr_ok:clause:95»
                                                                                                                                                                                                    exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                                      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.BINARYBITS»]))
                                                                                                                                                                                                  cases hbody with
                                                                                                                                                                                                  | orElse_success hfirst =>
                                                                                                                                                                                                      exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                                  | orElse_unmatch _ hbody =>
                                                                                                                                                                                                    have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                                        (SpecTec.«Instr_ok:clause:96» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                                      unfold SpecTec.«Instr_ok:clause:96»
                                                                                                                                                                                                      exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                                        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.TERNARYBITS»]))
                                                                                                                                                                                                    cases hbody with
                                                                                                                                                                                                    | orElse_success hfirst =>
                                                                                                                                                                                                        exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                                    | orElse_unmatch _ hbody =>
                                                                                                                                                                                                      have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                                          (SpecTec.«Instr_ok:clause:97» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                                        unfold SpecTec.«Instr_ok:clause:97»
                                                                                                                                                                                                        exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                                          (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.SPLAT»]))
                                                                                                                                                                                                      cases hbody with
                                                                                                                                                                                                      | orElse_success hfirst =>
                                                                                                                                                                                                          exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                                      | orElse_unmatch _ hbody =>
                                                                                                                                                                                                        have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                                            (SpecTec.«Instr_ok:clause:98» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                                          unfold SpecTec.«Instr_ok:clause:98»
                                                                                                                                                                                                          exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                                            (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.EXTRACT»]))
                                                                                                                                                                                                        cases hbody with
                                                                                                                                                                                                        | orElse_success hfirst =>
                                                                                                                                                                                                            exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                                        | orElse_unmatch _ hbody =>
                                                                                                                                                                                                          have hunmatch : SpecTecExecution.Eval SpecTec.Body
                                                                                                                                                                                                              (SpecTec.«Instr_ok:clause:99» c irt (.«REF.FUNC» x)) n .unmatch n := by
                                                                                                                                                                                                            unfold SpecTec.«Instr_ok:clause:99»
                                                                                                                                                                                                            exact SpecTecExecution.Eval.bind_unmatch
                                                                                                                                                                                                              (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.REPLACE»]))
                                                                                                                                                                                                          cases hbody with
                                                                                                                                                                                                          | orElse_success hfirst =>
                                                                                                                                                                                                              exact (properties.wasm_module_ok.Execution.unmatch_excludes_success hunmatch _ hfirst).elim
                                                                                                                                                                                                          | orElse_unmatch _ hbody =>
                                                                                                                                                                                                            cases hbody

theorem ref_func_dispatch_requires_membership
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (result : SpecTec.inferinstrtype)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«REF.FUNC» x)⟩)
      n (.success (.of result)) finalSupply) :
    x < c.FUNCS.length ∧ FreeUnionValidation.HasFunc c.REFS x :=
  RefFuncValidation.ref_func_clause_requires_membership
    c irt x result n finalSupply
    (ref_func_clause_of_dispatch c irt x result n finalSupply hcall)

theorem ref_func_dispatch_success_of_membership
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (dt : SpecTec.deftype) (n : Nat)
    (hlt : x < c.FUNCS.length)
    (hget : c.FUNCS[x]? = some dt)
    (href : FreeUnionValidation.HasFunc c.REFS x) :
    ∃ result : SpecTec.inferinstrtype,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.Call.Instr_ok c irt (.«REF.FUNC» x)⟩)
        n (.success (.of result)) n := by
  obtain ⟨result, hclause⟩ :=
    RefFuncValidation.ref_func_clause_success_of_membership
      c irt x dt n hlt hget href
  exact ⟨result, ref_func_dispatch_of_clause c irt x result n n hclause⟩

theorem ref_func_dispatch_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (n : Nat) :
    (∃ (result : SpecTec.inferinstrtype) (finalSupply : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.Call.Instr_ok c irt (.«REF.FUNC» x)⟩)
        n (.success (.of result)) finalSupply) ↔
      x < c.FUNCS.length ∧ FreeUnionValidation.HasFunc c.REFS x := by
  constructor
  · rintro ⟨result, finalSupply, hcall⟩
    exact ref_func_dispatch_requires_membership
      c irt x result n finalSupply hcall
  · rintro ⟨hlt, href⟩
    have hget : c.FUNCS[x]? = some c.FUNCS[x] :=
      List.getElem?_eq_getElem hlt
    obtain ⟨result, hcall⟩ :=
      ref_func_dispatch_success_of_membership
        c irt x c.FUNCS[x] n hlt hget href
    exact ⟨result, n, hcall⟩

end properties.wasm_module_ok.InstrRefDispatch
