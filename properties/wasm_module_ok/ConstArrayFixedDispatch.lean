import properties.wasm_module_ok.ConstArrayFixedEffect
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayFixedDispatch

theorem array_new_fixed_dispatch_of_clause
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (iit : SpecTec.inferinstrtype) (start fin : Nat)
    (hclause : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:66» c irt (.«ARRAY.NEW_FIXED» x count))
      start (.success (.of iit)) fin) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«ARRAY.NEW_FIXED» x count)⟩)
      start (.success (.of iit)) fin := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Instr_ok_clauses c irt (.«ARRAY.NEW_FIXED» x count)))
    start (.success (.of iit)) fin
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:0» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:UNREACHABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:1» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:NOP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:2» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:3» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:4» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:SELECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:5» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BLOCK»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:6» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOOP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:7» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:IF % % ELSE %»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:8» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:9» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_IF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:10» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_TABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:11» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:11»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:12» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:13» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:13»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:14» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:14»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST_FAIL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:15» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:15»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:16» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:16»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:17» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:17»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_INDIRECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:18» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:18»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:19» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:19»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:20» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:20»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:21» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:21»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_INDIRECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:22» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:22»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:23» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:23»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:24» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:24»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TRY_TABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:25» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:25»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:26» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:26»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:27» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:27»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.TEE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:28» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:28»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:29» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:29»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:30» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:30»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:31» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:31»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:32» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:32»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SIZE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:33» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:33»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:34» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:34»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.FILL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:35» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:35»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.COPY»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:36» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:36»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.INIT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:37» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:37»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ELEM.DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:38» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:38»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOAD»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:39» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:39»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STORE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:40» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:40»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:41» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:41»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:42» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:42»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD_LANE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:43» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:43»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE_LANE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:44» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:44»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.SIZE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:45» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:45»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.GROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:46» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:46»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.FILL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:47» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:47»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.COPY»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:48» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:48»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.INIT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:49» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:49»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DATA.DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:50» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:50»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:51» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:51»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:52» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:52»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.IS_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:53» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:53»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.AS_NON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:54» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:54»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.TEST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:55» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:55»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.CAST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:56» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:56»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.EQ»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:57» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:57»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:58» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:58»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:I31.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:59» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:59»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:60» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:60»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:61» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:61»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:62» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:62»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:63» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:63»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:64» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:64»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:65» c irt (.«ARRAY.NEW_FIXED» x count)) start .unmatch start
    unfold SpecTec.«Instr_ok:clause:65»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  exact SpecTecExecution.tryClauses_cons_success hclause

theorem array_new_fixed_clause_of_dispatch
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n) (iit : SpecTec.inferinstrtype)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«ARRAY.NEW_FIXED» x count)⟩)
      n (.success (.of iit)) fin) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:66» c irt (.«ARRAY.NEW_FIXED» x count))
      n (.success (.of iit)) fin := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Instr_ok_clauses c irt (.«ARRAY.NEW_FIXED» x count)))
        n (.success (.of iit)) fin at hbody
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.Instr_ok_clauses c irt (.«ARRAY.NEW_FIXED» x count))
          n (.of iit) fin).1 hbody
      unfold SpecTec.Instr_ok_clauses at hselected
      cases hselected with
      | here h0 =>
          unfold SpecTec.«Instr_ok:clause:0» at h0
          cases h0 with
          | bind_success hguard _ =>
              cases hguard with
              | guard_true hg => simp [SpecTec.«exec:match:instr:UNREACHABLE»] at hg
      | next _ hselected =>
        cases hselected with
        | here h1 =>
            unfold SpecTec.«Instr_ok:clause:1» at h1
            cases h1 with
            | bind_success hguard _ =>
                cases hguard with
                | guard_true hg => simp [SpecTec.«exec:match:instr:NOP»] at hg
        | next _ hselected =>
          cases hselected with
          | here h2 =>
              unfold SpecTec.«Instr_ok:clause:2» at h2
              cases h2 with
              | bind_success hguard _ =>
                  cases hguard with
                  | guard_true hg => simp [SpecTec.«exec:match:instr:DROP»] at hg
          | next _ hselected =>
            cases hselected with
            | here h3 =>
                unfold SpecTec.«Instr_ok:clause:3» at h3
                cases h3 with
                | bind_success hguard _ =>
                    cases hguard with
                    | guard_true hg => simp at hg
            | next _ hselected =>
              cases hselected with
              | here h4 =>
                  unfold SpecTec.«Instr_ok:clause:4» at h4
                  cases h4 with
                  | bind_success hguard _ =>
                      cases hguard with
                      | guard_true hg => simp [SpecTec.«exec:match:instr:SELECT»] at hg
              | next _ hselected =>
                cases hselected with
                | here h5 =>
                    unfold SpecTec.«Instr_ok:clause:5» at h5
                    cases h5 with
                    | bind_success hguard _ =>
                        cases hguard with
                        | guard_true hg => simp [SpecTec.«exec:match:instr:BLOCK»] at hg
                | next _ hselected =>
                  cases hselected with
                  | here h6 =>
                      unfold SpecTec.«Instr_ok:clause:6» at h6
                      cases h6 with
                      | bind_success hguard _ =>
                          cases hguard with
                          | guard_true hg => simp [SpecTec.«exec:match:instr:LOOP»] at hg
                  | next _ hselected =>
                    cases hselected with
                    | here h7 =>
                        unfold SpecTec.«Instr_ok:clause:7» at h7
                        cases h7 with
                        | bind_success hguard _ =>
                            cases hguard with
                            | guard_true hg => simp [SpecTec.«exec:match:instr:IF % % ELSE %»] at hg
                    | next _ hselected =>
                      cases hselected with
                      | here h8 =>
                          unfold SpecTec.«Instr_ok:clause:8» at h8
                          cases h8 with
                          | bind_success hguard _ =>
                              cases hguard with
                              | guard_true hg => simp [SpecTec.«exec:match:instr:BR»] at hg
                      | next _ hselected =>
                        cases hselected with
                        | here h9 =>
                            unfold SpecTec.«Instr_ok:clause:9» at h9
                            cases h9 with
                            | bind_success hguard _ =>
                                cases hguard with
                                | guard_true hg => simp [SpecTec.«exec:match:instr:BR_IF»] at hg
                        | next _ hselected =>
                          cases hselected with
                          | here h10 =>
                              unfold SpecTec.«Instr_ok:clause:10» at h10
                              cases h10 with
                              | bind_success hguard _ =>
                                  cases hguard with
                                  | guard_true hg => simp [SpecTec.«exec:match:instr:BR_TABLE»] at hg
                          | next _ hselected =>
                            cases hselected with
                            | here h11 =>
                                unfold SpecTec.«Instr_ok:clause:11» at h11
                                cases h11 with
                                | bind_success hguard _ =>
                                    cases hguard with
                                    | guard_true hg => simp [SpecTec.«exec:match:instr:BR_ON_NULL»] at hg
                            | next _ hselected =>
                              cases hselected with
                              | here h12 =>
                                  unfold SpecTec.«Instr_ok:clause:12» at h12
                                  cases h12 with
                                  | bind_success hguard _ =>
                                      cases hguard with
                                      | guard_true hg => simp [SpecTec.«exec:match:instr:BR_ON_NON_NULL»] at hg
                              | next _ hselected =>
                                cases hselected with
                                | here h13 =>
                                    unfold SpecTec.«Instr_ok:clause:13» at h13
                                    cases h13 with
                                    | bind_success hguard _ =>
                                        cases hguard with
                                        | guard_true hg => simp [SpecTec.«exec:match:instr:BR_ON_CAST»] at hg
                                | next _ hselected =>
                                  cases hselected with
                                  | here h14 =>
                                      unfold SpecTec.«Instr_ok:clause:14» at h14
                                      cases h14 with
                                      | bind_success hguard _ =>
                                          cases hguard with
                                          | guard_true hg => simp [SpecTec.«exec:match:instr:BR_ON_CAST_FAIL»] at hg
                                  | next _ hselected =>
                                    cases hselected with
                                    | here h15 =>
                                        unfold SpecTec.«Instr_ok:clause:15» at h15
                                        cases h15 with
                                        | bind_success hguard _ =>
                                            cases hguard with
                                            | guard_true hg => simp [SpecTec.«exec:match:instr:CALL»] at hg
                                    | next _ hselected =>
                                      cases hselected with
                                      | here h16 =>
                                          unfold SpecTec.«Instr_ok:clause:16» at h16
                                          cases h16 with
                                          | bind_success hguard _ =>
                                              cases hguard with
                                              | guard_true hg => simp [SpecTec.«exec:match:instr:CALL_REF»] at hg
                                      | next _ hselected =>
                                        cases hselected with
                                        | here h17 =>
                                            unfold SpecTec.«Instr_ok:clause:17» at h17
                                            cases h17 with
                                            | bind_success hguard _ =>
                                                cases hguard with
                                                | guard_true hg => simp [SpecTec.«exec:match:instr:CALL_INDIRECT»] at hg
                                        | next _ hselected =>
                                          cases hselected with
                                          | here h18 =>
                                              unfold SpecTec.«Instr_ok:clause:18» at h18
                                              cases h18 with
                                              | bind_success hguard _ =>
                                                  cases hguard with
                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:RETURN»] at hg
                                          | next _ hselected =>
                                            cases hselected with
                                            | here h19 =>
                                                unfold SpecTec.«Instr_ok:clause:19» at h19
                                                cases h19 with
                                                | bind_success hguard _ =>
                                                    cases hguard with
                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:RETURN_CALL»] at hg
                                            | next _ hselected =>
                                              cases hselected with
                                              | here h20 =>
                                                  unfold SpecTec.«Instr_ok:clause:20» at h20
                                                  cases h20 with
                                                  | bind_success hguard _ =>
                                                      cases hguard with
                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:RETURN_CALL_REF»] at hg
                                              | next _ hselected =>
                                                cases hselected with
                                                | here h21 =>
                                                    unfold SpecTec.«Instr_ok:clause:21» at h21
                                                    cases h21 with
                                                    | bind_success hguard _ =>
                                                        cases hguard with
                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:RETURN_CALL_INDIRECT»] at hg
                                                | next _ hselected =>
                                                  cases hselected with
                                                  | here h22 =>
                                                      unfold SpecTec.«Instr_ok:clause:22» at h22
                                                      cases h22 with
                                                      | bind_success hguard _ =>
                                                          cases hguard with
                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:THROW»] at hg
                                                  | next _ hselected =>
                                                    cases hselected with
                                                    | here h23 =>
                                                        unfold SpecTec.«Instr_ok:clause:23» at h23
                                                        cases h23 with
                                                        | bind_success hguard _ =>
                                                            cases hguard with
                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:THROW_REF»] at hg
                                                    | next _ hselected =>
                                                      cases hselected with
                                                      | here h24 =>
                                                          unfold SpecTec.«Instr_ok:clause:24» at h24
                                                          cases h24 with
                                                          | bind_success hguard _ =>
                                                              cases hguard with
                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:TRY_TABLE»] at hg
                                                      | next _ hselected =>
                                                        cases hselected with
                                                        | here h25 =>
                                                            unfold SpecTec.«Instr_ok:clause:25» at h25
                                                            cases h25 with
                                                            | bind_success hguard _ =>
                                                                cases hguard with
                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:LOCAL.GET»] at hg
                                                        | next _ hselected =>
                                                          cases hselected with
                                                          | here h26 =>
                                                              unfold SpecTec.«Instr_ok:clause:26» at h26
                                                              cases h26 with
                                                              | bind_success hguard _ =>
                                                                  cases hguard with
                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:LOCAL.SET»] at hg
                                                          | next _ hselected =>
                                                            cases hselected with
                                                            | here h27 =>
                                                                unfold SpecTec.«Instr_ok:clause:27» at h27
                                                                cases h27 with
                                                                | bind_success hguard _ =>
                                                                    cases hguard with
                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:LOCAL.TEE»] at hg
                                                            | next _ hselected =>
                                                              cases hselected with
                                                              | here h28 =>
                                                                                                          unfold SpecTec.«Instr_ok:clause:28» at h28
                                                                                                          cases h28 with
                                                                                                          | bind_success hguard _ =>
                                                                                                              cases hguard with
                                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:GLOBAL.GET»] at hg
                                                              | next _ hselected =>
                                                                cases hselected with
                                                                | here h29 =>
                                                                    unfold SpecTec.«Instr_ok:clause:29» at h29
                                                                    cases h29 with
                                                                    | bind_success hguard _ =>
                                                                        cases hguard with
                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:GLOBAL.SET»] at hg
                                                                | next _ hselected =>
                                                                  cases hselected with
                                                                  | here h30 =>
                                                                      unfold SpecTec.«Instr_ok:clause:30» at h30
                                                                      cases h30 with
                                                                      | bind_success hguard _ =>
                                                                          cases hguard with
                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:TABLE.GET»] at hg
                                                                  | next _ hselected =>
                                                                    cases hselected with
                                                                    | here h31 =>
                                                                        unfold SpecTec.«Instr_ok:clause:31» at h31
                                                                        cases h31 with
                                                                        | bind_success hguard _ =>
                                                                            cases hguard with
                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:TABLE.SET»] at hg
                                                                    | next _ hselected =>
                                                                      cases hselected with
                                                                      | here h32 =>
                                                                          unfold SpecTec.«Instr_ok:clause:32» at h32
                                                                          cases h32 with
                                                                          | bind_success hguard _ =>
                                                                              cases hguard with
                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:TABLE.SIZE»] at hg
                                                                      | next _ hselected =>
                                                                        cases hselected with
                                                                        | here h33 =>
                                                                            unfold SpecTec.«Instr_ok:clause:33» at h33
                                                                            cases h33 with
                                                                            | bind_success hguard _ =>
                                                                                cases hguard with
                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:TABLE.GROW»] at hg
                                                                        | next _ hselected =>
                                                                          cases hselected with
                                                                          | here h34 =>
                                                                              unfold SpecTec.«Instr_ok:clause:34» at h34
                                                                              cases h34 with
                                                                              | bind_success hguard _ =>
                                                                                  cases hguard with
                                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:TABLE.FILL»] at hg
                                                                          | next _ hselected =>
                                                                            cases hselected with
                                                                            | here h35 =>
                                                                                unfold SpecTec.«Instr_ok:clause:35» at h35
                                                                                cases h35 with
                                                                                | bind_success hguard _ =>
                                                                                    cases hguard with
                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:TABLE.COPY»] at hg
                                                                            | next _ hselected =>
                                                                              cases hselected with
                                                                              | here h36 =>
                                                                                  unfold SpecTec.«Instr_ok:clause:36» at h36
                                                                                  cases h36 with
                                                                                  | bind_success hguard _ =>
                                                                                      cases hguard with
                                                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:TABLE.INIT»] at hg
                                                                              | next _ hselected =>
                                                                                cases hselected with
                                                                                | here h37 =>
                                                                                    unfold SpecTec.«Instr_ok:clause:37» at h37
                                                                                    cases h37 with
                                                                                    | bind_success hguard _ =>
                                                                                        cases hguard with
                                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:ELEM.DROP»] at hg
                                                                                | next _ hselected =>
                                                                                  cases hselected with
                                                                                  | here h38 =>
                                                                                      unfold SpecTec.«Instr_ok:clause:38» at h38
                                                                                      cases h38 with
                                                                                      | bind_success hguard _ =>
                                                                                          cases hguard with
                                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:LOAD»] at hg
                                                                                  | next _ hselected =>
                                                                                    cases hselected with
                                                                                    | here h39 =>
                                                                                        unfold SpecTec.«Instr_ok:clause:39» at h39
                                                                                        cases h39 with
                                                                                        | bind_success hguard _ =>
                                                                                            cases hguard with
                                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:STORE»] at hg
                                                                                    | next _ hselected =>
                                                                                      cases hselected with
                                                                                      | here h40 =>
                                                                                          unfold SpecTec.«Instr_ok:clause:40» at h40
                                                                                          cases h40 with
                                                                                          | bind_success hguard _ =>
                                                                                              cases hguard with
                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.LOAD»] at hg
                                                                                      | next _ hselected =>
                                                                                        cases hselected with
                                                                                        | here h41 =>
                                                                                            unfold SpecTec.«Instr_ok:clause:41» at h41
                                                                                            cases h41 with
                                                                                            | bind_success hguard _ =>
                                                                                                cases hguard with
                                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.STORE»] at hg
                                                                                        | next _ hselected =>
                                                                                          cases hselected with
                                                                                          | here h42 =>
                                                                                              unfold SpecTec.«Instr_ok:clause:42» at h42
                                                                                              cases h42 with
                                                                                              | bind_success hguard _ =>
                                                                                                  cases hguard with
                                                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.LOAD_LANE»] at hg
                                                                                          | next _ hselected =>
                                                                                            cases hselected with
                                                                                            | here h43 =>
                                                                                                unfold SpecTec.«Instr_ok:clause:43» at h43
                                                                                                cases h43 with
                                                                                                | bind_success hguard _ =>
                                                                                                    cases hguard with
                                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.STORE_LANE»] at hg
                                                                                            | next _ hselected =>
                                                                                              cases hselected with
                                                                                              | here h44 =>
                                                                                                  unfold SpecTec.«Instr_ok:clause:44» at h44
                                                                                                  cases h44 with
                                                                                                  | bind_success hguard _ =>
                                                                                                      cases hguard with
                                                                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:MEMORY.SIZE»] at hg
                                                                                              | next _ hselected =>
                                                                                                cases hselected with
                                                                                                | here h45 =>
                                                                                                    unfold SpecTec.«Instr_ok:clause:45» at h45
                                                                                                    cases h45 with
                                                                                                    | bind_success hguard _ =>
                                                                                                        cases hguard with
                                                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:MEMORY.GROW»] at hg
                                                                                                | next _ hselected =>
                                                                                                  cases hselected with
                                                                                                  | here h46 =>
                                                                                                      unfold SpecTec.«Instr_ok:clause:46» at h46
                                                                                                      cases h46 with
                                                                                                      | bind_success hguard _ =>
                                                                                                          cases hguard with
                                                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:MEMORY.FILL»] at hg
                                                                                                  | next _ hselected =>
                                                                                                    cases hselected with
                                                                                                    | here h47 =>
                                                                                                        unfold SpecTec.«Instr_ok:clause:47» at h47
                                                                                                        cases h47 with
                                                                                                        | bind_success hguard _ =>
                                                                                                            cases hguard with
                                                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:MEMORY.COPY»] at hg
                                                                                                    | next _ hselected =>
                                                                                                      cases hselected with
                                                                                                      | here h48 =>
                                                                                                          unfold SpecTec.«Instr_ok:clause:48» at h48
                                                                                                          cases h48 with
                                                                                                          | bind_success hguard _ =>
                                                                                                              cases hguard with
                                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:MEMORY.INIT»] at hg
                                                                                                      | next _ hselected =>
                                                                                                        cases hselected with
                                                                                                        | here h49 =>
                                                                                                            unfold SpecTec.«Instr_ok:clause:49» at h49
                                                                                                            cases h49 with
                                                                                                            | bind_success hguard _ =>
                                                                                                                cases hguard with
                                                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:DATA.DROP»] at hg
                                                                                                        | next _ hselected =>
                                                                                                          cases hselected with
                                                                                                          | here h50 =>
                                                                                                              unfold SpecTec.«Instr_ok:clause:50» at h50
                                                                                                              cases h50 with
                                                                                                              | bind_success hguard _ =>
                                                                                                                  cases hguard with
                                                                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:REF.NULL»] at hg
                                                                                                          | next _ hselected =>
                                                                                                            cases hselected with
                                                                                                            | here h51 =>
                                                                                                                unfold SpecTec.«Instr_ok:clause:51» at h51
                                                                                                                cases h51 with
                                                                                                                | bind_success hguard _ =>
                                                                                                                    cases hguard with
                                                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:REF.FUNC»] at hg
                                                                                                            | next _ hselected =>
                                                                                                              cases hselected with
                                                                                                              | here h52 =>
                                                                                                                  unfold SpecTec.«Instr_ok:clause:52» at h52
                                                                                                                  cases h52 with
                                                                                                                  | bind_success hguard _ =>
                                                                                                                      cases hguard with
                                                                                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:REF.IS_NULL»] at hg
                                                                                                              | next _ hselected =>
                                                                                                                cases hselected with
                                                                                                                | here h53 =>
                                                                                                                    unfold SpecTec.«Instr_ok:clause:53» at h53
                                                                                                                    cases h53 with
                                                                                                                    | bind_success hguard _ =>
                                                                                                                        cases hguard with
                                                                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:REF.AS_NON_NULL»] at hg
                                                                                                                | next _ hselected =>
                                                                                                                  cases hselected with
                                                                                                                  | here h54 =>
                                                                                                                      unfold SpecTec.«Instr_ok:clause:54» at h54
                                                                                                                      cases h54 with
                                                                                                                      | bind_success hguard _ =>
                                                                                                                          cases hguard with
                                                                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:REF.TEST»] at hg
                                                                                                                  | next _ hselected =>
                                                                                                                    cases hselected with
                                                                                                                    | here h55 =>
                                                                                                                        unfold SpecTec.«Instr_ok:clause:55» at h55
                                                                                                                        cases h55 with
                                                                                                                        | bind_success hguard _ =>
                                                                                                                            cases hguard with
                                                                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:REF.CAST»] at hg
                                                                                                                    | next _ hselected =>
                                                                                                                      cases hselected with
                                                                                                                      | here h56 =>
                                                                                                                          unfold SpecTec.«Instr_ok:clause:56» at h56
                                                                                                                          cases h56 with
                                                                                                                          | bind_success hguard _ =>
                                                                                                                              cases hguard with
                                                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:REF.EQ»] at hg
                                                                                                                      | next _ hselected =>
                                                                                                                        cases hselected with
                                                                                                                        | here h57 =>
                                                                                                                            unfold SpecTec.«Instr_ok:clause:57» at h57
                                                                                                                            cases h57 with
                                                                                                                            | bind_success hguard _ =>
                                                                                                                                cases hguard with
                                                                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:REF.I31»] at hg
                                                                                                                        | next _ hselected =>
                                                                                                                          cases hselected with
                                                                                                                          | here h58 =>
                                                                                                                              unfold SpecTec.«Instr_ok:clause:58» at h58
                                                                                                                              cases h58 with
                                                                                                                              | bind_success hguard _ =>
                                                                                                                                  cases hguard with
                                                                                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:I31.GET»] at hg
                                                                                                                          | next _ hselected =>
                                                                                                                            cases hselected with
                                                                                                                            | here h59 =>
                                                                                                                                unfold SpecTec.«Instr_ok:clause:59» at h59
                                                                                                                                cases h59 with
                                                                                                                                | bind_success hguard _ =>
                                                                                                                                    cases hguard with
                                                                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:STRUCT.NEW»] at hg
                                                                                                                            | next _ hselected =>
                                                                                                                              cases hselected with
                                                                                                                              | here h60 =>
                                                                                                                                  unfold SpecTec.«Instr_ok:clause:60» at h60
                                                                                                                                  cases h60 with
                                                                                                                                  | bind_success hguard _ =>
                                                                                                                                      cases hguard with
                                                                                                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:STRUCT.NEW»] at hg
                                                                                                                              | next _ hselected =>
                                                                                                                                cases hselected with
                                                                                                                                | here h61 =>
                                                                                                                                    unfold SpecTec.«Instr_ok:clause:61» at h61
                                                                                                                                    cases h61 with
                                                                                                                                    | bind_success hguard _ =>
                                                                                                                                        cases hguard with
                                                                                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:STRUCT.GET»] at hg
                                                                                                                                | next _ hselected =>
                                                                                                                                  cases hselected with
                                                                                                                                  | here h62 =>
                                                                                                                                      unfold SpecTec.«Instr_ok:clause:62» at h62
                                                                                                                                      cases h62 with
                                                                                                                                      | bind_success hguard _ =>
                                                                                                                                          cases hguard with
                                                                                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:STRUCT.GET»] at hg
                                                                                                                                  | next _ hselected =>
                                                                                                                                    cases hselected with
                                                                                                                                    | here h63 =>
                                                                                                                                        unfold SpecTec.«Instr_ok:clause:63» at h63
                                                                                                                                        cases h63 with
                                                                                                                                        | bind_success hguard _ =>
                                                                                                                                            cases hguard with
                                                                                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:STRUCT.SET»] at hg
                                                                                                                                    | next _ hselected =>
                                                                                                                                      cases hselected with
                                                                                                                                      | here h64 =>
                                                                                                                                          unfold SpecTec.«Instr_ok:clause:64» at h64
                                                                                                                                          cases h64 with
                                                                                                                                          | bind_success hguard _ =>
                                                                                                                                              cases hguard with
                                                                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.NEW»] at hg
                                                                                                                                      | next _ hselected =>
                                                                                                                                        cases hselected with
                                                                                                                                        | here h65 =>
                                                                                                                                            unfold SpecTec.«Instr_ok:clause:65» at h65
                                                                                                                                            cases h65 with
                                                                                                                                            | bind_success hguard _ =>
                                                                                                                                                cases hguard with
                                                                                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.NEW»] at hg
                                                                                                                                        | next _ hselected =>
                                                                                                                                          cases hselected with
                                                                                                                                          | here h66 => exact h66
                                                                                                                                          | next _ hselected =>
                                                                                                                                            cases hselected with
                                                                                                                                            | here h67 =>
                                                                                                                                                unfold SpecTec.«Instr_ok:clause:67» at h67
                                                                                                                                                cases h67 with
                                                                                                                                                | bind_success hguard _ =>
                                                                                                                                                    cases hguard with
                                                                                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.NEW_ELEM»] at hg
                                                                                                                                            | next _ hselected =>
                                                                                                                                              cases hselected with
                                                                                                                                              | here h68 =>
                                                                                                                                                  unfold SpecTec.«Instr_ok:clause:68» at h68
                                                                                                                                                  cases h68 with
                                                                                                                                                  | bind_success hguard _ =>
                                                                                                                                                      cases hguard with
                                                                                                                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.NEW_DATA»] at hg
                                                                                                                                              | next _ hselected =>
                                                                                                                                                cases hselected with
                                                                                                                                                | here h69 =>
                                                                                                                                                    unfold SpecTec.«Instr_ok:clause:69» at h69
                                                                                                                                                    cases h69 with
                                                                                                                                                    | bind_success hguard _ =>
                                                                                                                                                        cases hguard with
                                                                                                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.GET»] at hg
                                                                                                                                                | next _ hselected =>
                                                                                                                                                  cases hselected with
                                                                                                                                                  | here h70 =>
                                                                                                                                                      unfold SpecTec.«Instr_ok:clause:70» at h70
                                                                                                                                                      cases h70 with
                                                                                                                                                      | bind_success hguard _ =>
                                                                                                                                                          cases hguard with
                                                                                                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.GET»] at hg
                                                                                                                                                  | next _ hselected =>
                                                                                                                                                    cases hselected with
                                                                                                                                                    | here h71 =>
                                                                                                                                                        unfold SpecTec.«Instr_ok:clause:71» at h71
                                                                                                                                                        cases h71 with
                                                                                                                                                        | bind_success hguard _ =>
                                                                                                                                                            cases hguard with
                                                                                                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.SET»] at hg
                                                                                                                                                    | next _ hselected =>
                                                                                                                                                      cases hselected with
                                                                                                                                                      | here h72 =>
                                                                                                                                                          unfold SpecTec.«Instr_ok:clause:72» at h72
                                                                                                                                                          cases h72 with
                                                                                                                                                          | bind_success hguard _ =>
                                                                                                                                                              cases hguard with
                                                                                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.LEN»] at hg
                                                                                                                                                      | next _ hselected =>
                                                                                                                                                        cases hselected with
                                                                                                                                                        | here h73 =>
                                                                                                                                                            unfold SpecTec.«Instr_ok:clause:73» at h73
                                                                                                                                                            cases h73 with
                                                                                                                                                            | bind_success hguard _ =>
                                                                                                                                                                cases hguard with
                                                                                                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.COPY»] at hg
                                                                                                                                                        | next _ hselected =>
                                                                                                                                                          cases hselected with
                                                                                                                                                          | here h74 =>
                                                                                                                                                              unfold SpecTec.«Instr_ok:clause:74» at h74
                                                                                                                                                              cases h74 with
                                                                                                                                                              | bind_success hguard _ =>
                                                                                                                                                                  cases hguard with
                                                                                                                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.FILL»] at hg
                                                                                                                                                          | next _ hselected =>
                                                                                                                                                            cases hselected with
                                                                                                                                                            | here h75 =>
                                                                                                                                                                unfold SpecTec.«Instr_ok:clause:75» at h75
                                                                                                                                                                cases h75 with
                                                                                                                                                                | bind_success hguard _ =>
                                                                                                                                                                    cases hguard with
                                                                                                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.INIT_DATA»] at hg
                                                                                                                                                            | next _ hselected =>
                                                                                                                                                              cases hselected with
                                                                                                                                                              | here h76 =>
                                                                                                                                                                  unfold SpecTec.«Instr_ok:clause:76» at h76
                                                                                                                                                                  cases h76 with
                                                                                                                                                                  | bind_success hguard _ =>
                                                                                                                                                                      cases hguard with
                                                                                                                                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:ARRAY.INIT_ELEM»] at hg
                                                                                                                                                              | next _ hselected =>
                                                                                                                                                                cases hselected with
                                                                                                                                                                | here h77 =>
                                                                                                                                                                    unfold SpecTec.«Instr_ok:clause:77» at h77
                                                                                                                                                                    cases h77 with
                                                                                                                                                                    | bind_success hguard _ =>
                                                                                                                                                                        cases hguard with
                                                                                                                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:EXTERN.CONVERT»] at hg
                                                                                                                                                                | next _ hselected =>
                                                                                                                                                                  cases hselected with
                                                                                                                                                                  | here h78 =>
                                                                                                                                                                      unfold SpecTec.«Instr_ok:clause:78» at h78
                                                                                                                                                                      cases h78 with
                                                                                                                                                                      | bind_success hguard _ =>
                                                                                                                                                                          cases hguard with
                                                                                                                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:CONST»] at hg
                                                                                                                                                                  | next _ hselected =>
                                                                                                                                                                    cases hselected with
                                                                                                                                                                    | here h79 =>
                                                                                                                                                                        unfold SpecTec.«Instr_ok:clause:79» at h79
                                                                                                                                                                        cases h79 with
                                                                                                                                                                        | bind_success hguard _ =>
                                                                                                                                                                            cases hguard with
                                                                                                                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:TEST»] at hg
                                                                                                                                                                    | next _ hselected =>
                                                                                                                                                                      cases hselected with
                                                                                                                                                                      | here h80 =>
                                                                                                                                                                          unfold SpecTec.«Instr_ok:clause:80» at h80
                                                                                                                                                                          cases h80 with
                                                                                                                                                                          | bind_success hguard _ =>
                                                                                                                                                                              cases hguard with
                                                                                                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:COMPARE»] at hg
                                                                                                                                                                      | next _ hselected =>
                                                                                                                                                                        cases hselected with
                                                                                                                                                                        | here h81 =>
                                                                                                                                                                            unfold SpecTec.«Instr_ok:clause:81» at h81
                                                                                                                                                                            cases h81 with
                                                                                                                                                                            | bind_success hguard _ =>
                                                                                                                                                                                cases hguard with
                                                                                                                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:UNARY»] at hg
                                                                                                                                                                        | next _ hselected =>
                                                                                                                                                                          cases hselected with
                                                                                                                                                                          | here h82 =>
                                                                                                                                                                              unfold SpecTec.«Instr_ok:clause:82» at h82
                                                                                                                                                                              cases h82 with
                                                                                                                                                                              | bind_success hguard _ =>
                                                                                                                                                                                  cases hguard with
                                                                                                                                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:BINOP»] at hg
                                                                                                                                                                          | next _ hselected =>
                                                                                                                                                                            cases hselected with
                                                                                                                                                                            | here h83 =>
                                                                                                                                                                                unfold SpecTec.«Instr_ok:clause:83» at h83
                                                                                                                                                                                cases h83 with
                                                                                                                                                                                | bind_success hguard _ =>
                                                                                                                                                                                    cases hguard with
                                                                                                                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:CONVERT»] at hg
                                                                                                                                                                            | next _ hselected =>
                                                                                                                                                                              cases hselected with
                                                                                                                                                                              | here h84 =>
                                                                                                                                                                                  unfold SpecTec.«Instr_ok:clause:84» at h84
                                                                                                                                                                                  cases h84 with
                                                                                                                                                                                  | bind_success hguard _ =>
                                                                                                                                                                                      cases hguard with
                                                                                                                                                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.CONST»] at hg
                                                                                                                                                                              | next _ hselected =>
                                                                                                                                                                                cases hselected with
                                                                                                                                                                                | here h85 =>
                                                                                                                                                                                    unfold SpecTec.«Instr_ok:clause:85» at h85
                                                                                                                                                                                    cases h85 with
                                                                                                                                                                                    | bind_success hguard _ =>
                                                                                                                                                                                        cases hguard with
                                                                                                                                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.TEST»] at hg
                                                                                                                                                                                | next _ hselected =>
                                                                                                                                                                                  cases hselected with
                                                                                                                                                                                  | here h86 =>
                                                                                                                                                                                      unfold SpecTec.«Instr_ok:clause:86» at h86
                                                                                                                                                                                      cases h86 with
                                                                                                                                                                                      | bind_success hguard _ =>
                                                                                                                                                                                          cases hguard with
                                                                                                                                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.UNARY»] at hg
                                                                                                                                                                                  | next _ hselected =>
                                                                                                                                                                                    cases hselected with
                                                                                                                                                                                    | here h87 =>
                                                                                                                                                                                        unfold SpecTec.«Instr_ok:clause:87» at h87
                                                                                                                                                                                        cases h87 with
                                                                                                                                                                                        | bind_success hguard _ =>
                                                                                                                                                                                            cases hguard with
                                                                                                                                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.BINARY»] at hg
                                                                                                                                                                                    | next _ hselected =>
                                                                                                                                                                                      cases hselected with
                                                                                                                                                                                      | here h88 =>
                                                                                                                                                                                          unfold SpecTec.«Instr_ok:clause:88» at h88
                                                                                                                                                                                          cases h88 with
                                                                                                                                                                                          | bind_success hguard _ =>
                                                                                                                                                                                              cases hguard with
                                                                                                                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.TERNARY»] at hg
                                                                                                                                                                                      | next _ hselected =>
                                                                                                                                                                                        cases hselected with
                                                                                                                                                                                        | here h89 =>
                                                                                                                                                                                            unfold SpecTec.«Instr_ok:clause:89» at h89
                                                                                                                                                                                            cases h89 with
                                                                                                                                                                                            | bind_success hguard _ =>
                                                                                                                                                                                                cases hguard with
                                                                                                                                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.COMPARE»] at hg
                                                                                                                                                                                        | next _ hselected =>
                                                                                                                                                                                          cases hselected with
                                                                                                                                                                                          | here h90 =>
                                                                                                                                                                                              unfold SpecTec.«Instr_ok:clause:90» at h90
                                                                                                                                                                                              cases h90 with
                                                                                                                                                                                              | bind_success hguard _ =>
                                                                                                                                                                                                  cases hguard with
                                                                                                                                                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.CONVERT»] at hg
                                                                                                                                                                                          | next _ hselected =>
                                                                                                                                                                                            cases hselected with
                                                                                                                                                                                            | here h91 =>
                                                                                                                                                                                                unfold SpecTec.«Instr_ok:clause:91» at h91
                                                                                                                                                                                                cases h91 with
                                                                                                                                                                                                | bind_success hguard _ =>
                                                                                                                                                                                                    cases hguard with
                                                                                                                                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.SHIFT»] at hg
                                                                                                                                                                                            | next _ hselected =>
                                                                                                                                                                                              cases hselected with
                                                                                                                                                                                              | here h92 =>
                                                                                                                                                                                                  unfold SpecTec.«Instr_ok:clause:92» at h92
                                                                                                                                                                                                  cases h92 with
                                                                                                                                                                                                  | bind_success hguard _ =>
                                                                                                                                                                                                      cases hguard with
                                                                                                                                                                                                      | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.BITMASK»] at hg
                                                                                                                                                                                              | next _ hselected =>
                                                                                                                                                                                                cases hselected with
                                                                                                                                                                                                | here h93 =>
                                                                                                                                                                                                    unfold SpecTec.«Instr_ok:clause:93» at h93
                                                                                                                                                                                                    cases h93 with
                                                                                                                                                                                                    | bind_success hguard _ =>
                                                                                                                                                                                                        cases hguard with
                                                                                                                                                                                                        | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.TESTBITS»] at hg
                                                                                                                                                                                                | next _ hselected =>
                                                                                                                                                                                                  cases hselected with
                                                                                                                                                                                                  | here h94 =>
                                                                                                                                                                                                      unfold SpecTec.«Instr_ok:clause:94» at h94
                                                                                                                                                                                                      cases h94 with
                                                                                                                                                                                                      | bind_success hguard _ =>
                                                                                                                                                                                                          cases hguard with
                                                                                                                                                                                                          | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.UNARYBITS»] at hg
                                                                                                                                                                                                  | next _ hselected =>
                                                                                                                                                                                                    cases hselected with
                                                                                                                                                                                                    | here h95 =>
                                                                                                                                                                                                        unfold SpecTec.«Instr_ok:clause:95» at h95
                                                                                                                                                                                                        cases h95 with
                                                                                                                                                                                                        | bind_success hguard _ =>
                                                                                                                                                                                                            cases hguard with
                                                                                                                                                                                                            | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.BINARYBITS»] at hg
                                                                                                                                                                                                    | next _ hselected =>
                                                                                                                                                                                                      cases hselected with
                                                                                                                                                                                                      | here h96 =>
                                                                                                                                                                                                          unfold SpecTec.«Instr_ok:clause:96» at h96
                                                                                                                                                                                                          cases h96 with
                                                                                                                                                                                                          | bind_success hguard _ =>
                                                                                                                                                                                                              cases hguard with
                                                                                                                                                                                                              | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.TERNARYBITS»] at hg
                                                                                                                                                                                                      | next _ hselected =>
                                                                                                                                                                                                        cases hselected with
                                                                                                                                                                                                        | here h97 =>
                                                                                                                                                                                                            unfold SpecTec.«Instr_ok:clause:97» at h97
                                                                                                                                                                                                            cases h97 with
                                                                                                                                                                                                            | bind_success hguard _ =>
                                                                                                                                                                                                                cases hguard with
                                                                                                                                                                                                                | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.SPLAT»] at hg
                                                                                                                                                                                                        | next _ hselected =>
                                                                                                                                                                                                          cases hselected with
                                                                                                                                                                                                          | here h98 =>
                                                                                                                                                                                                              unfold SpecTec.«Instr_ok:clause:98» at h98
                                                                                                                                                                                                              cases h98 with
                                                                                                                                                                                                              | bind_success hguard _ =>
                                                                                                                                                                                                                  cases hguard with
                                                                                                                                                                                                                  | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.EXTRACT»] at hg
                                                                                                                                                                                                          | next _ hselected =>
                                                                                                                                                                                                            cases hselected with
                                                                                                                                                                                                            | here h99 =>
                                                                                                                                                                                                                unfold SpecTec.«Instr_ok:clause:99» at h99
                                                                                                                                                                                                                cases h99 with
                                                                                                                                                                                                                | bind_success hguard _ =>
                                                                                                                                                                                                                    cases hguard with
                                                                                                                                                                                                                    | guard_true hg => simp [SpecTec.«exec:match:instr:VEC.REPLACE»] at hg
                                                                                                                                                                                                            | next _ hselected =>
                                                                                                                                                                                                              cases hselected


theorem array_new_fixed_dispatch_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (iit : SpecTec.inferinstrtype) (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«ARRAY.NEW_FIXED» x count)⟩)
      start (.success (.of iit)) fin ↔
    ∃ yt : SpecTec.fieldtype, ∃ t : SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.arraytype,
          SpecTec.Call.«$array_type» c x⟩)
        start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.valtype,
          SpecTec.Call.«$unpacked_field_type» yt⟩)
        middle (.success (.of t)) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, MakeValidation.makeResult t count),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  constructor
  · intro h
    exact (ConstArrayFixedEffect.array_new_fixed_clause_iff
      c irt x count iit start fin).1
      (array_new_fixed_clause_of_dispatch c irt x count iit start fin h)
  · intro h
    exact array_new_fixed_dispatch_of_clause c irt x count iit start fin
      ((ConstArrayFixedEffect.array_new_fixed_clause_iff
        c irt x count iit start fin).2 h)

theorem array_new_fixed_zero_dispatch_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«ARRAY.NEW_FIXED» x 0)⟩)
      start (.success (.of iit)) fin ↔
    ∃ yt : SpecTec.fieldtype, ∃ t : SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.arraytype,
          SpecTec.Call.«$array_type» c x⟩)
        start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.valtype,
          SpecTec.Call.«$unpacked_field_type» yt⟩)
        middle (.success (.of t)) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  simpa only [MakeValidation.makeResult] using
    (array_new_fixed_dispatch_iff c irt x 0 iit start fin)

theorem array_new_fixed_constant_instruction_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (iit : SpecTec.inferinstrtype) (start fin : Nat) :
    ConstSyntaxDecision.syntaxAllowed c (.«ARRAY.NEW_FIXED» x count) = true ∧
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«ARRAY.NEW_FIXED» x count)⟩)
      start (.success (.of iit)) fin ↔
    ∃ yt : SpecTec.fieldtype, ∃ t : SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.arraytype,
          SpecTec.Call.«$array_type» c x⟩)
        start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.valtype,
          SpecTec.Call.«$unpacked_field_type» yt⟩)
        middle (.success (.of t)) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, MakeValidation.makeResult t count),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  simpa only [ConstSyntaxDecision.syntaxAllowed, ite_self, true_and] using
    (array_new_fixed_dispatch_iff c irt x count iit start fin)

end properties.wasm_module_ok.ConstArrayFixedDispatch
