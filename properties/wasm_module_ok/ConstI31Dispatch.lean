import properties.wasm_module_ok.ConstI31Effect
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstI31Dispatch

theorem i31_dispatch_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«REF.I31»)⟩)
      n (.success (.of
        (⟨{ INS := (.NoEllipses, [.NumT .I32T]),
             OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull .I31HT)]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Instr_ok_clauses c irt (.«REF.I31»)))
    n (.success (.of
      (⟨{ INS := (.NoEllipses, [.NumT .I32T]),
           OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull .I31HT)]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:0» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:UNREACHABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:1» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:NOP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:2» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:3» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:4» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:SELECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:5» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BLOCK»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:6» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOOP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:7» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:IF % % ELSE %»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:8» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:9» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_IF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:10» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_TABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:11» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:11»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:12» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:12»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_NON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:13» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:13»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:14» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:14»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:BR_ON_CAST_FAIL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:15» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:15»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:16» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:16»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:17» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:17»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CALL_INDIRECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:18» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:18»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:19» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:19»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:20» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:20»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:21» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:21»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:RETURN_CALL_INDIRECT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:22» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:22»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:23» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:23»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:THROW_REF»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:24» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:24»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TRY_TABLE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:25» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:25»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:26» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:26»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:27» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:27»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOCAL.TEE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:28» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:28»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:29» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:29»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:30» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:30»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:31» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:31»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SET»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:32» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:32»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.SIZE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:33» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:33»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.GROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:34» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:34»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.FILL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:35» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:35»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.COPY»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:36» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:36»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:TABLE.INIT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:37» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:37»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ELEM.DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:38» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:38»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:LOAD»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:39» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:39»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STORE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:40» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:40»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:41» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:41»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:42» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:42»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.LOAD_LANE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:43» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:43»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.STORE_LANE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:44» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:44»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.SIZE»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:45» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:45»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.GROW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:46» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:46»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.FILL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:47» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:47»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.COPY»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:48» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:48»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:MEMORY.INIT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:49» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:49»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:DATA.DROP»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:50» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:50»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:51» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:51»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:52» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:52»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.IS_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:53» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:53»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.AS_NON_NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:54» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:54»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.TEST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:55» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:55»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.CAST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:56» c irt (.«REF.I31»)) n .unmatch n
    unfold SpecTec.«Instr_ok:clause:56»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.EQ»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Instr_ok:clause:57» c irt (.«REF.I31»))
    n (.success (.of
      (⟨{ INS := (.NoEllipses, [.NumT .I32T]),
           OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull .I31HT)]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n
  exact ConstI31Effect.i31_clause_total c irt n

theorem i31_instruction_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (iit : SpecTec.inferinstrtype) (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt .«REF.I31»⟩)
      n (.success (.of iit)) fin) :
    iit =
      (⟨{ INS := (.NoEllipses, [.NumT .I32T]),
           OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull .I31HT)]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
    fin = n := by
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h
      (i31_dispatch_total c irt n)
  cases hout
  exact ⟨rfl, hsupply⟩

theorem i31_clause_of_dispatch
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (iit : SpecTec.inferinstrtype) (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt .«REF.I31»⟩)
      n (.success (.of iit)) fin) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:57» c irt .«REF.I31»)
      n (.success (.of iit)) fin := by
  obtain ⟨hout, hsupply⟩ := i31_instruction_effect c irt iit n fin h
  rw [hout, hsupply]
  exact ConstI31Effect.i31_clause_total c irt n

end properties.wasm_module_ok.ConstI31Dispatch
