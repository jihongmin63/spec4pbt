import properties.wasm_module_ok.ConstructiveBodyDispatch
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace properties.wasm_module_ok.ConstructiveBodyOpcode
open SpecTec properties.wasm_module_ok
-- Proof-only dispatch: no generated AST is inspected by these lemmas.

theorem other0 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠0) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:0» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:0»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:UNREACHABLE»,Bool.false_eq_true,not_false_eq_true]

theorem other1 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠1) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:1» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:1»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:NOP»,Bool.false_eq_true,not_false_eq_true]

theorem other2 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠2) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:2» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:2»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:DROP»,Bool.false_eq_true,not_false_eq_true]

theorem other3 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠3) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:3» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:3»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,Bool.false_eq_true,not_false_eq_true]

theorem other4 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠3) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:4» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:4»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:SELECT»,Bool.false_eq_true,not_false_eq_true]

theorem other5 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠4) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:5» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:5»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BLOCK»,Bool.false_eq_true,not_false_eq_true]

theorem other6 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠5) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:6» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:6»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:LOOP»,Bool.false_eq_true,not_false_eq_true]

theorem other7 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠6) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:7» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:7»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:IF % % ELSE %»,Bool.false_eq_true,not_false_eq_true]

theorem other8 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠7) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:8» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:8»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BR»,Bool.false_eq_true,not_false_eq_true]

theorem other9 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠8) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:9» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:9»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BR_IF»,Bool.false_eq_true,not_false_eq_true]

theorem other10 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠9) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:10» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:10»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BR_TABLE»,Bool.false_eq_true,not_false_eq_true]

theorem other11 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠10) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:11» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:11»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BR_ON_NULL»,Bool.false_eq_true,not_false_eq_true]

theorem other12 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠11) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:12» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:12»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BR_ON_NON_NULL»,Bool.false_eq_true,not_false_eq_true]

theorem other13 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠12) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:13» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:13»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BR_ON_CAST»,Bool.false_eq_true,not_false_eq_true]

theorem other14 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠13) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:14» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:14»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BR_ON_CAST_FAIL»,Bool.false_eq_true,not_false_eq_true]

theorem other15 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠14) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:15» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:15»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:CALL»,Bool.false_eq_true,not_false_eq_true]

theorem other16 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠15) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:16» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:16»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:CALL_REF»,Bool.false_eq_true,not_false_eq_true]

theorem other17 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠16) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:17» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:17»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:CALL_INDIRECT»,Bool.false_eq_true,not_false_eq_true]

theorem other18 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠17) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:18» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:18»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:RETURN»,Bool.false_eq_true,not_false_eq_true]

theorem other19 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠18) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:19» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:19»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:RETURN_CALL»,Bool.false_eq_true,not_false_eq_true]

theorem other20 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠19) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:20» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:20»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:RETURN_CALL_REF»,Bool.false_eq_true,not_false_eq_true]

theorem other21 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠20) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:21» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:21»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:RETURN_CALL_INDIRECT»,Bool.false_eq_true,not_false_eq_true]

theorem other22 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠21) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:22» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:22»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:THROW»,Bool.false_eq_true,not_false_eq_true]

theorem other23 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠22) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:23» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:23»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:THROW_REF»,Bool.false_eq_true,not_false_eq_true]

theorem other24 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠23) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:24» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:24»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TRY_TABLE»,Bool.false_eq_true,not_false_eq_true]

theorem other25 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠24) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:25» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:25»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:LOCAL.GET»,Bool.false_eq_true,not_false_eq_true]

theorem other26 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠25) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:26» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:26»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:LOCAL.SET»,Bool.false_eq_true,not_false_eq_true]

theorem other27 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠26) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:27» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:27»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:LOCAL.TEE»,Bool.false_eq_true,not_false_eq_true]

theorem other28 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠27) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:28» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:28»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:GLOBAL.GET»,Bool.false_eq_true,not_false_eq_true]

theorem other29 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠28) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:29» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:29»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:GLOBAL.SET»,Bool.false_eq_true,not_false_eq_true]

theorem other30 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠29) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:30» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:30»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TABLE.GET»,Bool.false_eq_true,not_false_eq_true]

theorem other31 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠30) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:31» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:31»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TABLE.SET»,Bool.false_eq_true,not_false_eq_true]

theorem other32 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠31) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:32» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:32»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TABLE.SIZE»,Bool.false_eq_true,not_false_eq_true]

theorem other33 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠32) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:33» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:33»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TABLE.GROW»,Bool.false_eq_true,not_false_eq_true]

theorem other34 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠33) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:34» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:34»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TABLE.FILL»,Bool.false_eq_true,not_false_eq_true]

theorem other35 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠34) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:35» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:35»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TABLE.COPY»,Bool.false_eq_true,not_false_eq_true]

theorem other36 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠35) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:36» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:36»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TABLE.INIT»,Bool.false_eq_true,not_false_eq_true]

theorem other37 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠36) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:37» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:37»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ELEM.DROP»,Bool.false_eq_true,not_false_eq_true]

theorem other38 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠37) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:38» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:38»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:LOAD»,Bool.false_eq_true,not_false_eq_true]

theorem other39 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠38) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:39» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:39»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:STORE»,Bool.false_eq_true,not_false_eq_true]

theorem other40 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠39) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:40» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:40»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.LOAD»,Bool.false_eq_true,not_false_eq_true]

theorem other41 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠40) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:41» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:41»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.STORE»,Bool.false_eq_true,not_false_eq_true]

theorem other42 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠41) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:42» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:42»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.LOAD_LANE»,Bool.false_eq_true,not_false_eq_true]

theorem other43 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠42) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:43» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:43»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.STORE_LANE»,Bool.false_eq_true,not_false_eq_true]

theorem other44 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠43) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:44» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:44»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:MEMORY.SIZE»,Bool.false_eq_true,not_false_eq_true]

theorem other45 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠44) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:45» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:45»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:MEMORY.GROW»,Bool.false_eq_true,not_false_eq_true]

theorem other46 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠45) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:46» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:46»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:MEMORY.FILL»,Bool.false_eq_true,not_false_eq_true]

theorem other47 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠46) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:47» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:47»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:MEMORY.COPY»,Bool.false_eq_true,not_false_eq_true]

theorem other48 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠47) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:48» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:48»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:MEMORY.INIT»,Bool.false_eq_true,not_false_eq_true]

theorem other49 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠48) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:49» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:49»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:DATA.DROP»,Bool.false_eq_true,not_false_eq_true]

theorem other50 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠49) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:50» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:50»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:REF.NULL»,Bool.false_eq_true,not_false_eq_true]

theorem other51 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠50) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:51» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:51»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:REF.FUNC»,Bool.false_eq_true,not_false_eq_true]

theorem other52 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠51) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:52» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:52»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:REF.IS_NULL»,Bool.false_eq_true,not_false_eq_true]

theorem other53 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠52) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:53» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:53»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:REF.AS_NON_NULL»,Bool.false_eq_true,not_false_eq_true]

theorem other54 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠53) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:54» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:54»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:REF.TEST»,Bool.false_eq_true,not_false_eq_true]

theorem other55 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠54) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:55» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:55»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:REF.CAST»,Bool.false_eq_true,not_false_eq_true]

theorem other56 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠55) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:56» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:56»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:REF.EQ»,Bool.false_eq_true,not_false_eq_true]

theorem other57 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠56) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:57» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:57»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:REF.I31»,Bool.false_eq_true,not_false_eq_true]

theorem other58 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠57) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:58» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:58»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:I31.GET»,Bool.false_eq_true,not_false_eq_true]

theorem other59 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠58) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:59» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:59»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:STRUCT.NEW»,Bool.false_eq_true,not_false_eq_true]

theorem other60 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠58) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:60» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:60»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:STRUCT.NEW»,Bool.false_eq_true,not_false_eq_true]

theorem other61 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠59) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:61» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:61»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:STRUCT.GET»,Bool.false_eq_true,not_false_eq_true]

theorem other62 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠59) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:62» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:62»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:STRUCT.GET»,Bool.false_eq_true,not_false_eq_true]

theorem other63 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠60) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:63» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:63»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:STRUCT.SET»,Bool.false_eq_true,not_false_eq_true]

theorem other64 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠61) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:64» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:64»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.NEW»,Bool.false_eq_true,not_false_eq_true]

theorem other65 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠61) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:65» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:65»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.NEW»,Bool.false_eq_true,not_false_eq_true]

theorem other66 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠62) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:66» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:66»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»,Bool.false_eq_true,not_false_eq_true]

theorem other67 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠63) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:67» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:67»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.NEW_ELEM»,Bool.false_eq_true,not_false_eq_true]

theorem other68 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠64) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:68» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:68»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.NEW_DATA»,Bool.false_eq_true,not_false_eq_true]

theorem other69 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠65) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:69» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:69»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.GET»,Bool.false_eq_true,not_false_eq_true]

theorem other70 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠65) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:70» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:70»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.GET»,Bool.false_eq_true,not_false_eq_true]

theorem other71 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠66) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:71» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:71»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.SET»,Bool.false_eq_true,not_false_eq_true]

theorem other72 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠67) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:72» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:72»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.LEN»,Bool.false_eq_true,not_false_eq_true]

theorem other73 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠68) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:73» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:73»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.COPY»,Bool.false_eq_true,not_false_eq_true]

theorem other74 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠69) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:74» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:74»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.FILL»,Bool.false_eq_true,not_false_eq_true]

theorem other75 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠70) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:75» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:75»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.INIT_DATA»,Bool.false_eq_true,not_false_eq_true]

theorem other76 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠71) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:76» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:76»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:ARRAY.INIT_ELEM»,Bool.false_eq_true,not_false_eq_true]

theorem other77 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠72) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:77» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:77»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:EXTERN.CONVERT»,Bool.false_eq_true,not_false_eq_true]

theorem other78 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠73) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:78» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:78»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:CONST»,Bool.false_eq_true,not_false_eq_true]

theorem other79 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠74) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:79» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:79»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:TEST»,Bool.false_eq_true,not_false_eq_true]

theorem other80 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠75) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:80» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:80»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:COMPARE»,Bool.false_eq_true,not_false_eq_true]

theorem other81 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠76) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:81» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:81»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:UNARY»,Bool.false_eq_true,not_false_eq_true]

theorem other82 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠77) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:82» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:82»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:BINOP»,Bool.false_eq_true,not_false_eq_true]

theorem other83 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠78) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:83» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:83»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:CONVERT»,Bool.false_eq_true,not_false_eq_true]

theorem other84 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠79) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:84» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:84»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.CONST»,Bool.false_eq_true,not_false_eq_true]

theorem other85 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠80) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:85» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:85»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.TEST»,Bool.false_eq_true,not_false_eq_true]

theorem other86 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠81) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:86» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:86»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.UNARY»,Bool.false_eq_true,not_false_eq_true]

theorem other87 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠82) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:87» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:87»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.BINARY»,Bool.false_eq_true,not_false_eq_true]

theorem other88 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠83) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:88» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:88»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.TERNARY»,Bool.false_eq_true,not_false_eq_true]

theorem other89 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠84) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:89» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:89»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.COMPARE»,Bool.false_eq_true,not_false_eq_true]

theorem other90 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠85) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:90» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:90»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.CONVERT»,Bool.false_eq_true,not_false_eq_true]

theorem other91 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠86) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:91» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:91»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.SHIFT»,Bool.false_eq_true,not_false_eq_true]

theorem other92 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠87) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:92» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:92»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.BITMASK»,Bool.false_eq_true,not_false_eq_true]

theorem other93 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠88) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:93» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:93»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.TESTBITS»,Bool.false_eq_true,not_false_eq_true]

theorem other94 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠89) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:94» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:94»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.UNARYBITS»,Bool.false_eq_true,not_false_eq_true]

theorem other95 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠90) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:95» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:95»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.BINARYBITS»,Bool.false_eq_true,not_false_eq_true]

theorem other96 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠91) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:96» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:96»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.TERNARYBITS»,Bool.false_eq_true,not_false_eq_true]

theorem other97 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠92) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:97» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:97»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.SPLAT»,Bool.false_eq_true,not_false_eq_true]

theorem other98 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠93) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:98» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:98»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.EXTRACT»,Bool.false_eq_true,not_false_eq_true]

theorem other99 (c : context) (stack : inferresulttype) (i : instr) (n : Nat)
    (h : i.ctorIdx≠94) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:99» c stack i) n .unmatch n := by
  unfold SpecTec.«Instr_ok:clause:99»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  cases i <;> simp_all [instr.ctorIdx,SpecTec.«exec:match:instr:VEC.REPLACE»,Bool.false_eq_true,not_false_eq_true]

def ruleOpcode : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | 9 => 8
  | 10 => 9
  | 11 => 10
  | 12 => 11
  | 13 => 12
  | 14 => 13
  | 15 => 14
  | 16 => 15
  | 17 => 16
  | 18 => 17
  | 19 => 18
  | 20 => 19
  | 21 => 20
  | 22 => 21
  | 23 => 22
  | 24 => 23
  | 25 => 24
  | 26 => 25
  | 27 => 26
  | 28 => 27
  | 29 => 28
  | 30 => 29
  | 31 => 30
  | 32 => 31
  | 33 => 32
  | 34 => 33
  | 35 => 34
  | 36 => 35
  | 37 => 36
  | 38 => 37
  | 39 => 38
  | 40 => 39
  | 41 => 40
  | 42 => 41
  | 43 => 42
  | 44 => 43
  | 45 => 44
  | 46 => 45
  | 47 => 46
  | 48 => 47
  | 49 => 48
  | 50 => 49
  | 51 => 50
  | 52 => 51
  | 53 => 52
  | 54 => 53
  | 55 => 54
  | 56 => 55
  | 57 => 56
  | 58 => 57
  | 59 => 58
  | 60 => 58
  | 61 => 59
  | 62 => 59
  | 63 => 60
  | 64 => 61
  | 65 => 61
  | 66 => 62
  | 67 => 63
  | 68 => 64
  | 69 => 65
  | 70 => 65
  | 71 => 66
  | 72 => 67
  | 73 => 68
  | 74 => 69
  | 75 => 70
  | 76 => 71
  | 77 => 72
  | 78 => 73
  | 79 => 74
  | 80 => 75
  | 81 => 76
  | 82 => 77
  | 83 => 78
  | 84 => 79
  | 85 => 80
  | 86 => 81
  | 87 => 82
  | 88 => 83
  | 89 => 84
  | 90 => 85
  | 91 => 86
  | 92 => 87
  | 93 => 88
  | 94 => 89
  | 95 => 90
  | 96 => 91
  | 97 => 92
  | 98 => 93
  | 99 => 94
  | _ => 100

theorem other (c : context) (stack : inferresulttype) (i : instr) (n k : Nat)
    (hk : k<100) (h : i.ctorIdx≠ruleOpcode k) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (((SpecTec.Instr_ok_clauses c stack i)[k]'(by simpa only [SpecTec.Instr_ok_clauses,List.length_cons,List.length_nil] using hk)) ())
      n .unmatch n := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 ∨ k=19 ∨ k=20 ∨ k=21 ∨ k=22 ∨ k=23 ∨ k=24 ∨ k=25 ∨ k=26 ∨ k=27 ∨ k=28 ∨ k=29 ∨ k=30 ∨ k=31 ∨ k=32 ∨ k=33 ∨ k=34 ∨ k=35 ∨ k=36 ∨ k=37 ∨ k=38 ∨ k=39 ∨ k=40 ∨ k=41 ∨ k=42 ∨ k=43 ∨ k=44 ∨ k=45 ∨ k=46 ∨ k=47 ∨ k=48 ∨ k=49 ∨ k=50 ∨ k=51 ∨ k=52 ∨ k=53 ∨ k=54 ∨ k=55 ∨ k=56 ∨ k=57 ∨ k=58 ∨ k=59 ∨ k=60 ∨ k=61 ∨ k=62 ∨ k=63 ∨ k=64 ∨ k=65 ∨ k=66 ∨ k=67 ∨ k=68 ∨ k=69 ∨ k=70 ∨ k=71 ∨ k=72 ∨ k=73 ∨ k=74 ∨ k=75 ∨ k=76 ∨ k=77 ∨ k=78 ∨ k=79 ∨ k=80 ∨ k=81 ∨ k=82 ∨ k=83 ∨ k=84 ∨ k=85 ∨ k=86 ∨ k=87 ∨ k=88 ∨ k=89 ∨ k=90 ∨ k=91 ∨ k=92 ∨ k=93 ∨ k=94 ∨ k=95 ∨ k=96 ∨ k=97 ∨ k=98 ∨ k=99 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact other0 c stack i n h
  · exact other1 c stack i n h
  · exact other2 c stack i n h
  · exact other3 c stack i n h
  · exact other4 c stack i n h
  · exact other5 c stack i n h
  · exact other6 c stack i n h
  · exact other7 c stack i n h
  · exact other8 c stack i n h
  · exact other9 c stack i n h
  · exact other10 c stack i n h
  · exact other11 c stack i n h
  · exact other12 c stack i n h
  · exact other13 c stack i n h
  · exact other14 c stack i n h
  · exact other15 c stack i n h
  · exact other16 c stack i n h
  · exact other17 c stack i n h
  · exact other18 c stack i n h
  · exact other19 c stack i n h
  · exact other20 c stack i n h
  · exact other21 c stack i n h
  · exact other22 c stack i n h
  · exact other23 c stack i n h
  · exact other24 c stack i n h
  · exact other25 c stack i n h
  · exact other26 c stack i n h
  · exact other27 c stack i n h
  · exact other28 c stack i n h
  · exact other29 c stack i n h
  · exact other30 c stack i n h
  · exact other31 c stack i n h
  · exact other32 c stack i n h
  · exact other33 c stack i n h
  · exact other34 c stack i n h
  · exact other35 c stack i n h
  · exact other36 c stack i n h
  · exact other37 c stack i n h
  · exact other38 c stack i n h
  · exact other39 c stack i n h
  · exact other40 c stack i n h
  · exact other41 c stack i n h
  · exact other42 c stack i n h
  · exact other43 c stack i n h
  · exact other44 c stack i n h
  · exact other45 c stack i n h
  · exact other46 c stack i n h
  · exact other47 c stack i n h
  · exact other48 c stack i n h
  · exact other49 c stack i n h
  · exact other50 c stack i n h
  · exact other51 c stack i n h
  · exact other52 c stack i n h
  · exact other53 c stack i n h
  · exact other54 c stack i n h
  · exact other55 c stack i n h
  · exact other56 c stack i n h
  · exact other57 c stack i n h
  · exact other58 c stack i n h
  · exact other59 c stack i n h
  · exact other60 c stack i n h
  · exact other61 c stack i n h
  · exact other62 c stack i n h
  · exact other63 c stack i n h
  · exact other64 c stack i n h
  · exact other65 c stack i n h
  · exact other66 c stack i n h
  · exact other67 c stack i n h
  · exact other68 c stack i n h
  · exact other69 c stack i n h
  · exact other70 c stack i n h
  · exact other71 c stack i n h
  · exact other72 c stack i n h
  · exact other73 c stack i n h
  · exact other74 c stack i n h
  · exact other75 c stack i n h
  · exact other76 c stack i n h
  · exact other77 c stack i n h
  · exact other78 c stack i n h
  · exact other79 c stack i n h
  · exact other80 c stack i n h
  · exact other81 c stack i n h
  · exact other82 c stack i n h
  · exact other83 c stack i n h
  · exact other84 c stack i n h
  · exact other85 c stack i n h
  · exact other86 c stack i n h
  · exact other87 c stack i n h
  · exact other88 c stack i n h
  · exact other89 c stack i n h
  · exact other90 c stack i n h
  · exact other91 c stack i n h
  · exact other92 c stack i n h
  · exact other93 c stack i n h
  · exact other94 c stack i n h
  · exact other95 c stack i n h
  · exact other96 c stack i n h
  · exact other97 c stack i n h
  · exact other98 c stack i n h
  · exact other99 c stack i n h

#print axioms other
end properties.wasm_module_ok.ConstructiveBodyOpcode
