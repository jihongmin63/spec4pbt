import properties.wasm_module_ok.ConstructiveBodyIndexedProductions
import properties.wasm_module_ok.ConstructiveBodyOperatorCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyIndexedCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyIndexedCalls

theorem branch_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR x)⟩)
      n (.success (.of result)) finish) : x<c.LABELS.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.BR x) 8 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:8» c stack (.BR x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:8» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem branch_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR x)⟩)
      n (.success (.of result)) finish) :
    ∃ts,c.LABELS[x]?=some ts ∧ result=((⟨(.Ellipses,ts),(.Ellipses,[])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := branch_bound c stack x result n finish h
  let ts := c.LABELS[x]
  have hx : c.LABELS[x]?=some ts := List.getElem?_eq_getElem hb
  exact ⟨ts,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.BR x) _ result n finish
    (branch c stack x ts n hx) h⟩

theorem branchIf_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR_IF x)⟩)
      n (.success (.of result)) finish) : x<c.LABELS.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.BR_IF x) 9 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:9» c stack (.BR_IF x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:9» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem branchIf_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR_IF x)⟩)
      n (.success (.of result)) finish) :
    ∃ts,c.LABELS[x]?=some ts ∧ result=((⟨(.NoEllipses,ts++[.NumT .I32T]),(.NoEllipses,ts)⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := branchIf_bound c stack x result n finish h
  let ts := c.LABELS[x]
  have hx : c.LABELS[x]?=some ts := List.getElem?_eq_getElem hb
  exact ⟨ts,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.BR_IF x) _ result n finish
    (branchIf c stack x ts n hx) h⟩

theorem globalGet_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.GET» x)⟩)
      n (.success (.of result)) finish) : x<c.GLOBALS.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«GLOBAL.GET» x) 28 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:28» c stack (.«GLOBAL.GET» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:28» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem globalGet_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.GET» x)⟩)
      n (.success (.of result)) finish) :
    ∃mu t,c.GLOBALS[x]?=some (.GlobalT mu t) ∧ result=((⟨(.NoEllipses,[]),(.NoEllipses,[t])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := globalGet_bound c stack x result n finish h
  cases he : c.GLOBALS[x] with
  | GlobalT mu t =>
    have hx : c.GLOBALS[x]?=some (.GlobalT mu t) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨mu,t,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«GLOBAL.GET» x) _ result n finish
      (globalGet c stack x mu t n hx) h⟩

theorem globalSet_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.SET» x)⟩)
      n (.success (.of result)) finish) : x<c.GLOBALS.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«GLOBAL.SET» x) 29 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:29» c stack (.«GLOBAL.SET» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:29» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem tableGet_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.GET» x)⟩)
      n (.success (.of result)) finish) : x<c.TABLES.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.GET» x) 30 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:30» c stack (.«TABLE.GET» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:30» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem tableGet_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.GET» x)⟩)
      n (.success (.of result)) finish) :
    ∃addr lim rt,c.TABLES[x]?=some (.TableT addr lim rt) ∧ result=((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[.RefT rt])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := tableGet_bound c stack x result n finish h
  cases he : c.TABLES[x] with
  | TableT addr lim rt =>
    have hx : c.TABLES[x]?=some (.TableT addr lim rt) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨addr,lim,rt,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«TABLE.GET» x) _ result n finish
      (tableGet c stack x addr lim rt n hx) h⟩

theorem tableSet_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.SET» x)⟩)
      n (.success (.of result)) finish) : x<c.TABLES.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.SET» x) 31 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:31» c stack (.«TABLE.SET» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:31» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem tableSet_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.SET» x)⟩)
      n (.success (.of result)) finish) :
    ∃addr lim rt,c.TABLES[x]?=some (.TableT addr lim rt) ∧ result=((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.RefT rt]),(.NoEllipses,[])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := tableSet_bound c stack x result n finish h
  cases he : c.TABLES[x] with
  | TableT addr lim rt =>
    have hx : c.TABLES[x]?=some (.TableT addr lim rt) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨addr,lim,rt,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«TABLE.SET» x) _ result n finish
      (tableSet c stack x addr lim rt n hx) h⟩

theorem tableSize_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.SIZE» x)⟩)
      n (.success (.of result)) finish) : x<c.TABLES.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.SIZE» x) 32 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:32» c stack (.«TABLE.SIZE» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:32» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem tableSize_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.SIZE» x)⟩)
      n (.success (.of result)) finish) :
    ∃addr lim rt,c.TABLES[x]?=some (.TableT addr lim rt) ∧ result=((⟨(.NoEllipses,[]),(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := tableSize_bound c stack x result n finish h
  cases he : c.TABLES[x] with
  | TableT addr lim rt =>
    have hx : c.TABLES[x]?=some (.TableT addr lim rt) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨addr,lim,rt,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«TABLE.SIZE» x) _ result n finish
      (tableSize c stack x addr lim rt n hx) h⟩

theorem tableGrow_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.GROW» x)⟩)
      n (.success (.of result)) finish) : x<c.TABLES.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.GROW» x) 33 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:33» c stack (.«TABLE.GROW» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:33» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem tableGrow_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.GROW» x)⟩)
      n (.success (.of result)) finish) :
    ∃addr lim rt,c.TABLES[x]?=some (.TableT addr lim rt) ∧ result=((⟨(.NoEllipses,[.RefT rt,.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := tableGrow_bound c stack x result n finish h
  cases he : c.TABLES[x] with
  | TableT addr lim rt =>
    have hx : c.TABLES[x]?=some (.TableT addr lim rt) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨addr,lim,rt,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«TABLE.GROW» x) _ result n finish
      (tableGrow c stack x addr lim rt n hx) h⟩

theorem tableFill_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.FILL» x)⟩)
      n (.success (.of result)) finish) : x<c.TABLES.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.FILL» x) 34 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:34» c stack (.«TABLE.FILL» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:34» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem tableFill_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.FILL» x)⟩)
      n (.success (.of result)) finish) :
    ∃addr lim rt,c.TABLES[x]?=some (.TableT addr lim rt) ∧ result=((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.RefT rt,.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := tableFill_bound c stack x result n finish h
  cases he : c.TABLES[x] with
  | TableT addr lim rt =>
    have hx : c.TABLES[x]?=some (.TableT addr lim rt) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨addr,lim,rt,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«TABLE.FILL» x) _ result n finish
      (tableFill c stack x addr lim rt n hx) h⟩

theorem memorySize_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.SIZE» x)⟩)
      n (.success (.of result)) finish) : x<c.MEMS.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.SIZE» x) 44 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:44» c stack (.«MEMORY.SIZE» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:44» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem memorySize_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.SIZE» x)⟩)
      n (.success (.of result)) finish) :
    ∃addr lim,c.MEMS[x]?=some (.MemoryT addr lim) ∧ result=((⟨(.NoEllipses,[]),(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := memorySize_bound c stack x result n finish h
  cases he : c.MEMS[x] with
  | MemoryT addr lim =>
    have hx : c.MEMS[x]?=some (.MemoryT addr lim) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨addr,lim,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«MEMORY.SIZE» x) _ result n finish
      (memorySize c stack x addr lim n hx) h⟩

theorem memoryGrow_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.GROW» x)⟩)
      n (.success (.of result)) finish) : x<c.MEMS.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.GROW» x) 45 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:45» c stack (.«MEMORY.GROW» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:45» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem memoryGrow_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.GROW» x)⟩)
      n (.success (.of result)) finish) :
    ∃addr lim,c.MEMS[x]?=some (.MemoryT addr lim) ∧ result=((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := memoryGrow_bound c stack x result n finish h
  cases he : c.MEMS[x] with
  | MemoryT addr lim =>
    have hx : c.MEMS[x]?=some (.MemoryT addr lim) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨addr,lim,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«MEMORY.GROW» x) _ result n finish
      (memoryGrow c stack x addr lim n hx) h⟩

theorem memoryFill_bound (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.FILL» x)⟩)
      n (.success (.of result)) finish) : x<c.MEMS.length := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.FILL» x) 46 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:46» c stack (.«MEMORY.FILL» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:46» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb _ =>
    cases hb with | guard_true hb => exact hb

theorem memoryFill_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.FILL» x)⟩)
      n (.success (.of result)) finish) :
    ∃addr lim,c.MEMS[x]?=some (.MemoryT addr lim) ∧ result=((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.NumT .I32T,.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[])⟩,[]) : inferinstrtype) ∧ finish=n := by
  have hb := memoryFill_bound c stack x result n finish h
  cases he : c.MEMS[x] with
  | MemoryT addr lim =>
    have hx : c.MEMS[x]?=some (.MemoryT addr lim) := by simpa [he] using (List.getElem?_eq_getElem hb)
    exact ⟨addr,lim,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«MEMORY.FILL» x) _ result n finish
      (memoryFill c stack x addr lim n hx) h⟩

theorem globalSet_lookup (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.SET» x)⟩)
      n (.success (.of result)) finish) : ∃t,c.GLOBALS[x]?=some (.GlobalT .Var t) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«GLOBAL.SET» x) 29 (by decide) rfl (by decide) result n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:29» c stack (.«GLOBAL.SET» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:29» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb body =>
    cases hb
    cases hx : c.GLOBALS[x]? with
    | none => rw [hx] at body; cases body
    | some gt =>
      rw [hx] at body
      cases gt with | GlobalT mu t =>
       cases mu with
       | Var => exact ⟨t,rfl⟩
       | Cons =>
         cases body with | bind_success hg _ =>
          cases hg with | guard_true he => cases he

theorem globalSet_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.SET» x)⟩)
      n (.success (.of result)) finish) :
    ∃t,c.GLOBALS[x]?=some (.GlobalT .Var t) ∧ result=ConstructiveBodyControl.effect [t] [] [] ∧ finish=n := by
  obtain ⟨t,hx⟩ := globalSet_lookup c stack x result n finish h
  exact ⟨t,hx,ConstructiveBodyOperatorCalls.effect_unique c stack (.«GLOBAL.SET» x) _ result n finish
    (globalSet c stack x t n hx) h⟩

theorem elemDrop_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ELEM.DROP» x)⟩)
      n (.success (.of result)) finish) : x<c.ELEMS.length ∧ result=ConstructiveBodyControl.effect [] [] [] ∧ finish=n := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«ELEM.DROP» x) 37 (by decide) rfl (by decide) result n finish).1 h
  have hb : x<c.ELEMS.length := by
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:37» c stack (.«ELEM.DROP» x)) n _ finish at hs
    unfold SpecTec.«Instr_ok:clause:37» at hs
    cases hs with | bind_success hg tail =>
     cases hg
     cases tail with | bind_success hb _ =>
      cases hb with | guard_true hb => exact hb.2
  exact ⟨hb,ConstructiveBodyOperatorCalls.effect_unique c stack (.«ELEM.DROP» x) _ result n finish (elemDrop c stack x n hb) h⟩

theorem dataDrop_original (c : context) (stack : inferresulttype) (x : Nat) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«DATA.DROP» x)⟩)
      n (.success (.of result)) finish) : x<c.DATAS.length ∧ result=ConstructiveBodyControl.effect [] [] [] ∧ finish=n := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«DATA.DROP» x) 49 (by decide) rfl (by decide) result n finish).1 h
  have hb : x<c.DATAS.length := by
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:49» c stack (.«DATA.DROP» x)) n _ finish at hs
    unfold SpecTec.«Instr_ok:clause:49» at hs
    cases hs with | bind_success hg tail =>
     cases hg
     cases tail with | bind_success hb _ =>
      cases hb with | guard_true hb => exact hb.2
  exact ⟨hb,ConstructiveBodyOperatorCalls.effect_unique c stack (.«DATA.DROP» x) _ result n finish (dataDrop c stack x n hb) h⟩


#print axioms globalSet_original
#print axioms tableFill_original
end properties.wasm_module_ok.ConstructiveBodyIndexedCoverage
