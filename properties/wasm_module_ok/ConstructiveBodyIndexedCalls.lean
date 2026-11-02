import properties.wasm_module_ok.ConstructiveBodyLookup
import properties.wasm_module_ok.AddrNumtypeDecision
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyIndexedCalls
open SpecTec properties.wasm_module_ok

theorem branch (c : context) (stack : inferresulttype) (x : Nat) (ts : List valtype) (n : Nat)
    (hx : c.LABELS[x]?=some ts) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR x)⟩)
      n (.success (.of ((⟨(.Ellipses,ts),(.Ellipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BR x) 8 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:8» c stack (.BR x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:8»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  exact SpecTecExecution.Eval.pure _

theorem branchIf (c : context) (stack : inferresulttype) (x : Nat) (ts : List valtype) (n : Nat)
    (hx : c.LABELS[x]?=some ts) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR_IF x)⟩)
      n (.success (.of ((⟨(.NoEllipses,ts++[.NumT .I32T]),(.NoEllipses,ts)⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BR_IF x) 9 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:9» c stack (.BR_IF x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:9»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  exact SpecTecExecution.Eval.pure _

theorem globalGet (c : context) (stack : inferresulttype) (x : Nat) (mu : SpecTec.mut) (t : valtype) (n : Nat)
    (hx : c.GLOBALS[x]?=some (.GlobalT mu t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.GET» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[]),(.NoEllipses,[t])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«GLOBAL.GET» x) 28 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:28» c stack (.«GLOBAL.GET» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:28»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  exact SpecTecExecution.Eval.pure _

theorem globalSet (c : context) (stack : inferresulttype) (x : Nat) (t : valtype) (n : Nat)
    (hx : c.GLOBALS[x]?=some (.GlobalT .Var t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.SET» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[t]),(.NoEllipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«GLOBAL.SET» x) 29 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:29» c stack (.«GLOBAL.SET» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:29»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem tableGet (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (n : Nat)
    (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.GET» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[.RefT rt])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.GET» x) 30 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:30» c stack (.«TABLE.GET» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:30»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem tableSet (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (n : Nat)
    (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.SET» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.RefT rt]),(.NoEllipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.SET» x) 31 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:31» c stack (.«TABLE.SET» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:31»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem tableSize (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (n : Nat)
    (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.SIZE» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[]),(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.SIZE» x) 32 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:32» c stack (.«TABLE.SIZE» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:32»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem tableGrow (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (n : Nat)
    (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.GROW» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[.RefT rt,.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.GROW» x) 33 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:33» c stack (.«TABLE.GROW» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:33»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem tableFill (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (n : Nat)
    (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.FILL» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.RefT rt,.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.FILL» x) 34 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:34» c stack (.«TABLE.FILL» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:34»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem memorySize (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits) (n : Nat)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.SIZE» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[]),(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.SIZE» x) 44 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:44» c stack (.«MEMORY.SIZE» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:44»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem memoryGrow (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits) (n : Nat)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.GROW» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.GROW» x) 45 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:45» c stack (.«MEMORY.GROW» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:45»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem memoryFill (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits) (n : Nat)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.FILL» x)⟩)
      n (.success (.of ((⟨(.NoEllipses,[.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.NumT .I32T,.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)]),(.NoEllipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.FILL» x) 46 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:46» c stack (.«MEMORY.FILL» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:46»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem elemDrop (c : context) (stack : inferresulttype) (x n : Nat) (hx : x<c.ELEMS.length) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ELEM.DROP» x)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [] [] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ELEM.DROP» x) 37 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:37» c stack (.«ELEM.DROP» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:37»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true ⟨Nat.zero_le _,hx⟩)
  exact SpecTecExecution.Eval.pure _

theorem dataDrop (c : context) (stack : inferresulttype) (x n : Nat) (hx : x<c.DATAS.length) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«DATA.DROP» x)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [] [] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«DATA.DROP» x) 49 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:49» c stack (.«DATA.DROP» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:49»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true ⟨Nat.zero_le _,hx⟩)
  exact SpecTecExecution.Eval.pure _


#print axioms tableFill
#print axioms memoryGrow
end properties.wasm_module_ok.ConstructiveBodyIndexedCalls
