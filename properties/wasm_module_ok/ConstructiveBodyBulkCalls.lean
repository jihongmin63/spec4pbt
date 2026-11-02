import properties.wasm_module_ok.ConstructiveBodyAddressMinimum
import properties.wasm_module_ok.ConstructiveBodyReferenceMatcher
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBulkCalls
open SpecTec properties.wasm_module_ok

def copyInputs (a b : addrtype) : List valtype :=
  [.NumT (AddrNumtypeDecision.numtypeOfAddrtype a),.NumT (AddrNumtypeDecision.numtypeOfAddrtype b),
   .NumT (AddrNumtypeDecision.numtypeOfAddrtype (ConstructiveBodyAddressMinimum.minimum a b))]
def initInputs (a : addrtype) : List valtype :=
  [.NumT (AddrNumtypeDecision.numtypeOfAddrtype a),.NumT .I32T,.NumT .I32T]

theorem tableCopy (c : context) (stack : inferresulttype) (x y : Nat) (a : addrtype) (la : limits) (ra : reftype)
    (b : addrtype) (lb : limits) (rb : reftype)
    (hx : c.TABLES[x]?=some (.TableT a la ra))
    (hy : c.TABLES[y]?=some (.TableT b lb rb))
    (hm : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_reftype» c.TYPES rb ra⟩) s (.success (.of true)) s) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.COPY» x y)⟩)
      n (.success (.of (ConstructiveBodyControl.effect (copyInputs a b) [] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.COPY» x y) 35 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:35» c stack (.«TABLE.COPY» x y)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:35»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply SpecTecExecution.Eval.bind_success (hm n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total a n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total b n)
  apply SpecTecExecution.Eval.bind_success (ConstructiveBodyAddressMinimum.total a b n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total (ConstructiveBodyAddressMinimum.minimum a b) n)
  exact SpecTecExecution.Eval.pure _

theorem tableInit (c : context) (stack : inferresulttype) (x y : Nat) (a : addrtype) (la : limits) (ra : reftype) (rb : reftype)
    (hx : c.TABLES[x]?=some (.TableT a la ra))
    (hy : c.ELEMS[y]?=some rb)
    (hm : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_reftype» c.TYPES rb ra⟩) s (.success (.of true)) s) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.INIT» x y)⟩)
      n (.success (.of (ConstructiveBodyControl.effect (initInputs a) [] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.INIT» x y) 36 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:36» c stack (.«TABLE.INIT» x y)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:36»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply SpecTecExecution.Eval.bind_success (hm n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total a n)
  exact SpecTecExecution.Eval.pure _

theorem memoryCopy (c : context) (stack : inferresulttype) (x y : Nat) (a : addrtype) (la : limits)
    (b : addrtype) (lb : limits)
    (hx : c.MEMS[x]?=some (.MemoryT a la))
    (hy : c.MEMS[y]?=some (.MemoryT b lb)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.COPY» x y)⟩)
      n (.success (.of (ConstructiveBodyControl.effect (copyInputs a b) [] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.COPY» x y) 47 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:47» c stack (.«MEMORY.COPY» x y)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:47»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total a n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total b n)
  apply SpecTecExecution.Eval.bind_success (ConstructiveBodyAddressMinimum.total a b n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total (ConstructiveBodyAddressMinimum.minimum a b) n)
  exact SpecTecExecution.Eval.pure _

theorem memoryInit (c : context) (stack : inferresulttype) (x y : Nat) (a : addrtype) (la : limits)
    (hx : c.MEMS[x]?=some (.MemoryT a la))
    (hy : y<c.DATAS.length) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.INIT» x y)⟩)
      n (.success (.of (ConstructiveBodyControl.effect (initInputs a) [] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.INIT» x y) 48 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:48» c stack (.«MEMORY.INIT» x y)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:48»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true ⟨Nat.zero_le _,hy⟩)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total a n)
  exact SpecTecExecution.Eval.pure _

#print axioms tableCopy
#print axioms memoryInit
end properties.wasm_module_ok.ConstructiveBodyBulkCalls
