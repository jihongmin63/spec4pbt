import properties.wasm_module_ok.ConstructiveBodyMemoryBounds
import properties.wasm_module_ok.ConstructiveBodyIndexedTypes
import properties.wasm_module_ok.AddrNumtypeDecision
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryCalls
open SpecTec properties.wasm_module_ok

theorem vec_size (v : vectype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨Int,Call.«$vec_size» v⟩)
      n (.success (.of (16 : Int))) n := by
  cases v
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$vec_size_clauses» .V128T)) n _ n
  apply SpecTecExecution.tryClauses_cons_success
  unfold SpecTec.«$vec_size:clause:0»
  exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)

theorem load (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits)
    (op : loadop_) (ty : numtype)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim))
    (ho : ∀n,SpecTecExecution.Eval SpecTec.Body (.call ⟨numtype,Call.Loadop_ok c op⟩)
      n (.success (.of ty)) n)
    (n : Nat) : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«LOAD» x op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)] [.NumT ty]))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«LOAD» x op) 38 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:38» c stack (.«LOAD» x op)) n _ n
  unfold SpecTec.«Instr_ok:clause:38»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (ho n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem store (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits)
    (op : storeop_) (ty : numtype)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim))
    (ho : ∀n,SpecTecExecution.Eval SpecTec.Body (.call ⟨numtype,Call.Storeop_ok c op⟩)
      n (.success (.of ty)) n)
    (n : Nat) : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«STORE» x op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.NumT ty] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«STORE» x op) 39 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:39» c stack (.«STORE» x op)) n _ n
  unfold SpecTec.«Instr_ok:clause:39»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (ho n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem vload (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits)
    (op : vloadop_) (ty : vectype)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim))
    (ho : ∀n,SpecTecExecution.Eval SpecTec.Body (.call ⟨vectype,Call.Vloadop_ok c op⟩)
      n (.success (.of ty)) n)
    (n : Nat) : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.LOAD» x op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)] [.VecT ty]))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.LOAD» x op) 40 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:40» c stack (.«VEC.LOAD» x op)) n _ n
  unfold SpecTec.«Instr_ok:clause:40»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (ho n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem vstore (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits)
    (op : vstoreop_) (ty : vectype)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim))
    (ho : ∀n,SpecTecExecution.Eval SpecTec.Body (.call ⟨vectype,Call.Vstoreop_ok c op⟩)
      n (.success (.of ty)) n)
    (n : Nat) : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.STORE» x op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.VecT ty] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.STORE» x op) 41 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:41» c stack (.«VEC.STORE» x op)) n _ n
  unfold SpecTec.«Instr_ok:clause:41»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (ho n)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem laneLoad (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits)
    (op : vlaneop_) (ty : vectype) (lane : Int)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim))
    (ho : ∀n,SpecTecExecution.Eval SpecTec.Body (.call ⟨vectype,Call.Vlaneop_ok c op⟩)
      n (.success (.of ty)) n)
    (hl : lane<Int.tdiv 16 (ConstructiveBodyScalarSizes.packSize op.PACK))
    (n : Nat) : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.LOAD_LANE» x op lane)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.VecT ty] [.VecT ty]))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.LOAD_LANE» x op lane) 42 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:42» c stack (.«VEC.LOAD_LANE» x op lane)) n _ n
  unfold SpecTec.«Instr_ok:clause:42»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (ho n)
  apply SpecTecExecution.Eval.bind_success (vec_size ty n)
  apply SpecTecExecution.Eval.bind_success (ConstructiveBodyScalarSizes.pack_size op.PACK n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.orElse_success (SpecTecExecution.Eval.guard_true
    (by cases op.PACK <;> decide)))
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hl)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

theorem laneStore (c : context) (stack : inferresulttype) (x : Nat) (addr : addrtype) (lim : limits)
    (op : vlaneop_) (ty : vectype) (lane : Int)
    (hx : c.MEMS[x]?=some (.MemoryT addr lim))
    (ho : ∀n,SpecTecExecution.Eval SpecTec.Body (.call ⟨vectype,Call.Vlaneop_ok c op⟩)
      n (.success (.of ty)) n)
    (hl : lane<Int.tdiv 16 (ConstructiveBodyScalarSizes.packSize op.PACK))
    (n : Nat) : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.STORE_LANE» x op lane)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),.VecT ty] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.STORE_LANE» x op lane) 43 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:43» c stack (.«VEC.STORE_LANE» x op lane)) n _ n
  unfold SpecTec.«Instr_ok:clause:43»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (ho n)
  apply SpecTecExecution.Eval.bind_success (vec_size ty n)
  apply SpecTecExecution.Eval.bind_success (ConstructiveBodyScalarSizes.pack_size op.PACK n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.orElse_success (SpecTecExecution.Eval.guard_true
    (by cases op.PACK <;> decide)))
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hl)
  apply SpecTecExecution.Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact SpecTecExecution.Eval.pure _

#print axioms laneStore
end properties.wasm_module_ok.ConstructiveBodyMemoryCalls
