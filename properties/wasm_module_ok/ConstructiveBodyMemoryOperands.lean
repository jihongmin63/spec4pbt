import properties.wasm_module_ok.ConstructiveBodyMemoryCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryOperands
open SpecTec properties.wasm_module_ok ConstructiveBodyMemoryBounds ConstructiveBodyScalarSizes

def OffsetBound : addrtype → Nat → Prop
  | .I32AT,offset => offset<4294967296
  | .I64AT,_ => True

theorem scalar_size (ty : numtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨Int,Call.«$num_size» ty⟩)
      n (.success (.of (Int.ofNat (2^numLog ty)))) n := by
  simpa only [num_pow] using num_size ty n

theorem loadop_ok_some (c : context) (ty : numtype) (align offset : Nat) (pt : packtype) (ext : extension)
    (addr : addrtype) (lim : limits) (hx : c.MEMS[0]?=some (.MemoryT addr lim))
    (hoff : OffsetBound addr offset)
    (hp : packSize pt<Int.ofNat (2^numLog ty))
    (ha : align≤packLog pt) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨numtype,Call.Loadop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : loadop_)⟩)
      n (.success (.of ty)) n := by
  have hlog : packLog pt<4096 := by cases pt <;> decide
  have halign := (alignment align (packLog pt) hlog).2 ha
  rw [←pack_pow] at halign
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Loadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : loadop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Loadop_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
    apply SpecTecExecution.Eval.bind_success (pack_ok (2^numLog ty) pt n hp)
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hoff)
    exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Loadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : loadop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Loadop_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
      apply SpecTecExecution.Eval.bind_success (pack_ok (2^numLog ty) pt n hp)
      apply SpecTecExecution.Eval.bind_success (pack_size pt n)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
      rw [hx]
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Loadop_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
    apply SpecTecExecution.Eval.bind_success (pack_ok (2^numLog ty) pt n hp)
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    exact SpecTecExecution.Eval.pure _

theorem loadop_ok_none (c : context) (ty : numtype) (align offset : Nat)
    (addr : addrtype) (lim : limits) (hx : c.MEMS[0]?=some (.MemoryT addr lim))
    (hoff : OffsetBound addr offset)
    (ha : align≤numLog ty) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨numtype,Call.Loadop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : loadop_)⟩)
      n (.success (.of ty)) n := by
  have hlog : numLog ty<4096 := by cases ty <;> decide
  have halign := (alignment align (numLog ty) hlog).2 ha
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Loadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : loadop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Loadop_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Loadop_ok:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Loadop_ok:clause:2»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hoff)
    exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Loadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : loadop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Loadop_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Loadop_ok:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Loadop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
      rw [hx]
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Loadop_ok:clause:3»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    exact SpecTecExecution.Eval.pure _

theorem storeop_ok_some (c : context) (ty : numtype) (align offset : Nat) (pt : packtype)
    (addr : addrtype) (lim : limits) (hx : c.MEMS[0]?=some (.MemoryT addr lim))
    (hoff : OffsetBound addr offset)
    (hp : packSize pt<Int.ofNat (2^numLog ty))
    (ha : align≤packLog pt) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨numtype,Call.Storeop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some pt } : storeop_)⟩)
      n (.success (.of ty)) n := by
  have hlog : packLog pt<4096 := by cases pt <;> decide
  have halign := (alignment align (packLog pt) hlog).2 ha
  rw [←pack_pow] at halign
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Storeop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some pt } : storeop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Storeop_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
    apply SpecTecExecution.Eval.bind_success (pack_ok (2^numLog ty) pt n hp)
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hoff)
    exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Storeop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some pt } : storeop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Storeop_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
      apply SpecTecExecution.Eval.bind_success (pack_ok (2^numLog ty) pt n hp)
      apply SpecTecExecution.Eval.bind_success (pack_size pt n)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
      rw [hx]
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Storeop_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
    apply SpecTecExecution.Eval.bind_success (pack_ok (2^numLog ty) pt n hp)
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    exact SpecTecExecution.Eval.pure _

theorem storeop_ok_none (c : context) (ty : numtype) (align offset : Nat)
    (addr : addrtype) (lim : limits) (hx : c.MEMS[0]?=some (.MemoryT addr lim))
    (hoff : OffsetBound addr offset)
    (ha : align≤numLog ty) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨numtype,Call.Storeop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : storeop_)⟩)
      n (.success (.of ty)) n := by
  have hlog : numLog ty<4096 := by cases ty <;> decide
  have halign := (alignment align (numLog ty) hlog).2 ha
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Storeop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : storeop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Storeop_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Storeop_ok:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Storeop_ok:clause:2»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hoff)
    exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Storeop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : storeop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Storeop_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Storeop_ok:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Storeop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
      rw [hx]
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Storeop_ok:clause:3»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (scalar_size ty n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    exact SpecTecExecution.Eval.pure _

theorem vloadop_ok_some (c : context) (ty : vectype) (align offset : Nat) (pt : packtype) (ext : vextension)
    (addr : addrtype) (lim : limits) (hx : c.MEMS[0]?=some (.MemoryT addr lim))
    (hoff : OffsetBound addr offset)
    (hp : packSize pt<Int.ofNat (2^4))
    (ha : align≤packLog pt) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨vectype,Call.Vloadop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : vloadop_)⟩)
      n (.success (.of ty)) n := by
  have hlog : packLog pt<4096 := by cases pt <;> decide
  have halign := (alignment align (packLog pt) hlog).2 ha
  rw [←pack_pow] at halign
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Vloadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : vloadop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vloadop_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
    apply SpecTecExecution.Eval.bind_success (pack_ok (2^4) pt n hp)
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hoff)
    exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Vloadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=some (pt,ext) } : vloadop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vloadop_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
      apply SpecTecExecution.Eval.bind_success (pack_ok (2^4) pt n hp)
      apply SpecTecExecution.Eval.bind_success (pack_size pt n)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
      rw [hx]
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vloadop_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
    apply SpecTecExecution.Eval.bind_success (pack_ok (2^4) pt n hp)
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    exact SpecTecExecution.Eval.pure _

theorem vloadop_ok_none (c : context) (ty : vectype) (align offset : Nat)
    (addr : addrtype) (lim : limits) (hx : c.MEMS[0]?=some (.MemoryT addr lim))
    (hoff : OffsetBound addr offset)
    (ha : align≤4) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨vectype,Call.Vloadop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : vloadop_)⟩)
      n (.success (.of ty)) n := by
  have hlog : 4<4096 := by decide
  have halign := (alignment align (4) hlog).2 ha
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Vloadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : vloadop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vloadop_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vloadop_ok:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vloadop_ok:clause:2»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hoff)
    exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Vloadop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=none } : vloadop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vloadop_ok:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vloadop_ok:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vloadop_ok:clause:2»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
      rw [hx]
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vloadop_ok:clause:3»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    exact SpecTecExecution.Eval.pure _

theorem vstoreop_ok_void (c : context) (ty : vectype) (align offset : Nat)
    (addr : addrtype) (lim : limits) (hx : c.MEMS[0]?=some (.MemoryT addr lim))
    (hoff : OffsetBound addr offset)
    (ha : align≤4) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨vectype,Call.Vstoreop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=.VOID } : vstoreop_)⟩)
      n (.success (.of ty)) n := by
  have hlog : 4<4096 := by decide
  have halign := (alignment align (4) hlog).2 ha
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Vstoreop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=.VOID } : vstoreop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vstoreop_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hoff)
    exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Vstoreop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=.VOID } : vstoreop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vstoreop_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
      rw [hx]
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vstoreop_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    exact SpecTecExecution.Eval.pure _

theorem vlaneop_ok_pack (c : context) (ty : vectype) (align offset : Nat) (pt : packtype)
    (addr : addrtype) (lim : limits) (hx : c.MEMS[0]?=some (.MemoryT addr lim))
    (hoff : OffsetBound addr offset)
    (hp : packSize pt<Int.ofNat (2^4))
    (ha : align≤packLog pt) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨vectype,Call.Vlaneop_ok c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=pt } : vlaneop_)⟩)
      n (.success (.of ty)) n := by
  have hlog : packLog pt<4096 := by cases pt <;> decide
  have halign := (alignment align (packLog pt) hlog).2 ha
  rw [←pack_pow] at halign
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Vlaneop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=pt } : vlaneop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vlaneop_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
    apply SpecTecExecution.Eval.bind_success (pack_ok (2^4) pt n hp)
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hoff)
    exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Vlaneop_ok_clauses c ({ TYPE:=ty,ALIGN:=align,OFFSET:=offset,PACK:=pt } : vlaneop_))) n _ n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vlaneop_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
      apply SpecTecExecution.Eval.bind_success (pack_ok (2^4) pt n hp)
      apply SpecTecExecution.Eval.bind_success (pack_size pt n)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
      rw [hx]
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vlaneop_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyMemoryCalls.vec_size ty n)
    apply SpecTecExecution.Eval.bind_success (pack_ok (2^4) pt n hp)
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true halign)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    exact SpecTecExecution.Eval.pure _

#print axioms vlaneop_ok_pack
end properties.wasm_module_ok.ConstructiveBodyMemoryOperands
