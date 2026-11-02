import properties.wasm_module_ok.ConstructiveBodyMemoryOperands
import properties.wasm_module_ok.ConstructiveBodyEvalReduction
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemorySuffix
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEvalReduction ConstructiveBodyMemoryOperands

def addrTest : addrtype → addrtype → Bool
  | .I32AT => SpecTec.«exec:match:addrtype:I32AT»
  | .I64AT => SpecTec.«exec:match:addrtype:I64AT»

theorem addrTest_eq (want addr : addrtype) : addrTest want addr=true ↔ addr=want := by
  cases want <;> cases addr <;> decide

def tail {α : Type} (c : context) (want : addrtype) (offset : Nat) (value : α) : Plan Request :=
  .bind (.guard (0<c.MEMS.length)) fun (_ : Unit) =>
    match (c.MEMS[0]? : Option memtype) with
    | some mt =>
      match mt with
      | memtype.MemoryT addr _ =>
        .bind (.guard (addrTest want addr=true)) fun (_ : Unit) =>
          match want with
          | .I32AT => .bind (.guard (offset<4294967296)) fun (_ : Unit) => .pure value
          | .I64AT => .pure value
    | none => .unmatch

theorem tail_original {α : Type} (c : context) (want : addrtype) (offset : Nat) (value got : α)
    (n finish : Nat) (h : Eval SpecTec.Body (tail c want offset value) n (.success (.of got)) finish) :
    ∃lim,c.MEMS[0]?=some (.MemoryT want lim) ∧ OffsetBound want offset ∧ got=value ∧ finish=n := by
  unfold tail at h
  obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
  cases hx : c.MEMS[0]? with
  | none => rw [hx] at h; cases h
  | some mt =>
    cases mt with | MemoryT addr lim =>
      rw [hx] at h
      obtain ⟨he,h⟩ := (bind_guard _ _ _ _ _).1 h
      have he := (addrTest_eq want addr).1 he
      subst want
      cases addr with
      | I32AT =>
        obtain ⟨hoff,h⟩ := (bind_guard _ _ _ _ _).1 h
        exact ⟨lim,rfl,hoff,(pure_success _ _ _ _).1 h⟩
      | I64AT => exact ⟨lim,rfl,trivial,(pure_success _ _ _ _).1 h⟩

theorem pack_original (size : Nat) (pt : packtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨Unit,Call.Pack_ok (Int.ofNat size) pt⟩) n (.success (.of ())) finish) :
    ConstructiveBodyScalarSizes.packSize pt<Int.ofNat size ∧ finish=n := by
  cases h with | call h =>
    obtain ⟨k,hs⟩ := (tryClauses_success_iff (SpecTec.Pack_ok_clauses (Int.ofNat size) pt) n (.of ()) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Pack_ok:clause:0» at h
      obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
      simp only [Int.toNat?] at h
      rw [bind_known _ _ _ _ _ _ (ConstructiveBodyScalarSizes.pack_size pt n)] at h
      obtain ⟨hp,h⟩ := (bind_guard _ _ _ _ _).1 h
      exact ⟨hp,((pure_success _ _ _ _).1 h).2⟩
    | next _ hn => cases hn

#print axioms pack_original
end properties.wasm_module_ok.ConstructiveBodyMemorySuffix
