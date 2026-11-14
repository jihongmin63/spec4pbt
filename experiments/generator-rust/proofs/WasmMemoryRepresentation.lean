import WasmMemorySpecification
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open Aeneas.Std generator_rust.wasm.ast SpecTecExecution

/-- Extract only the original bounds; no execution determinism assumption is needed. -/
theorem limits_bounds_of_execution (context : SpecTec.context) (bound : Nat)
    (limits : SpecTec.limits) (start finish : Nat)
    (run : Eval SpecTec.Body (.call ⟨Unit, SpecTec.Call.Limits_ok context bound limits⟩)
      start (.success (.of ())) finish) :
    limits.MIN ≤ bound ∧
      ∀ maximum ∈ limits.MAX, limits.MIN ≤ maximum ∧ maximum ≤ bound := by
  cases run with
  | call body =>
      change Eval SpecTec.Body
        (.orElse (SpecTec.«Limits_ok:clause:0» context bound limits)
          (fun _ => tryClauses [SpecTec.«Limits_ok:clause:1» context bound limits]))
        start (.success (.of ())) finish at body
      cases body with
      | orElse_success first =>
          unfold SpecTec.«Limits_ok:clause:0» at first
          cases first with
          | bind_success absent tail =>
              cases absent with
              | guard_true absent =>
                  cases tail with
                  | bind_success minimum _ =>
                      cases minimum with
                      | guard_true minimum =>
                          have noMaximum : limits.MAX = none := by
                            cases value : limits.MAX <;> simp [value] at absent ⊢
                          exact ⟨minimum, by simp [noMaximum]⟩
      | orElse_unmatch _ tail =>
          change Eval SpecTec.Body
            (.orElse (SpecTec.«Limits_ok:clause:1» context bound limits) (fun _ => .unmatch))
            _ (.success (.of ())) finish at tail
          cases tail with
          | orElse_success second =>
              unfold SpecTec.«Limits_ok:clause:1» at second
              cases second with
              | bind_success present tail =>
                  cases present with
                  | guard_true present =>
                      cases value : limits.MAX with
                      | none => simp [value] at present
                      | some maximum =>
                          rw [value] at tail
                          cases tail with
                          | bind_success bounded _ =>
                              cases bounded with
                              | guard_true bounded =>
                                  exact ⟨bounded.1.1, by
                                    simpa [value] using And.intro bounded.2 bounded.1.2⟩
          | orElse_unmatch _ impossible => cases impossible

def addressLiteral : SpecTec.addrtype → AddressType
  | .I32AT => .I32
  | .I64AT => .I64

/-- Original memory validation supplies exactly the page limits used by Rust. -/
theorem memtype_bounds_of_execution (context : SpecTec.context) (address : SpecTec.addrtype)
    (limits : SpecTec.limits) (start finish : Nat)
    (run : Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Memtype_ok context (.MemoryT address limits)⟩)
      start (.success (.of ())) finish) :
    limits.MIN ≤ memoryPageLimit (addressLiteral address) ∧
      ∀ maximum ∈ limits.MAX,
        limits.MIN ≤ maximum ∧ maximum ≤ memoryPageLimit (addressLiteral address) := by
  cases run with
  | call body =>
      change Eval SpecTec.Body
        (.orElse (SpecTec.«Memtype_ok:clause:0» context (.MemoryT address limits))
          (fun _ => tryClauses [SpecTec.«Memtype_ok:clause:1» context (.MemoryT address limits)]))
        start (.success (.of ())) finish at body
      cases body with
      | orElse_success first =>
          unfold SpecTec.«Memtype_ok:clause:0» at first
          cases first with
          | bind_success width tail =>
              cases width with
              | guard_true width =>
                  cases tail with
                  | bind_success checked _ =>
                      cases address with
                      | I32AT => exact limits_bounds_of_execution context 65536 limits _ _ checked
                      | I64AT => cases width
      | orElse_unmatch _ tail =>
          change Eval SpecTec.Body
            (.orElse (SpecTec.«Memtype_ok:clause:1» context (.MemoryT address limits))
              (fun _ => .unmatch)) _ (.success (.of ())) finish at tail
          cases tail with
          | orElse_success second =>
              unfold SpecTec.«Memtype_ok:clause:1» at second
              cases second with
              | bind_success width tail =>
                  cases width with
                  | guard_true width =>
                      cases tail with
                      | bind_success checked _ =>
                          cases address with
                          | I32AT => cases width
                          | I64AT => exact limits_bounds_of_execution context 281474976710656 limits _ _ checked
          | orElse_unmatch _ impossible => cases impossible

private theorem bounded_memory_representable (address : SpecTec.addrtype)
    (minimum : Nat) (maximum : Option Nat)
    (bounded : minimum ≤ memoryPageLimit (addressLiteral address) ∧
      ∀ value ∈ maximum, minimum ≤ value ∧ value ≤ memoryPageLimit (addressLiteral address)) :
    ∃ item : Memory, MemoryBounded item ∧
      (memory item).MTYPE = .MemoryT address ⟨minimum, maximum⟩ := by
  have limitFits : memoryPageLimit (addressLiteral address) < 18446744073709551616 := by
    cases address <;> decide
  have minimumFits : minimum < 18446744073709551616 := lt_of_le_of_lt bounded.1 limitFits
  let minimumWord : U64 := UScalar.ofNatCore minimum minimumFits
  cases maximum with
  | none =>
      refine ⟨⟨addressLiteral address, minimumWord, none⟩, ?_, ?_⟩
      · simpa [MemoryBounded, minimumWord] using bounded
      · cases address <;> simp [memory, addressLiteral, minimumWord]
  | some maximum =>
      have maximumBound := bounded.2 maximum rfl
      have maximumFits : maximum < 18446744073709551616 := lt_of_le_of_lt maximumBound.2 limitFits
      let maximumWord : U64 := UScalar.ofNatCore maximum maximumFits
      refine ⟨⟨addressLiteral address, minimumWord, some maximumWord⟩, ?_, ?_⟩
      · simpa [MemoryBounded, minimumWord, maximumWord] using bounded
      · cases address <;> simp [memory, addressLiteral, minimumWord, maximumWord]

/-- Every original valid memory type is represented exactly; word bounds follow from the specification. -/
theorem memtype_representable_iff (context : SpecTec.context) (type : SpecTec.memtype) :
    SpecTec.Memtype_ok context type ↔
      ∃ item : Memory, MemoryBounded item ∧ (memory item).MTYPE = type := by
  constructor
  · rintro ⟨finish, run⟩
    cases type with
    | MemoryT address limits =>
        exact bounded_memory_representable address limits.MIN limits.MAX
          (memtype_bounds_of_execution context address limits 0 finish run)
  · rintro ⟨item, bounded, rfl⟩
    exact memory_bounded_valid context item bounded

/-- Original memory lists have an exact recursive Rust representation, including order and duplicates. -/
theorem original_memories_representable (context : SpecTec.context) (items : List SpecTec.memory)
    (valid : ∀ item ∈ items, SpecTec.Memtype_ok context item.MTYPE) :
    ∃ represented : List Memory,
      (∀ item ∈ represented, MemoryBounded item) ∧ represented.map memory = items := by
  induction items with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons head tail ih =>
      obtain ⟨first, firstBound, firstType⟩ :=
        (memtype_representable_iff context head.MTYPE).mp (valid head (by simp))
      obtain ⟨rest, restBound, restEqual⟩ := ih (by
        intro item present
        exact valid item (by simp [present]))
      have firstEqual : memory first = head := by
        cases head with
        | mk type =>
            change (memory first).MTYPE = type at firstType
            rw [←firstType]
      refine ⟨first :: rest, ?_, ?_⟩
      · intro item present
        rcases List.mem_cons.mp present with rfl | present
        · exact firstBound
        · exact restBound item present
      · simp [firstEqual, restEqual]

/-- The original-domain representation is connected to the actual full Rust replay and original Module_ok. -/
theorem original_memories_generated_valid (context : SpecTec.context) (items : List SpecTec.memory)
    (valid : ∀ item ∈ items, SpecTec.Memtype_ok context item.MTYPE) :
    (∃ config, ReplaySupport config { emptyModule with MEMS := items }) ∧
      SpecTec.Module_ok { emptyModule with MEMS := items } := by
  obtain ⟨represented, bounded, exactItems⟩ := original_memories_representable context items valid
  rw [←exactItems]
  exact memory_list_generated_valid represented bounded

open Lean Elab Command in
run_cmd do
  for declaration in [``limits_bounds_of_execution, ``memtype_bounds_of_execution,
      ``memtype_representable_iff, ``original_memories_representable,
      ``original_memories_generated_valid] do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
