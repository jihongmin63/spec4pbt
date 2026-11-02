import properties.wasm_module_ok.ConstructiveConstTableCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstGeneration
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage

def erasedEntry (c : context) (e : Entry c) : Audited (Witness c) :=
  e.values.map fun x => ⟨x.val,x.property.1⟩

def chooseEntries (c : context) (head : Entry c) (tail : List (Entry c)) : Audited (Witness c) :=
  Audited.merge (erasedEntry c head) (tail.map (erasedEntry c))

def atRound (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (n : Nat) : Audited (Witness c) :=
  match he : rounds c hr hp hn n with
  | [] => False.elim (rounds_nonempty c hr hp hn n he)
  | a::as => chooseEntries c a as

def trees (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :
    Gen (Witness c) := Gen.arbNat >>= fun n => (atRound c hr hp hn n).generator

theorem trees_audit (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :
    Structural (trees c hr hp hn) := ⟨arbNat_audit,fun n => (atRound c hr hp hn n).audit⟩

theorem chooseEntries_support (c : context) (head : Entry c) (tail : List (Entry c)) (out : Witness c) :
    Gen.support (chooseEntries c head tail).generator out ↔ Covers (head::tail) out.val := by
  rw [chooseEntries,merge_support]
  simp only [List.mem_cons,List.mem_map]
  constructor
  · rintro ⟨g,hg,hs⟩
    rcases hg with rfl|⟨e,he,rfl⟩
    · obtain ⟨v,hv,he⟩ := hs
      exact ⟨head,by simp,v,hv,(congrArg Subtype.val he).symm⟩
    · obtain ⟨v,hv,hvalue⟩ := hs
      exact ⟨e,by simp [he],v,hv,(congrArg Subtype.val hvalue).symm⟩
  · rintro ⟨e,he,v,hv,hvalue⟩
    refine ⟨erasedEntry c e,?_,v,hv,Subtype.ext hvalue.symm⟩
    rcases List.mem_cons.mp he with rfl|he
    · exact Or.inl rfl
    · exact Or.inr ⟨e,he,rfl⟩

theorem atRound_support (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (n : Nat) (out : Witness c) :
    Gen.support (atRound c hr hp hn n).generator out ↔ Covers (rounds c hr hp hn n) out.val := by
  unfold atRound
  split
  · contradiction
  · rename_i a as he
    simpa only [he] using chooseEntries_support c a as out

theorem trees_support (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (out : Witness c) :
    Gen.support (trees c hr hp hn) out ↔ ∃n,Covers (rounds c hr hp hn n) out.val := by
  simp [trees,atRound_support]

theorem rounds_monotone (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (n k : Nat) : rounds c hr hp hn n⊆rounds c hr hp hn (n+k) := by
  induction k with
  | zero => exact List.Subset.refl _
  | succ k ih =>
    intro e he
    exact List.mem_append_left _ (ih he)

theorem atRound_monotone (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (n k : Nat) (out : Witness c)
    (h : Gen.support (atRound c hr hp hn n).generator out) :
    Gen.support (atRound c hr hp hn (n+k)).generator out := by
  rw [atRound_support] at h ⊢
  exact covers_mono (rounds_monotone c hr hp hn n k) h

#print axioms trees_audit
#print axioms trees_support
end properties.wasm_module_ok.ConstructiveConstGeneration
