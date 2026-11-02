import Spec4Pbt.CorrectGen
import properties.wasm_module_ok.Validity

set_option autoImplicit false

namespace properties.wasm_module_ok.Staged

/-- A stage emits only values satisfying its local condition and the entry
condition required by its successor. Its support is exact on valid inputs. -/
structure Stage (S T : Type) where
  entry : S → Prop
  nextEntry : T → Prop
  valid : S → T → Prop
  generate : S → Gen T
  always : ∀ s, entry s → ∃ t, valid s t ∧ nextEntry t
  sound : ∀ s t, entry s → Gen.support (generate s) t →
    valid s t ∧ nextEntry t
  complete : ∀ s t, entry s → valid s t → nextEntry t →
    Gen.support (generate s) t

def chain {S T U : Type} (a : Stage S T) (b : Stage T U)
    (s : S) : Gen U :=
  a.generate s >>= b.generate

theorem chain_support_iff {S T U : Type}
    (a : Stage S T) (b : Stage T U)
    (compatible : ∀ t, a.nextEntry t ↔ b.entry t)
    (s : S) (u : U) (hs : a.entry s) :
    Gen.support (chain a b s) u ↔
      ∃ t, a.valid s t ∧ a.nextEntry t ∧
        b.valid t u ∧ b.nextEntry u := by
  simp only [chain, Gen.Support.support_bind]
  constructor
  · rintro ⟨t, ht, hu⟩
    obtain ⟨hvalid, hnext⟩ := a.sound s t hs ht
    obtain ⟨huvalid, hunext⟩ := b.sound t u ((compatible t).mp hnext) hu
    exact ⟨t, hvalid, hnext, huvalid, hunext⟩
  · rintro ⟨t, htvalid, hnext, huvalid, hunext⟩
    have hbentry : b.entry t := (compatible t).mp hnext
    exact ⟨t, a.complete s t hs htvalid ((compatible t).mpr hbentry),
      b.complete t u hbentry huvalid hunext⟩

theorem chain_nonempty {S T U : Type}
    (a : Stage S T) (b : Stage T U)
    (compatible : ∀ t, a.nextEntry t ↔ b.entry t)
    (s : S) (hs : a.entry s) :
    ∃ u, Gen.support (chain a b s) u := by
  obtain ⟨t, htvalid, hnext⟩ := a.always s hs
  have hbentry : b.entry t := (compatible t).mp hnext
  obtain ⟨u, huvalid, hunext⟩ := b.always t hbentry
  refine ⟨u, ?_⟩
  apply (chain_support_iff a b compatible s u hs).2
  exact ⟨t, htvalid, hnext, huvalid, hunext⟩

def compose {S T U : Type}
    (a : Stage S T) (b : Stage T U)
    (compatible : ∀ t, a.nextEntry t ↔ b.entry t) : Stage S U where
  entry := a.entry
  nextEntry := b.nextEntry
  valid := fun s u =>
    ∃ t, a.valid s t ∧ a.nextEntry t ∧ b.valid t u
  generate := chain a b
  always := by
    intro s hs
    obtain ⟨t, htvalid, hnext⟩ := a.always s hs
    obtain ⟨u, huvalid, hunext⟩ :=
      b.always t ((compatible t).mp hnext)
    exact ⟨u, ⟨t, htvalid, hnext, huvalid⟩, hunext⟩
  sound := by
    intro s u hs hsupport
    obtain ⟨t, htvalid, hnext, huvalid, hunext⟩ :=
      (chain_support_iff a b compatible s u hs).1 hsupport
    exact ⟨⟨t, htvalid, hnext, huvalid⟩, hunext⟩
  complete := by
    intro s u hs hvalid hunext
    obtain ⟨t, htvalid, hnext, huvalid⟩ := hvalid
    exact (chain_support_iff a b compatible s u hs).2
      ⟨t, htvalid, hnext, huvalid, hunext⟩

/-- A derived value is passed forward without sampling a second copy. -/
def computeStage {S T : Type} (f : S → T) : Stage S T where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun s t => t = f s
  generate := fun s => pure (f s)
  always := by
    intro s _
    exact ⟨f s, rfl, trivial⟩
  sound := by
    intro s t _ h
    exact ⟨h, trivial⟩
  complete := by
    intro s t _ hv _
    exact hv

/-- Module assembly is exact once each translated stage call supplies its
piece of the generated validation trace. This theorem is independent of any
concrete generator implementation. -/
theorem module_ok_iff_stage_trace (m : SpecTec.module) :
    SpecTec.Module_ok m ↔
      Nonempty (properties.wasm_module_ok.Validity.ModuleOkTrace m) := by
  constructor
  · exact properties.wasm_module_ok.Validity.module_ok_full_trace m
  · exact properties.wasm_module_ok.Validity.module_ok_of_full_trace m

end properties.wasm_module_ok.Staged
