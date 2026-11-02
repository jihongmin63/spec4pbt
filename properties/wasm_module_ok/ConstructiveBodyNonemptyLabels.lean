import properties.wasm_module_ok.ConstructiveBodyReferenceProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyNonemptyLabels
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment

structure Label (c : context) where
  entry : ConstructiveBodyLookup.Entry c.LABELS
  nonempty : 0<entry.value.length

def Label.width {c : context} (label : Label c) : Nat := label.entry.value.length-1

theorem Label.bound {c : context} (label : Label c) : label.width<label.entry.value.length := by
  have h := label.nonempty
  unfold Label.width
  omega

def Label.front {c : context} (label : Label c) : List valtype := label.entry.value.take label.width
def Label.last {c : context} (label : Label c) : valtype := label.entry.value[label.width]'label.bound

theorem Label.converted {c : context} (label : Label c) :
    Int.ofNat label.entry.value.length-Int.ofNat 1=Int.ofNat label.width := by
  have h := label.nonempty
  exact (Int.ofNat_sub (show 1≤label.entry.value.length from by omega)).symm

theorem Label.lookupLast {c : context} (label : Label c) :
    label.entry.value[label.width]?=some label.last := List.getElem?_eq_getElem label.bound

theorem Label.frontBacked {c : context} (label : Label c) (env : Env c) :
    ∀t∈label.front,CandidateValMatch.InTableVal c t := by
  intro t ht
  exact env.labels label.entry.value label.entry.mem t (List.mem_of_mem_take ht)

theorem Label.lastBacked {c : context} (label : Label c) (env : Env c) :
    CandidateValMatch.InTableVal c label.last :=
  env.labels label.entry.value label.entry.mem label.last (List.mem_iff_getElem?.mpr ⟨label.width,label.lookupLast⟩)

def all (c : context) : List (Label c) :=
  (ConstructiveBodyLookup.entries c.LABELS).flatMap fun e =>
    match he : e.value with
    | [] => []
    | t::ts => [⟨e,by simp [he]⟩]

theorem complete (c : context) (label : Label c) : label∈all c := by
  apply List.mem_flatMap.mpr
  refine ⟨label.entry,ConstructiveBodyLookup.complete _ label.entry,?_⟩
  split
  next he => have h := label.nonempty; simp [he] at h
  next t ts he => exact List.mem_singleton_self _

#print axioms complete
#print axioms Label.converted
end properties.wasm_module_ok.ConstructiveBodyNonemptyLabels
