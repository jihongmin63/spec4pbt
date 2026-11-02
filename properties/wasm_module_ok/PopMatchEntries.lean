import properties.wasm_module_ok.PopMatchExtraction
import Mathlib.Data.List.Forall2
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

namespace properties.wasm_module_ok.PopMatchEntries

/-- The translated value-type match may accept more than equality. -/
def ValueMatches (c : SpecTec.context)
    (actual required : SpecTec.valtype) : Prop :=
  ∃ start finish : Nat,
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_valtype»
        c.TYPES actual required⟩)
      start (.success (.of true)) finish

theorem match_resulttype_entries
    (c : SpecTec.context)
    (actual required : List SpecTec.valtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype c actual required⟩)
      start (.success (.of ())) finish) :
    List.Forall₂ (ValueMatches c) actual required := by
  have ⟨hlen, hiter⟩ :=
    (MatchResulttypeValidation.match_resulttype_success_iff
      c actual required start finish).1 h
  clear h
  induction actual generalizing required start finish with
  | nil =>
    cases required with
    | nil => exact List.Forall₂.nil
    | cons _ _ => simp at hlen
  | cons a rest ih =>
    cases required with
    | nil => simp at hlen
    | cons b restNeed =>
      obtain ⟨middle, hhead, hrest⟩ :=
        (MatchResulttypeValidation.match_iter_cons_success_iff
          c a b rest restNeed start finish).1 hiter
      apply List.Forall₂.cons
      · exact ⟨start, middle, hhead⟩
      · have htailLength : restNeed.length = rest.length := by
          simpa using hlen
        exact ih restNeed middle finish htailLength hrest

theorem entries_source
    (c : SpecTec.context)
    (actual required : List SpecTec.valtype)
    (h : List.Forall₂ (ValueMatches c) actual required) :
    ∀ target ∈ required, ∃ source ∈ actual, ValueMatches c source target := by
  induction h with
  | nil =>
    intro target htarget
    cases htarget
  | @cons source target restActual restRequired hhead htail ih =>
    intro t ht
    rcases List.mem_cons.mp ht with heq | hmem
    · subst target
      exact ⟨source, List.mem_cons_self, hhead⟩
    · obtain ⟨u, hu, hrel⟩ := ih t hmem
      exact ⟨u, List.mem_cons_of_mem _ hu, hrel⟩

def MatchSaturated (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (required : SpecTec.valtype) : Prop :=
  ∃ actual ∈ s, ValueMatches c actual required

theorem pop_required_match_saturated
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (start finish : Nat)
    (s : Finset SpecTec.valtype)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) finish)
    (havailable : ∀ actual ∈ available, actual ∈ s) :
    ∀ required ∈ need, MatchSaturated c s required := by
  obtain ⟨_, middle, hmatch⟩ :=
    PopMatchExtraction.pop_noellipses_success_has_match
      c need available result start finish h
  have hentries := match_resulttype_entries c
    (available.drop (available.length - need.length)) need
    middle finish hmatch
  intro required hrequired
  obtain ⟨actual, hmem, hrel⟩ :=
    entries_source c _ _ hentries required hrequired
  exact ⟨actual, havailable actual (List.mem_of_mem_drop hmem), hrel⟩

end properties.wasm_module_ok.PopMatchEntries
