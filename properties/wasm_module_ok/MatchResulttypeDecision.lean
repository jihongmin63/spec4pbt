import properties.wasm_module_ok.CandidateValMatch
import properties.wasm_module_ok.MatchResulttypeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchResulttypeDecision

/-- Exact executable pairwise value matching for two result-type lists. -/
def matchPairs (c : SpecTec.context) :
    List SpecTec.valtype → List SpecTec.valtype → Bool
  | [], [] => true
  | actual :: restActual, required :: restRequired =>
      CandidateValMatch.candidateValMatch c actual required &&
        matchPairs c restActual restRequired
  | _, _ => false

theorem match_pairs_iff_iter
    (c : SpecTec.context)
    (actual required : List SpecTec.valtype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ t ∈ actual, CandidateValMatch.InTableVal c t)
    (hrequired : ∀ t ∈ required, CandidateValMatch.InTableVal c t) :
    matchPairs c actual required = true ↔
      required.length = actual.length ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Unit,
            SpecTec.Call.«Match_resulttype:rule:iter:0»
              c actual required⟩)
          n (.success (.of ())) n := by
  induction actual generalizing required n with
  | nil =>
    cases required with
    | nil =>
      constructor
      · intro _
        exact ⟨rfl, MatchResulttypeValidation.match_iter_nil_total c n⟩
      · intro _
        rfl
    | cons b bs =>
      constructor
      · intro h
        simp [matchPairs] at h
      · intro h
        have hlen := h.1
        simp at hlen
  | cons a as ih =>
    cases required with
    | nil =>
      constructor
      · intro h
        simp [matchPairs] at h
      · intro h
        have hlen := h.1
        simp at hlen
    | cons b bs =>
      have ha : CandidateValMatch.InTableVal c a :=
        hactual a (by simp)
      have hb : CandidateValMatch.InTableVal c b :=
        hrequired b (by simp)
      have has : ∀ t ∈ as, CandidateValMatch.InTableVal c t := by
        intro t ht
        exact hactual t (List.mem_cons_of_mem a ht)
      have hbs : ∀ t ∈ bs, CandidateValMatch.InTableVal c t := by
        intro t ht
        exact hrequired t (List.mem_cons_of_mem b ht)
      constructor
      · intro h
        have hparts :
            CandidateValMatch.candidateValMatch c a b = true ∧
              matchPairs c as bs = true := by
          simpa [matchPairs] using h
        have hhead :=
          (CandidateValMatch.candidate_val_match_iff
            c a b true n n hready ha hb).2 ⟨hparts.1.symm, rfl⟩
        obtain ⟨hlength, htail⟩ :=
          (ih bs n has hbs).1 hparts.2
        exact ⟨by simpa using congrArg Nat.succ hlength,
          (MatchResulttypeValidation.match_iter_cons_success_iff
            c a b as bs n n).2 ⟨n, hhead, htail⟩⟩
      · intro h
        obtain ⟨hlength, hiter⟩ := h
        obtain ⟨middle, hhead, htail⟩ :=
          (MatchResulttypeValidation.match_iter_cons_success_iff
            c a b as bs n n).1 hiter
        obtain ⟨hmatch, hmiddle⟩ :=
          (CandidateValMatch.candidate_val_match_iff
            c a b true n middle hready ha hb).1 hhead
        subst middle
        have hrest := (ih bs n has hbs).2 ⟨by simpa using hlength, htail⟩
        simp [matchPairs, hmatch, hrest]

theorem match_pairs_iff_resulttype
    (c : SpecTec.context)
    (actual required : List SpecTec.valtype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ t ∈ actual, CandidateValMatch.InTableVal c t)
    (hrequired : ∀ t ∈ required, CandidateValMatch.InTableVal c t) :
    matchPairs c actual required = true ↔
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.Match_resulttype c actual required⟩)
        n (.success (.of ())) n := by
  exact (match_pairs_iff_iter c actual required n hready
    hactual hrequired).trans
    (MatchResulttypeValidation.match_resulttype_success_iff
      c actual required n n).symm

theorem match_iter_success_counter
    (c : SpecTec.context)
    (actual required : List SpecTec.valtype)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ t ∈ actual, CandidateValMatch.InTableVal c t)
    (hrequired : ∀ t ∈ required, CandidateValMatch.InTableVal c t)
    (hlength : required.length = actual.length)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Match_resulttype:rule:iter:0»
          c actual required⟩)
      start (.success (.of ())) finish) :
    finish = start := by
  induction actual generalizing required start finish with
  | nil =>
    cases required with
    | nil =>
      exact (properties.wasm_module_ok.Execution.eval_deterministic hcall
        (MatchResulttypeValidation.match_iter_nil_total c start)).2
    | cons b bs => simp at hlength
  | cons a as ih =>
    cases required with
    | nil => simp at hlength
    | cons b bs =>
      obtain ⟨middle, hhead, htail⟩ :=
        (MatchResulttypeValidation.match_iter_cons_success_iff
          c a b as bs start finish).1 hcall
      have ha : CandidateValMatch.InTableVal c a :=
        hactual a (by simp)
      have hb : CandidateValMatch.InTableVal c b :=
        hrequired b (by simp)
      have has : ∀ t ∈ as, CandidateValMatch.InTableVal c t := by
        intro t ht
        exact hactual t (List.mem_cons_of_mem a ht)
      have hbs : ∀ t ∈ bs, CandidateValMatch.InTableVal c t := by
        intro t ht
        exact hrequired t (List.mem_cons_of_mem b ht)
      have hmiddle :=
        ((CandidateValMatch.candidate_val_match_iff
          c a b true start middle hready ha hb).1 hhead).2
      have hfinish := ih bs middle finish has hbs
        (by simpa using hlength) htail
      rw [hfinish, hmiddle]

theorem match_resulttype_success_counter
    (c : SpecTec.context)
    (actual required : List SpecTec.valtype)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ t ∈ actual, CandidateValMatch.InTableVal c t)
    (hrequired : ∀ t ∈ required, CandidateValMatch.InTableVal c t)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Match_resulttype c actual required⟩)
      start (.success (.of ())) finish) :
    finish = start := by
  obtain ⟨hlength, hiter⟩ :=
    (MatchResulttypeValidation.match_resulttype_success_iff
      c actual required start finish).1 hcall
  exact match_iter_success_counter c actual required start finish
    hready hactual hrequired hlength hiter

theorem match_pairs_of_resulttype_success
    (c : SpecTec.context)
    (actual required : List SpecTec.valtype)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ t ∈ actual, CandidateValMatch.InTableVal c t)
    (hrequired : ∀ t ∈ required, CandidateValMatch.InTableVal c t)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Match_resulttype c actual required⟩)
      start (.success (.of ())) finish) :
    matchPairs c actual required = true := by
  have hfinish := match_resulttype_success_counter
    c actual required start finish hready hactual hrequired hcall
  subst finish
  exact (match_pairs_iff_resulttype c actual required start
    hready hactual hrequired).2 hcall

end properties.wasm_module_ok.MatchResulttypeDecision
