import properties.wasm_module_ok.ConstructiveConstTableExpand
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTableCoverage
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand

def Covers {c : context} (table : List (Entry c)) (tree : Tree) : Prop :=
  ∃ e∈table,∃ t,Gen.support e.values.generator t ∧ t.val=tree

theorem covers_mono {c : context} {a b : List (Entry c)} {tree : Tree}
    (hsub : a⊆b) (h : Covers a tree) : Covers b tree := by
  obtain ⟨e,he,t,ht,hv⟩ := h
  exact ⟨e,hsub he,t,ht,hv⟩

theorem covers_good {c : context} {table : List (Entry c)} {tree : Tree}
    (h : Covers table tree) : Good c tree := by
  obtain ⟨e,he,t,ht,rfl⟩ := h
  exact t.property.1

theorem covers_inTable {c : context} {table : List (Entry c)} {tree : Tree}
    (h : Covers table tree) : CandidateValMatch.InTableVal c tree.output := by
  obtain ⟨e,he,t,ht,rfl⟩ := h
  simpa only [t.property.2] using e.inTable

theorem matched_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (e : Entry c) (hm : CandidateValMatch.candidateValMatch c e.type target=true)
    (v : Typed c e.type) (hv : Gen.support e.values.generator v)
    (out : Matched c target) (he : out.val=v.val) :
    Gen.support (matched c hr target ht e hm).generator out := by
  exact ⟨v,hv,Subtype.ext he⟩

theorem eligible_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (table : List (Entry c)) (out : Matched c target)
    (hc : Covers table out.val) :
    ∃ g∈eligible c hr target ht table,Gen.support g.generator out := by
  obtain ⟨e,he,v,hv,hvalue⟩ := hc
  have hm : CandidateValMatch.candidateValMatch c e.type target=true := by
    have hh := (MatchResulttypeDecision.match_pairs_iff_resulttype c [out.val.output] [target] 0 hr
      (by intro t h; have hte : t=out.val.output := by simpa using h
          subst t; simpa only [←hvalue,v.property.2] using e.inTable)
      (by intro t h; have hte : t=target := by simpa using h
          subst t; exact ht)).2 (out.property.2 0)
    simpa [MatchResulttypeDecision.matchPairs,←hvalue,v.property.2] using hh
  have hmem : matched c hr target ht e hm∈eligible c hr target ht table := by
    induction table with
    | nil => cases he
    | cons a as ih =>
      rcases List.mem_cons.mp he with rfl|he
      · simp [eligible,hm]
      · unfold eligible
        split
        · exact List.mem_cons_of_mem _ (ih he)
        · exact ih he
  exact ⟨_,hmem,matched_cover c hr target ht e hm v hv out hvalue.symm⟩

theorem operand_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (table : List (Entry c)) (out : Matched c target)
    (hc : Covers table out.val) :
    ∃ g,operand c hr target ht table=some g ∧ Gen.support g.generator out := by
  obtain ⟨g,hg,hs⟩ := eligible_cover c hr target ht table out hc
  cases he : eligible c hr target ht table with
  | nil => simp [he] at hg
  | cons a as =>
    refine ⟨a.merge as,by simp [operand,he],(merge_support a as out).2 ?_⟩
    exact ⟨g,by simpa only [he] using hg,hs⟩

theorem operands_ext {c : context} {need : List valtype} {a b : Operands c need}
    (h : a.trees=b.trees) : a=b := by
  cases a; cases b; cases h; rfl

theorem operands_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (table : List (Entry c)) (need : List valtype)
    (ht : ∀t∈need,CandidateValMatch.InTableVal c t) (out : Operands c need)
    (hc : ∀t∈out.trees,Covers table t) :
    ∃ g,operands c hr table need ht=some g ∧ Gen.support g.generator out := by
  have hm := (MatchResulttypeDecision.match_pairs_iff_resulttype c (outputs out.trees) need 0 hr
    (by intro t ht; obtain ⟨tree,hm,rfl⟩ := List.mem_map.mp ht
        exact covers_inTable (hc tree hm)) ht).2 (out.matching 0)
  induction need with
  | nil =>
    cases trees : out.trees with
    | nil =>
      refine ⟨Audited.pure (emptyOperands c),rfl,?_⟩
      change out=emptyOperands c
      exact operands_ext trees
    | cons a as => simp [outputs,trees,MatchResulttypeDecision.matchPairs] at hm
  | cons u us ih =>
    cases trees : out.trees with
    | nil => simp [outputs,trees,MatchResulttypeDecision.matchPairs] at hm
    | cons a as =>
      have hm' : CandidateValMatch.candidateValMatch c a.output u=true ∧
          MatchResulttypeDecision.matchPairs c (outputs as) us=true := by
        simpa [outputs,trees,MatchResulttypeDecision.matchPairs] using hm
      have hta : CandidateValMatch.InTableVal c a.output := covers_inTable (hc a (by simp [trees]))
      have htu := ht u (by simp)
      let head : Matched c u := ⟨a,out.good a (by simp [trees]),by
        intro n
        exact (MatchResulttypeDecision.match_pairs_iff_resulttype c [a.output] [u] n hr
          (by intro t h; have he : t=a.output := by simpa using h
              subst t; exact hta)
          (by intro t h; have he : t=u := by simpa using h
              subst t; exact htu)).1 (by simp [MatchResulttypeDecision.matchPairs,hm'.1])⟩
      let rest : Operands c us := ⟨as,(fun t ht => out.good t (by simp [trees,ht])),by
        intro n
        exact (MatchResulttypeDecision.match_pairs_iff_resulttype c (outputs as) us n hr
          (by intro t h; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
              exact covers_inTable (hc v (by simp [trees,hv])))
          (fun t h => ht t (by simp [h]))).1 hm'.2⟩
      obtain ⟨gh,hgh,hsh⟩ := operand_cover c hr u htu table head (hc a (by simp [trees]))
      obtain ⟨gt,hgt,hst⟩ := ih (fun t h => ht t (by simp [h])) rest
        (fun t h => hc t (by simp [rest,trees] at h ⊢; exact Or.inr h)) hm'.2
      refine ⟨gh.bind (fun a => gt.map (operandsCons c u us a)),?_,?_⟩
      · simp only [operands,hgh,hgt]
      · refine ⟨head,hsh,rest,hst,?_⟩
        exact operands_ext trees

#print axioms operands_cover
end properties.wasm_module_ok.ConstructiveConstTableCoverage
