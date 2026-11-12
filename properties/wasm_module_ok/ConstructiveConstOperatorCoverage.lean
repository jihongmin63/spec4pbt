import properties.wasm_module_ok.ConstructiveConstFixedCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstOperatorCoverage
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstSeedCoverage properties.wasm_module_ok.ConstructiveConstExpansionCoverage

theorem i31_cover (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (args : Operands c [.NumT .I32T]) (hc : ∀t∈args.trees,Covers table t) :
    Covers (i31Entries c hr table) (.node .«REF.I31» (.RefT (.«% %» .NoNull .I31HT)) args.trees) := by
  unfold i31Entries
  exact fromOperands_cover c hr table _ _ _ _ _ args hc

theorem arithmetic_entries_cover (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (op : binop_) (hop : .BINOP op∈ConstArithmeticValidation.arithmeticOps)
    (args : Operands c [.NumT (ConstInstrDecision.arithmeticType op),.NumT (ConstInstrDecision.arithmeticType op)])
    (hc : ∀t∈args.trees,Covers table t) :
    Covers (arithmeticEntries c hr table op hop) (.node (.BINOP op) (.NumT (ConstInstrDecision.arithmeticType op)) args.trees) := by
  unfold arithmeticEntries
  exact fromOperands_cover c hr table _ _ _ _ _ args hc

theorem arithmetic_cover (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (op : binop_) (hop : .BINOP op∈ConstArithmeticValidation.arithmeticOps)
    (args : Operands c [.NumT (ConstInstrDecision.arithmeticType op),.NumT (ConstInstrDecision.arithmeticType op)])
    (hc : ∀t∈args.trees,Covers table t) :
    Covers (allArithmetic c hr table) (.node (.BINOP op) (.NumT (ConstInstrDecision.arithmeticType op)) args.trees) := by
  have hops : op=.I32 .IAdd ∨ op=.I32 .ISub ∨ op=.I32 .IMul ∨ op=.I64 .IAdd ∨ op=.I64 .ISub ∨ op=.I64 .IMul := by
    simpa [ConstArithmeticValidation.arithmeticOps] using hop
  rcases hops with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    apply covers_mono (b := allArithmetic c hr table) ?_ (arithmetic_entries_cover c hr table _ hop args hc)
    intro e he
    simp only [allArithmetic,List.mem_append]
    tauto

theorem extern_cover (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (op : externop_) (nu : null) (ht : heaptype) (tree : Typed c (.RefT (.«% %» nu ht)))
    (hm : ∀ n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c [.RefT (.«% %» nu ht)]
        [.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1)]⟩)
      n (.success (.of ())) n)
    (hc : Covers table tree.val) :
    Covers (externEntries c hr table op) (externConvert c op nu ht tree hm).val := by
  have hc' : Covers (ConstructiveConstTableMerge.coalesce table) tree.val :=
    (ConstructiveConstTableMerge.coalesce_emits table tree.val).2 hc
  obtain ⟨e,he,v,hv,hvalue⟩ := hc'
  have het : e.type=.RefT (.«% %» nu ht) := by rw [←v.property.2,hvalue,tree.property.2]
  have htgt : CandidateValMatch.InTableVal c (.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1)) := by
    intro h hh
    have hh' : h=(ExternopTypeDecision.typeExternopResult op).1 := by simpa [ReadyMatchReachability.sourceValHeaptypes] using hh
    subst h
    exact .base _ (by cases op <;> simp [ExternopTypeDecision.typeExternopResult,HeaptypeValidation.baseHeaptypes])
  have hb : CandidateValMatch.candidateValMatch c e.type (.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1))=true := by
    have hmt := (MatchResulttypeDecision.match_pairs_iff_resulttype c [e.type] [_] 0 hr
      (by intro t h; have hte : t=e.type := by simpa using h
          subst t; exact e.inTable)
      (by intro t h; have hte : t=.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1) := by simpa using h
          subst t; exact htgt)).2 (by simpa only [het] using hm 0)
    simpa [MatchResulttypeDecision.matchPairs] using hmt
  unfold externEntries
  apply covers_flatMap e he
  split
  · rename_i nu' ht' htype
    have hh : nu'=nu ∧ ht'=ht := by simpa only [htype,valtype.RefT.injEq,reftype.«% %».injEq] using het
    obtain ⟨rfl,rfl⟩ := hh
    simp only [dif_pos hb]
    refine ⟨_,List.mem_singleton_self _,externConvert c op nu' ht' tree hm,?_,rfl⟩
    refine ⟨v,hv,?_⟩
    apply Subtype.ext
    simp only [externConvert]
    congr 1
    exact congrArg (fun t => [t]) hvalue.symm
  all_goals simp_all [het]

theorem extern_bottom_cover (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (op : externop_) (tree : Typed c .BotT)
    (hm : ∀ n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c [.BotT]
        [.RefT (.«% %» .NoNull (ExternopTypeDecision.typeExternopResult op).1)]⟩)
      n (.success (.of ())) n)
    (hc : Covers table tree.val) :
    Covers (externEntries c hr table op) (externBottom c op tree hm).val := by
  have hc' : Covers (ConstructiveConstTableMerge.coalesce table) tree.val :=
    (ConstructiveConstTableMerge.coalesce_emits table tree.val).2 hc
  obtain ⟨e,he,v,hv,hvalue⟩ := hc'
  have het : e.type=.BotT := by rw [←v.property.2,hvalue,tree.property.2]
  unfold externEntries
  apply covers_flatMap e he
  split
  · rename_i nu ht htype
    simp [het] at htype
  · refine ⟨_,List.mem_singleton_self _,externBottom c op tree hm,?_,rfl⟩
    refine ⟨v,hv,?_⟩
    apply Subtype.ext
    simp only [externBottom]
    congr 1
    exact congrArg (fun t => [t]) hvalue.symm
  all_goals simp_all [het]

#print axioms arithmetic_cover
#print axioms extern_cover
end properties.wasm_module_ok.ConstructiveConstOperatorCoverage
