import properties.wasm_module_ok.ConstructiveConstOriginalAggregates
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstOriginalOperators
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstSeedCoverage properties.wasm_module_ok.ConstructiveConstOperatorCoverage
open properties.wasm_module_ok.ConstructiveConstOriginalLeaves

theorem i31_node (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (u : valtype) (children : List Tree) (need : List valtype)
    (hi : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c (.NoEllipses,outputs children) .«REF.I31»⟩)
      0 (.success (.of (effect need u))) 0)
    (hm : ∀n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n)
    (hk : ∀t∈children,Good c t) (hc : ∀t∈children,Covers table t) :
    Covers (i31Entries c hr table) (.node .«REF.I31» u children) := by
  have he : effect [.NumT .I32T] (.RefT (.«% %» .NoNull .I31HT))=effect need u :=
    Option.some.inj ((ConstInstrDecision.i31_result_iff c _ _ 0 0).2 hi).1
  obtain ⟨hneed,hout⟩ := effect_inj _ _ _ _ he
  subst need; subst u
  exact i31_cover c hr table ⟨children,hk,hm⟩ hc

theorem arithmetic_node (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (op : binop_) (hop : .BINOP op∈ConstArithmeticValidation.arithmeticOps)
    (u : valtype) (children : List Tree) (need : List valtype)
    (hi : ConstInstrDecision.arithmeticResult op=some (effect need u))
    (hm : ∀n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n)
    (hk : ∀t∈children,Good c t) (hc : ∀t∈children,Covers table t) :
    Covers (allArithmetic c hr table) (.node (.BINOP op) u children) := by
  have he : effect [.NumT (ConstInstrDecision.arithmeticType op),.NumT (ConstInstrDecision.arithmeticType op)]
      (.NumT (ConstInstrDecision.arithmeticType op))=effect need u := by
    simpa [ConstInstrDecision.arithmeticResult,hop,effect] using hi
  obtain ⟨hneed,hout⟩ := effect_inj _ _ _ _ he
  subst need; subst u
  exact arithmetic_cover c hr table op hop ⟨children,hk,hm⟩ hc

theorem extern_node (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (op : externop_) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : ConstInstrDecision.externConvertResult op (.NoEllipses,outputs children)=some (effect need u))
    (hm : ∀n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n)
    (hk : ∀t∈children,Good c t) (hc : ∀t∈children,Covers table t) :
    Covers (externEntries c hr table op) (.node (.«EXTERN.CONVERT» op) u children) := by
  cases hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 (.NoEllipses,outputs children)) with
  | none => simp [ConstInstrDecision.externConvertResult,hp] at hi
  | some rt =>
    cases rt with
    | «% %» nu ht =>
      have he : effect [.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1)]
          (.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).2))=effect need u := by
        simpa [ConstInstrDecision.externConvertResult,hp,effect] using hi
      obtain ⟨hneed,hout⟩ := effect_inj _ _ _ _ he
      subst need; subst u
      have hlen := (MatchResulttypeValidation.match_resulttype_success_iff c _ _ 0 0).1 (hm 0) |>.1
      have hlen' : children.length=1 := by simpa [outputs] using hlen.symm
      obtain ⟨tree,hch⟩ : ∃tree,children=[tree] := by
        cases children with
        | nil => simp at hlen'
        | cons t ts =>
          have he : ts=[] := List.eq_nil_of_length_eq_zero (by simpa using hlen')
          exact ⟨t,by rw [he]⟩
      subst children
      simp only [outputs,List.map_singleton,PeekDecision.peekResult,List.reverse_singleton,
        List.getElem?_cons_zero,Option.getD_some] at hp
      cases htval : tree.output with
      | NumT _ => simp [htval,PeekRefDecision.peekRefResult] at hp
      | VecT _ => simp [htval,PeekRefDecision.peekRefResult] at hp
      | RefT rt =>
        cases rt with
        | «% %» nu' ht' =>
          have hrt : nu'=nu ∧ ht'=ht := by simpa [htval,PeekRefDecision.peekRefResult] using hp
          obtain ⟨rfl,rfl⟩ := hrt
          exact extern_cover c hr table op nu' ht' ⟨tree,hk tree (by simp),htval⟩
            (fun n => by simpa [outputs,htval] using hm n) (hc tree (by simp))
      | BotT =>
        have hrt : .NoNull=nu ∧ heaptype.BotHT=ht := by simpa [htval,PeekRefDecision.peekRefResult] using hp
        obtain ⟨rfl,rfl⟩ := hrt
        exact extern_bottom_cover c hr table op ⟨tree,hk tree (by simp),htval⟩
          (fun n => by simpa [outputs,htval] using hm n) (hc tree (by simp))

#print axioms extern_node
end properties.wasm_module_ok.ConstructiveConstOriginalOperators
