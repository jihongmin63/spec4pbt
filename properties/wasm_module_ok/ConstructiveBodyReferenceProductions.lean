import properties.wasm_module_ok.ConstructiveBodyReferenceCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyIndexedProductions

theorem retype (c : context) (nu other : SpecTec.null) (heap : heaptype)
    (h : CandidateValMatch.InTableVal c (.RefT (.«% %» nu heap))) :
    CandidateValMatch.InTableVal c (.RefT (.«% %» other heap)) := h

theorem peek_backed (c : context) (stack : inferresulttype) (hs : StackBacked c stack)
    (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) :
    CandidateValMatch.InTableVal c (.RefT (.«% %» nu heap)) := by
  have hb := ConstructiveBodySimpleAtoms.peek_backed c stack hs 0
  cases he : PeekDecision.peekResult 0 stack with
  | NumT nt => simp [PeekRefDecision.peekRefResult,he] at hp
  | VecT vt => simp [PeekRefDecision.peekRefResult,he] at hp
  | RefT rt =>
    have hr : rt=.«% %» nu heap := by simpa [PeekRefDecision.peekRefResult,he] using hp
    simpa [he,hr] using hb
  | BotT =>
    have hr : nu=.NoNull ∧ heap=.BotHT := by simpa [PeekRefDecision.peekRefResult,he] using hp.symm
    rcases hr with ⟨rfl,rfl⟩
    exact ConstructiveBodyReferenceMatcher.base_backed c .NoNull .BotHT (by simp [HeaptypeValidation.baseHeaptypes])

def nullRef (c : context) (stack : inferresulttype) (env : Env c) (heap : heaptype)
    (hh : heap∈FiniteValidTypes.heapCandidates c) : Production c stack :=
  fixed c stack env (.NoEllipses,[]) (.NoEllipses,[.RefT (.«% %» .Null heap)])
    (nil_backed c .NoEllipses)
    (cons_backed .NoEllipses (CandidateValMembership.valid_candidate_in_table c _
      ((FiniteValidTypes.validCandidates_spec c _).2 ((FiniteValidTypes.heapCandidates_spec c heap).1 hh)))
      (nil_backed c .NoEllipses))
    (.«REF.NULL» heap) (fun n => ConstRefNullDispatch.ref_null_dispatch_total c stack heap n
      ((FiniteValidTypes.heapCandidates_spec c heap).1 hh))

def funcRef (c : context) (stack : inferresulttype) (env : Env c) (e : ConstructiveBodyLookup.Entry c.FUNCS)
    (hr : FreeUnionValidation.HasFunc c.REFS e.index) : Production c stack :=
  fixed c stack env (.NoEllipses,[]) (.NoEllipses,[.RefT (.«% %» .NoNull (.DefHT e.value))])
    (nil_backed c .NoEllipses)
    (cons_backed .NoEllipses (CandidateValMembership.table_definition_in_table c e.value
      (env.provenance.funcs e.value e.mem) .NoNull) (nil_backed c .NoEllipses))
    (.«REF.FUNC» e.index) (fun n => (ConstRefFuncEffect.ref_func_instruction_iff c stack e.index _ n n).2
      ⟨e.value,e.lookup,hr,rfl,rfl⟩)

def equal (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  let rb := ConstructiveBodyReferenceMatcher.base_backed c .Null .EqHT (by simp [HeaptypeValidation.baseHeaptypes])
  let empty := nil_backed c .NoEllipses
  fixed c stack env (.NoEllipses,[.RefT (.«% %» .Null .EqHT),.RefT (.«% %» .Null .EqHT)]) (.NoEllipses,[.NumT .I32T])
    (cons_backed .NoEllipses rb (cons_backed .NoEllipses rb empty))
    (cons_backed .NoEllipses (num_backed c _) empty) .«REF.EQ» (ConstructiveBodyReferenceCalls.equal c stack)

def i31 (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  fixed c stack env (.NoEllipses,[.NumT .I32T]) (.NoEllipses,[.RefT (.«% %» .NoNull .I31HT)])
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (ConstructiveBodyReferenceMatcher.base_backed c .NoNull .I31HT (by simp [HeaptypeValidation.baseHeaptypes]))
      (nil_backed c .NoEllipses)) .«REF.I31» (ConstI31Dispatch.i31_dispatch_total c stack)

def getI31 (c : context) (stack : inferresulttype) (env : Env c) (extension : SpecTec.extension) : Production c stack :=
  fixed c stack env (.NoEllipses,[.RefT (.«% %» .Null .I31HT)]) (.NoEllipses,[.NumT .I32T])
    (cons_backed .NoEllipses (ConstructiveBodyReferenceMatcher.base_backed c .Null .I31HT (by simp [HeaptypeValidation.baseHeaptypes]))
      (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    (.«I31.GET» extension) (ConstructiveBodyReferenceCalls.getI31 c stack extension)

def arrayLength (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  fixed c stack env (.NoEllipses,[.RefT (.«% %» .Null .ArrayHT)]) (.NoEllipses,[.NumT .I32T])
    (cons_backed .NoEllipses (ConstructiveBodyReferenceMatcher.base_backed c .Null .ArrayHT (by simp [HeaptypeValidation.baseHeaptypes]))
      (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    .«ARRAY.LEN» (ConstructiveBodyReferenceCalls.arrayLength c stack)

def isNull (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) : Production c stack :=
  fixed c stack env (.NoEllipses,[.RefT (.«% %» .Null heap)]) (.NoEllipses,[.NumT .I32T])
    (cons_backed .NoEllipses (retype c nu .Null heap (peek_backed c stack hs nu heap hp)) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    .«REF.IS_NULL» (ConstructiveBodyReferenceCalls.isNull c stack nu heap hp)

def asNonNull (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) : Production c stack :=
  fixed c stack env (.NoEllipses,[.RefT (.«% %» .Null heap)]) (.NoEllipses,[.RefT (.«% %» .NoNull heap)])
    (cons_backed .NoEllipses (retype c nu .Null heap (peek_backed c stack hs nu heap hp)) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (retype c nu .NoNull heap (peek_backed c stack hs nu heap hp)) (nil_backed c .NoEllipses))
    .«REF.AS_NON_NULL» (ConstructiveBodyReferenceCalls.asNonNull c stack nu heap hp)

def externConvert (c : context) (stack : inferresulttype) (env : Env c) (op : externop_) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) : Production c stack :=
  fixed c stack env (.NoEllipses,[.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1)])
    (.NoEllipses,[.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).2)])
    (cons_backed .NoEllipses (ConstructiveBodyReferenceMatcher.base_backed c nu _ (by cases op <;> simp [ExternopTypeDecision.typeExternopResult,HeaptypeValidation.baseHeaptypes])) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (ConstructiveBodyReferenceMatcher.base_backed c nu _ (by cases op <;> simp [ExternopTypeDecision.typeExternopResult,HeaptypeValidation.baseHeaptypes])) (nil_backed c .NoEllipses))
    (.«EXTERN.CONVERT» op) (ConstructiveBodyReferenceCalls.externConvert c stack op nu heap hp)

def peeked (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) : List (Production c stack) :=
  match hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack) with
  | none => []
  | some (.«% %» nu heap) =>
    [isNull c stack env hs nu heap hp,asNonNull c stack env hs nu heap hp,
     externConvert c stack env .Internalize nu heap hp,externConvert c stack env .Externalize nu heap hp]

def all (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) : List (Production c stack) :=
  ((FiniteValidTypes.heapCandidates c).attach.map fun h => nullRef c stack env h.val h.property) ++
  ((ConstructiveBodyLookup.entries c.FUNCS).flatMap fun e =>
    if hr : ConstRefFuncProduction.hasFuncBool c.REFS e.index=true then
      [funcRef c stack env e ((ConstRefFuncProduction.has_func_bool_iff _ _).1 hr)] else []) ++
  [equal c stack env,i31 c stack env,getI31 c stack env .SX,getI31 c stack env .ZX,arrayLength c stack env] ++
  peeked c stack env hs

#print axioms all
end properties.wasm_module_ok.ConstructiveBodyReferenceProductions
