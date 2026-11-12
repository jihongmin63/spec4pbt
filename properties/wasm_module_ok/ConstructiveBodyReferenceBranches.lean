import properties.wasm_module_ok.ConstructiveBodyValidReferences
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceBranches
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyIndexedProductions ConstructiveBodyNonemptyLabels ConstructiveBodyReferenceDifference

def onNull (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (e : ConstructiveBodyLookup.Entry c.LABELS) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) : Production c stack :=
  let ref := ConstructiveBodyReferenceProductions.peek_backed c stack hs nu heap hp
  let labels := env.labels e.value e.mem
  fixed c stack env (.NoEllipses,e.value++[valtype.RefT (.«% %» .Null heap)]) (.NoEllipses,e.value++[valtype.RefT (.«% %» .NoNull heap)])
    (append_backed .NoEllipses labels (cons_backed .NoEllipses (ConstructiveBodyReferenceProductions.retype c nu .Null heap ref) (nil_backed c .NoEllipses)))
    (append_backed .NoEllipses labels (cons_backed .NoEllipses (ConstructiveBodyReferenceProductions.retype c nu .NoNull heap ref) (nil_backed c .NoEllipses)))
    (.BR_ON_NULL e.index) (ConstructiveBodyReferenceBranchCalls.onNull c stack e nu heap hp)

def onNonNull (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (label : Label c) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap))
    (hm : CandidateValMatch.candidateValMatch c (valtype.RefT (.«% %» .NoNull heap)) label.last=true) : Production c stack :=
  let ref := ConstructiveBodyReferenceProductions.peek_backed c stack hs nu heap hp
  fixed c stack env (.NoEllipses,label.front++[valtype.RefT (.«% %» .Null heap)]) (.NoEllipses,label.front)
    (append_backed .NoEllipses (label.frontBacked env)
      (cons_backed .NoEllipses (ConstructiveBodyReferenceProductions.retype c nu .Null heap ref) (nil_backed c .NoEllipses)))
    (label.frontBacked env) (.BR_ON_NON_NULL label.entry.index)
    (ConstructiveBodyReferenceBranchCalls.onNonNull c stack label nu heap hp (fun n => by
      rw [←hm]
      exact CandidateValMatch.candidate_val_match_total c _ _ n env.ready
        (ConstructiveBodyReferenceProductions.retype c nu .NoNull heap ref) (label.lastBacked env)))

def onCast (c : context) (stack : inferresulttype) (env : Env c) (label : Label c)
    (r1 r2 : ConstructiveBodyValidReferences.Ref c)
    (hr : ConstructiveBodyReferenceMatcher.refMatch c r2.value r1.value=true)
    (hm : CandidateValMatch.candidateValMatch c (valtype.RefT r2.value) label.last=true) : Production c stack :=
  fixed c stack env (.NoEllipses,label.front++[valtype.RefT r1.value]) (.NoEllipses,label.front++[valtype.RefT (difference r1.value r2.value)])
    (append_backed .NoEllipses (label.frontBacked env) (cons_backed .NoEllipses r1.backed (nil_backed c .NoEllipses)))
    (append_backed .NoEllipses (label.frontBacked env) (cons_backed .NoEllipses (backed c _ _ r1.backed) (nil_backed c .NoEllipses)))
    (.BR_ON_CAST label.entry.index r1.value r2.value)
    (ConstructiveBodyReferenceBranchCalls.onCast c stack label r1.value r2.value r1.call r2.call
      (fun n => by rw [←hr]; exact ConstructiveBodyReferenceMatcher.total c _ _ n env.ready r2.backed r1.backed)
      (fun n => by rw [←hm]; exact CandidateValMatch.candidate_val_match_total c _ _ n env.ready r2.backed (label.lastBacked env)))

def onCastFail (c : context) (stack : inferresulttype) (env : Env c) (label : Label c)
    (r1 r2 : ConstructiveBodyValidReferences.Ref c)
    (hr : ConstructiveBodyReferenceMatcher.refMatch c r2.value r1.value=true)
    (hm : CandidateValMatch.candidateValMatch c (valtype.RefT (difference r1.value r2.value)) label.last=true) : Production c stack :=
  fixed c stack env (.NoEllipses,label.front++[valtype.RefT r1.value]) (.NoEllipses,label.front++[valtype.RefT r2.value])
    (append_backed .NoEllipses (label.frontBacked env) (cons_backed .NoEllipses r1.backed (nil_backed c .NoEllipses)))
    (append_backed .NoEllipses (label.frontBacked env) (cons_backed .NoEllipses r2.backed (nil_backed c .NoEllipses)))
    (.BR_ON_CAST_FAIL label.entry.index r1.value r2.value)
    (ConstructiveBodyReferenceBranchCalls.onCastFail c stack label r1.value r2.value r1.call r2.call
      (fun n => by rw [←hr]; exact ConstructiveBodyReferenceMatcher.total c _ _ n env.ready r2.backed r1.backed)
      (fun n => by rw [←hm]; exact CandidateValMatch.candidate_val_match_total c _ _ n env.ready (backed c _ _ r1.backed) (label.lastBacked env)))

def peeked (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) : List (Production c stack) :=
  match hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack) with
  | none => []
  | some (.«% %» nu heap) =>
    ((ConstructiveBodyLookup.entries c.LABELS).map fun e => onNull c stack env hs e nu heap hp) ++
    ((ConstructiveBodyNonemptyLabels.all c).flatMap fun label =>
      if hm : CandidateValMatch.candidateValMatch c (valtype.RefT (.«% %» .NoNull heap)) label.last=true then
        [onNonNull c stack env hs label nu heap hp hm] else [])

def casted (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  (ConstructiveBodyNonemptyLabels.all c).flatMap fun label =>
    (ConstructiveBodyValidReferences.all c).flatMap fun r1 =>
      (ConstructiveBodyValidReferences.all c).flatMap fun r2 =>
        if hr : ConstructiveBodyReferenceMatcher.refMatch c r2.value r1.value=true then
          (if hm : CandidateValMatch.candidateValMatch c (valtype.RefT r2.value) label.last=true then
            [onCast c stack env label r1 r2 hr hm] else []) ++
          (if hm : CandidateValMatch.candidateValMatch c (valtype.RefT (difference r1.value r2.value)) label.last=true then
            [onCastFail c stack env label r1 r2 hr hm] else [])
        else []

def all (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) : List (Production c stack) :=
  peeked c stack env hs ++ casted c stack env

#print axioms all
end properties.wasm_module_ok.ConstructiveBodyReferenceBranches
