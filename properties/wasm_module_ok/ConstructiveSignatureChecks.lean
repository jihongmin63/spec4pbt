import properties.wasm_module_ok.ConstructiveSignatureState
import properties.wasm_module_ok.ConstructiveVarianceMonotone

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveSignatureChecks
open SpecTec properties.wasm_module_ok
open ConstructiveTypeSkeleton ConstructiveSignaturePlan ConstructiveSignatureState
open ConstructiveTypeEnvironment ConstructiveTypeCopy ConstructiveVarianceShapes

theorem shape_bound (c : context) (s : strtype) (hs : ValidShape c.TYPES.length s) :
    StrBound c.TYPES.length s :=
  ConstructiveTypeCopySource.str_bound c s ((valid_shape_iff c s).1 hs)

theorem entry_check (c full : context) (hsize : c.TYPES.length = full.TYPES.length)
    (hr : CandidateTypeReady.Ready full) (r : heaptype → heaptype → Bool)
    (hsound : ∀ a b, HeapBound c.TYPES.length a → HeapBound c.TYPES.length b →
      r a b = true → (ReadyHeapMatch.readyHeapMatch full a b).getD false = true)
    (env : List (Signature c)) (hd : Describes c full env)
    (e : Entry) (he : EntryAllowed (headers c env) e)
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ ConstructiveTypeSkeletonTrace.kind s = e.header.kind})
    (hcomp : Compatible c r env e he s.val) :
    CandidateStaticSuperList.staticSuperChecks full env.length s.val (parentSyntax e.parent) = true := by
  rcases e with ⟨header,p⟩
  cases p with
  | none => rfl
  | some i =>
    have hi : i < env.length := ConstructiveSignatureTrace.parent_bound c env _ he i rfl
    have hget := List.getElem?_eq_getElem hi
    have hfin : env[i].header.finality = .NoFinal := by
      obtain ⟨h,hlookup,hfin,hkind⟩ := he
      have hl : (headers c env)[i]? = some env[i].header := by simp [headers,hget]
      have hh := Option.some.inj (hl.symm.trans hlookup)
      exact hh ▸ hfin
    have hc : MatchStrtypeConditional.strMatch r s.val env[i].shape = true := by
      simpa only [Compatible,parent] using hcomp
    obtain ⟨dt,ps,closed,hlookup,hu,hrel⟩ := hd i env[i] hget
    have hs := shape_bound c s.val s.property.1
    have hp := shape_bound c env[i].shape env[i].valid
    have hm := ConstructiveVarianceMonotone.shapes c.TYPES.length r _ hsound
      s.val env[i].shape hs hp hc
    have hclosed := ConstructiveTypeSignatures.matching full hr s.val env[i].shape closed
      (hsize ▸ hs) hrel
    have hmclosed : MatchStrtypeConditional.strMatch
        (fun a b => (ReadyHeapMatch.readyHeapMatch full a b).getD false) s.val closed = true :=
      hclosed.trans hm
    simp [parentSyntax,CandidateStaticSuperList.staticSuperChecks,
      CandidateStaticSuperCheck.staticSuperCheck,hlookup,ReadyStaticSubtypeMatch.staticSuperMatch,
      hu,hfin,hi,hmclosed]

def checksFrom (full : context) : Nat → List SpecTec.subtype → Bool
  | _, [] => true
  | base, .SubT _ ps st :: sts =>
    CandidateStaticSuperList.staticSuperChecks full base st ps && checksFrom full (base+1) sts

theorem trace_checks (c full : context) (hsize : c.TYPES.length = full.TYPES.length)
    (hr : CandidateTypeReady.Ready full) (r : heaptype → heaptype → Bool)
    (hsound : ∀ a b, HeapBound c.TYPES.length a → HeapBound c.TYPES.length b →
      r a b = true → (ReadyHeapMatch.readyHeapMatch full a b).getD false = true)
    (env : List (Signature c)) (hd : Describes c full env)
    (es : List Entry) (he : Allowed (headers c env) es)
    (sts : List SpecTec.subtype) (ht : Trace c r env es he sts)
    (hremain : Remaining full env.length sts) : checksFrom full env.length sts = true := by
  induction es generalizing env sts with
  | nil => cases sts <;> simp_all [Trace,checksFrom]
  | cons e es ih =>
    cases sts with
    | nil => cases ht
    | cons st sts =>
      obtain ⟨s,rfl,hcomp,htail⟩ := ht
      have hhead := entry_check c full hsize hr r hsound env hd e he.1 s hcomp
      have hnew : At full env.length e.header.finality s.val := by
        simpa using hremain 0 e.header.finality (parentSyntax e.parent) s.val rfl
      have hd' := describes_append c full env (signature c e s) hd hnew
      have hremain' : Remaining full (env ++ [signature c e s]).length sts := by
        simpa using remaining_tail full env.length _ sts hremain
      have htailcheck := ih _ hd' _ _ htail hremain'
      simpa [checksFrom,hhead] using htailcheck

theorem paired_from (full : context) (base offset : Nat) (sts : List SpecTec.subtype) :
    CandidateGroupSuperChecks.pairedChecks full base (List.range' offset sts.length) sts =
      checksFrom full (base+offset) sts := by
  induction sts generalizing offset with
  | nil => rfl
  | cons st sts ih =>
    cases st
    simp [List.range'_succ,CandidateGroupSuperChecks.pairedChecks,checksFrom,ih,Nat.add_assoc]

theorem paired_zero (full : context) (base : Nat) (sts : List SpecTec.subtype) :
    CandidateGroupSuperChecks.pairedChecks full base (List.range sts.length) sts =
      checksFrom full base sts := by
  simpa [List.range_eq_range'] using paired_from full base 0 sts

end properties.wasm_module_ok.ConstructiveSignatureChecks
