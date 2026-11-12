import properties.wasm_module_ok.ConstructiveFreshSoundness

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveSignatureCoverage
open SpecTec properties.wasm_module_ok
open ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace ConstructiveSignaturePlan
open ConstructiveSignatureState ConstructiveSignatureChecks ConstructiveFreshSoundness
open ConstructiveTypeEnvironment ConstructiveTypeCopy ConstructiveVarianceShapes

/-- Backward-only refinement: an original successful parent check yields the
exact constructive production. No check is executed by the generator. -/
theorem entry_compatible (c full : context) (hsize : c.TYPES.length = full.TYPES.length)
    (hr : CandidateTypeReady.Ready full) (r : heaptype → heaptype → Bool)
    (hback : ∀ a b, HeapBound c.TYPES.length a → HeapBound c.TYPES.length b →
      (ReadyHeapMatch.readyHeapMatch full a b).getD false = true → r a b = true)
    (env : List (Signature c)) (hd : Describes c full env)
    (e : Entry) (he : EntryAllowed (headers c env) e)
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind})
    (hcheck : CandidateStaticSuperList.staticSuperChecks full env.length s.val
      (parentSyntax e.parent) = true) : Compatible c r env e he s.val := by
  rcases e with ⟨header,p⟩
  cases p with
  | none => trivial
  | some i =>
    have hi : i < env.length := ConstructiveSignatureTrace.parent_bound c env _ he i rfl
    have hget := List.getElem?_eq_getElem hi
    obtain ⟨dt,ps,closed,hlookup,hu,hrel⟩ := hd i env[i] hget
    have hh : (i < env.length ∧ env[i].header.finality = .NoFinal) ∧
        MatchStrtypeConditional.strMatch
          (fun a b => (ReadyHeapMatch.readyHeapMatch full a b).getD false) s.val closed = true := by
      simpa [parentSyntax,CandidateStaticSuperList.staticSuperChecks,
        CandidateStaticSuperCheck.staticSuperCheck,hlookup,ReadyStaticSubtypeMatch.staticSuperMatch,hu]
        using hcheck
    have hs := shape_bound c s.val s.property.1
    have hp := shape_bound c env[i].shape env[i].valid
    have hclosed := ConstructiveTypeSignatures.matching full hr s.val env[i].shape closed
      (hsize ▸ hs) hrel
    have hm := ConstructiveVarianceMonotone.shapes c.TYPES.length _ r hback
      s.val env[i].shape hs hp (hclosed.symm.trans hh.2)
    simpa only [Compatible,parent] using hm

theorem checks_trace (c full : context) (hsize : c.TYPES.length = full.TYPES.length)
    (hr : CandidateTypeReady.Ready full) (r : heaptype → heaptype → Bool)
    (hback : ∀ a b, HeapBound c.TYPES.length a → HeapBound c.TYPES.length b →
      (ReadyHeapMatch.readyHeapMatch full a b).getD false = true → r a b = true)
    (env : List (Signature c)) (hd : Describes c full env)
    (sts : List SpecTec.subtype) (he : Allowed (headers c env) (sts.map entryOf))
    (hparents : ∀ st ∈ sts, supers st = parentSyntax (entryOf st).parent)
    (hsource : CandidateSourceChecks.sourceChecks c sts = true)
    (hchecks : checksFrom full env.length sts = true)
    (hremain : Remaining full env.length sts) :
    Trace c r env (sts.map entryOf) he sts := by
  induction sts generalizing env with
  | nil => trivial
  | cons st sts ih =>
    cases st with
    | SubT fin ps raw =>
      let e := entryOf (.SubT fin ps raw)
      have hps : ps = parentSyntax e.parent := hparents (.SubT fin ps raw) (by simp)
      have hv : StrtypeValidation.strtypeValid c raw = true := by
        have hsub := (ConstructiveTypeCopySource.subs_valid c _).1 hsource (.SubT fin ps raw) (by simp)
        simp only [SubtypeValidation.subtypeValid,Bool.and_eq_true] at hsub
        exact hsub.2
      let s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind} :=
        ⟨raw,(valid_shape_iff c raw).2 hv,rfl⟩
      have hst : (.SubT fin ps raw : SpecTec.subtype) = .SubT e.header.finality (parentSyntax e.parent) s.val := by
        change (SpecTec.subtype.SubT fin ps raw) = .SubT fin (parentSyntax (parentOf ps)) raw
        exact congrArg (fun ps => SpecTec.subtype.SubT fin ps raw) hps
      have hcheckParts : CandidateStaticSuperList.staticSuperChecks full env.length raw ps = true ∧
          checksFrom full (env.length+1) sts = true := by simpa [checksFrom] using hchecks
      have hcomp := entry_compatible c full hsize hr r hback env hd e he.1 s
        (by simpa only [s,← hps] using hcheckParts.1)
      have hnew : At full env.length e.header.finality s.val := by
        simpa [e,entryOf,header,s] using hremain 0 fin ps raw rfl
      have hd' := describes_append c full env (signature c e s) hd hnew
      have he' := allowed_tail c env e (sts.map entryOf) he s
      have hsource' : CandidateSourceChecks.sourceChecks c sts = true := by
        simp only [CandidateSourceChecks.sourceChecks,Bool.and_eq_true] at hsource
        exact hsource.2
      have hremain' : Remaining full (env ++ [signature c e s]).length sts := by
        simpa using remaining_tail full env.length _ sts hremain
      refine ⟨s,hst,hcomp,?_⟩
      exact ih _ hd' he' (fun st hm => hparents st (by simp [hm])) hsource'
        (by simpa using hcheckParts.2) hremain'

end properties.wasm_module_ok.ConstructiveSignatureCoverage
