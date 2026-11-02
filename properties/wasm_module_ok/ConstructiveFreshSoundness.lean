import properties.wasm_module_ok.ConstructiveSignatureChecks
import properties.wasm_module_ok.CandidateRectypeConstruction

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveFreshSoundness
open SpecTec properties.wasm_module_ok
open ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace ConstructiveSignaturePlan
open ConstructiveSignatureState ConstructiveSignatureChecks ConstructiveFreshSignatures
open ConstructiveTypeEnvironment ConstructiveTypeCopy ConstructiveTypeCopySemantics

theorem source_same_length (c d : context) (hlen : c.TYPES.length = d.TYPES.length)
    (sts : List SpecTec.subtype) (h : CandidateSourceChecks.sourceChecks c sts = true) :
    CandidateSourceChecks.sourceChecks d sts = true := by
  apply (ConstructiveTypeCopySource.subs_valid d sts).2
  intro st hm
  have hv := (ConstructiveTypeCopySource.subs_valid c sts).1 h st hm
  rcases st with ⟨f,ps,s⟩
  have hp : (ps.length ≤ 1 ∧ SubtypeHeadListValidation.allHeaptypesValid c ps = true) ∧
      StrtypeValidation.strtypeValid c s = true := by simpa [SubtypeValidation.subtypeValid] using hv
  have hshape := (ConstructiveVarianceShapes.valid_shape_iff d s).1
    (hlen ▸ (ConstructiveVarianceShapes.valid_shape_iff c s).2 hp.2)
  have hparents : SubtypeHeadListValidation.allHeaptypesValid d ps = true := by
    apply (ConstructiveTypeCopySource.heaps_valid d ps).2
    intro p hm
    exact (ConstructiveTypeCopySource.heap_bound d p).2
      (hlen ▸ (ConstructiveTypeCopySource.heap_bound c p).1
        ((ConstructiveTypeCopySource.heaps_valid c ps).1 hp.1.2 p hm))
  simpa [SubtypeValidation.subtypeValid,hshape,hparents] using hp.1.1

theorem signatures_trace (c : context) (env : List (Signature c))
    (es : List Entry) (he : Allowed (headers c env) es) (sts : List SpecTec.subtype)
    (hs : Gen.support (signatures c env es he) sts) :
    Trace (capacity c es.length) (relation c (headers c env) es)
      (liftEnv c es.length env) es (by simpa using he) sts :=
  (fill_support _ _ _ _ _ _ _).1 hs

theorem signatures_facts (c : context) (env : List (Signature c))
    (hlen : env.length = c.TYPES.length)
    (es : List Entry) (he : Allowed (headers c env) es) (sts : List SpecTec.subtype)
    (hs : Gen.support (signatures c env es he) sts) :
    sts.length = es.length ∧ sts.map header = es.map Entry.header ∧
      CandidateSourceChecks.sourceChecks (capacity c es.length) sts = true := by
  apply ConstructiveSignatureTrace.facts _ _ _ _ _ _ (signatures_trace c env es he sts hs)
  simp [liftEnv,hlen]

theorem signatures_bound (c : context) (env : List (Signature c))
    (hlen : env.length = c.TYPES.length)
    (es : List Entry) (he : Allowed (headers c env) es) (sts : List SpecTec.subtype)
    (hs : Gen.support (signatures c env es he) sts) :
    GroupBound (c.TYPES.length+sts.length) sts := by
  obtain ⟨hl,_,hv⟩ := signatures_facts c env hlen es he sts hs
  simpa [hl] using ConstructiveTypeCopySource.group_bound (capacity c es.length) sts hv

/-- The actual original ordered Rectype_ok call succeeds for every signature
pass output. All obligations on the new group are derived from construction;
the assumptions describe only the previously constructed type environment. -/
theorem signatures_sound (c : context) (env : List (Signature c))
    (hc : CandidateTypeReady.Ready c) (hn : CandidateNestedReady.nestedTableReady c = true)
    (hmeta : Tracks c (headers c env)) (hdenote : Describes c c env)
    (es : List Entry) (he : Allowed (headers c env) es) (sts : List SpecTec.subtype)
    (hs : Gen.support (signatures c env es he) sts)
    (hb : GroupBound (c.TYPES.length+sts.length) sts) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      n (.success (.of (extended c sts hb))) n := by
  have hlen : env.length = c.TYPES.length := by simpa [headers] using hmeta.1
  have ht := signatures_trace c env es he sts hs
  obtain ⟨hl,hm,hsource⟩ := signatures_facts c env hlen es he sts hs
  have hsize : (capacity c es.length).TYPES.length = (extended c sts hb).TYPES.length := by
    simp [extended,definitions,hl]
  have hp : ParentLayout c.TYPES.length sts (es.map Entry.parent) := by
    simpa [liftEnv,hlen] using ConstructiveSignatureTrace.layout _ _ _ _ _ _ ht
  have hr := ready c sts hb (es.map Entry.parent) hp hc
  have hsound : ∀ a b, HeapBound (capacity c es.length).TYPES.length a →
      HeapBound (capacity c es.length).TYPES.length b → relation c (headers c env) es a b = true →
      (ReadyHeapMatch.readyHeapMatch (extended c sts hb) a b).getD false = true := by
    intro a b ha hb'
    exact ConstructiveTypeMetadata.heap_sound c (headers c env) sts hb
      (es.map Entry.parent) hp hc hmeta ((headers c env) ++ es.map Entry.header)
      (by rw [hm]) a b (hsize ▸ ha) (hsize ▸ hb')
  have hd := describes_lift c (extended c sts hb) _ rfl env hdenote es.length
  have hremain : Remaining (extended c sts hb) (liftEnv c es.length env).length sts := by
    simpa [liftEnv,hlen] using remaining_closed c sts hb
  have hchecks := trace_checks _ _ hsize hr _ hsound _ hd es _ sts ht hremain
  have hpaired : CandidateGroupSuperChecks.pairedChecks (extended c sts hb)
      c.TYPES.length (List.range sts.length) sts = true := by
    rw [paired_zero]
    simpa [liftEnv,hlen] using hchecks
  apply CandidateRectypeConstruction.rectype_success_of_checks c sts
    (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts hb) n
  · simpa [CandidateRectypeTable.transformed,Nat.add_comm] using
      group_value_correct c.TYPES c.TYPES.length (Nat.le_refl _) sts hb
  · exact source_same_length _ _ hsize sts hsource
  · exact hr
  · exact ConstructiveTypeNested.nested c sts hb hn
  · exact hpaired

theorem fresh_sound (c : context) (env : List (Signature c))
    (hc : CandidateTypeReady.Ready c) (hn : CandidateNestedReady.nestedTableReady c = true)
    (hmeta : Tracks c (headers c env)) (hdenote : Describes c c env)
    (rt : rectype) (hg : Gen.support (fresh c env) rt) (n : Nat) :
    ∃ out : context, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c rt⟩) n (.success (.of out)) n := by
  obtain ⟨es,_,sts,hs,rfl⟩ := hg
  have hlen : env.length = c.TYPES.length := by simpa [headers] using hmeta.1
  have hb := signatures_bound c env hlen es.val es.property sts hs
  exact ⟨extended c sts hb,signatures_sound c env hc hn hmeta hdenote es.val es.property sts hs hb n⟩

end properties.wasm_module_ok.ConstructiveFreshSoundness
