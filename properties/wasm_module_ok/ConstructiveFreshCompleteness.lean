import properties.wasm_module_ok.ConstructiveSignatureCoverage
import properties.wasm_module_ok.CandidatePairedCompleteness

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveFreshCompleteness
open SpecTec properties.wasm_module_ok
open ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace ConstructiveSignaturePlan
open ConstructiveSignatureState ConstructiveSignatureChecks ConstructiveSignatureCoverage
open ConstructiveFreshSignatures ConstructiveFreshSoundness
open ConstructiveTypeEnvironment ConstructiveTypeCopy ConstructiveTypeCopySemantics

theorem original_closed (c result : context) (sts : List SpecTec.subtype) (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish)
    (hb : GroupBound (c.TYPES.length+sts.length) sts) : result = extended c sts hb := by
  have hc := CandidateRectypeTable.rectype_success_candidateContext c result sts start finish hrect
  have ht : CandidateRectypeTable.transformed c sts =
      some (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts hb) := by
    simpa [CandidateRectypeTable.transformed,Nat.add_comm] using
      group_value_correct c.TYPES c.TYPES.length (Nat.le_refl _) sts hb
  simpa [CandidateRectypeTable.candidateContext,ht,extended,definitions] using hc.symm

theorem original_layout (c result : context) (env : List (Signature c))
    (hmeta : Tracks c (headers c env)) (sts : List SpecTec.subtype) (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    ParentLayout c.TYPES.length sts ((sts.map entryOf).map Entry.parent) := by
  constructor
  · simp
  · intro i p hp
    simp only [List.getElem?_map,Option.map_eq_some_iff] at hp
    obtain ⟨e,⟨st,hget,rfl⟩,he⟩ := hp
    obtain ⟨ha,hparents⟩ := original_entry c result (headers c env) sts start finish i st hmeta hrect hget
    cases st with
    | SubT f ps raw =>
      refine ⟨f,raw,?_,?_⟩
      · have hps : ps = parentSyntax p := by simpa [← he,parentSyntax,supers] using hparents
        simpa only [hps] using hget
      · intro k hk
        have hek : (entryOf (.SubT f ps raw)).parent = some k := he.trans hk
        simp only [EntryAllowed,hek] at ha
        obtain ⟨header,hlookup,_,_⟩ := ha
        have hlt := (List.getElem?_eq_some_iff.mp hlookup).1
        have hil := (List.getElem?_eq_some_iff.mp hget).1
        simpa [List.length_append,List.length_map,List.length_take,Nat.min_eq_left (Nat.le_of_lt hil),hmeta.1]
          using hlt

/-- Every original successful group whose whole closed group is absent from
the earlier table is generated with its exact raw syntax. Freshness is used
only in this backward proof, never as a candidate-selection runtime test. -/
theorem fresh_complete (c result : context) (env : List (Signature c))
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hmeta : Tracks c (headers c env)) (hdenote : Describes c c env)
    (sts : List SpecTec.subtype) (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish)
    (hb : GroupBound (c.TYPES.length+sts.length) sts)
    (hfresh : ∀ p i : Nat, c.TYPES[p]? ≠ some (.DefT
      (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts hb) i)) :
    Gen.support (fresh c env) (.RecT sts) := by
  have hlen : env.length = c.TYPES.length := by simpa [headers] using hmeta.1
  obtain ⟨hskeleton,hparents⟩ := original_skeleton c result (headers c env) sts start finish hmeta hrect
  have he : Allowed (headers c env) (sts.map entryOf) := (skeleton_support _ _).1 hskeleton
  have hp := original_layout c result env hmeta sts start finish hrect
  have hout := original_closed c result sts start finish hrect hb
  have hready := CandidateTypeReady.validated_types_ready c hc
  have hr := ready c sts hb _ hp hready
  have hsize : (capacity c (sts.map entryOf).length).TYPES.length = (extended c sts hb).TYPES.length := by
    simp [extended,definitions]
  have hback : ∀ a b, HeapBound (capacity c (sts.map entryOf).length).TYPES.length a →
      HeapBound (capacity c (sts.map entryOf).length).TYPES.length b →
      (ReadyHeapMatch.readyHeapMatch (extended c sts hb) a b).getD false = true →
      relation c (headers c env) (sts.map entryOf) a b = true := by
    intro a b ha hb' hmatch
    have hexact := ConstructiveTypeMetadata.heap_exact c (headers c env) sts hb
      ((sts.map entryOf).map Entry.parent) hp hready hmeta
      ((headers c env) ++ (sts.map entryOf).map Entry.header)
      (by simp [List.map_map,entryOf,Function.comp_def]) hfresh a b (hsize ▸ ha) (hsize ▸ hb')
    exact hexact.trans hmatch
  have hd := describes_lift c (extended c sts hb) _ rfl env hdenote (sts.map entryOf).length
  have hcandidate := CandidateRectypeTable.rectype_success_candidateContext c result sts start finish hrect
  have hsource := CandidateSourceChecks.rectype_success_sourceChecks c result result sts start finish hrect hcandidate
  rw [hout] at hsource
  have hsource' := source_same_length _ _ hsize.symm sts hsource
  have hpaired := CandidatePairedCompleteness.pairedChecks_of_success c result sts start finish hc hrect
  rw [hout,paired_zero] at hpaired
  have hcheck : checksFrom (extended c sts hb) (liftEnv c (sts.map entryOf).length env).length sts = true := by
    simpa [liftEnv,hlen] using hpaired
  have hremain : Remaining (extended c sts hb) (liftEnv c (sts.map entryOf).length env).length sts := by
    simpa [liftEnv,hlen] using remaining_closed c sts hb
  have ht := checks_trace _ _ hsize hr _ hback _ hd sts (by simpa using he)
    hparents hsource' hcheck hremain
  apply fresh_covers c env (sts.map entryOf) he sts
  exact (fill_support _ _ _ _ _ _ _).2 ht

end properties.wasm_module_ok.ConstructiveFreshCompleteness
