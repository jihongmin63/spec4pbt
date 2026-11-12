import properties.wasm_module_ok.ConstructiveTypeCopyPrefix
import properties.wasm_module_ok.CandidatePairedCompleteness
import properties.wasm_module_ok.SubstPrefixDeftype
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopySoundness
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveTypeCopyExact
open ConstructiveTypeCopySource ConstructiveTypeCopyPreserve
open properties.wasm_module_ok.ConstructiveTypeCopyRealization properties.wasm_module_ok.ConstructiveTypeCopyCompatibility
open properties.wasm_module_ok.ConstructiveTypeCopyGroupCompatibility properties.wasm_module_ok.ConstructiveTypeCopyPrefix

/-- Every supported copy of a previously constructed valid group succeeds in
its current validated prefix. Readiness, provenance, source validation and
subtype compatibility of the NEW group are all proved here. The only original
derivation assumed is for the already-existing earlier source group. -/
theorem copy_sound (before after c : context) (sts outs : List SpecTec.subtype)
    (start finish n : Nat) (tail : List deftype)
    (hbefore : ValidatedTypeChain.ValidatedTypes before)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (he : c.TYPES=after.TYPES++tail)
    (hle : before.TYPES.length≤c.TYPES.length)
    (hb : GroupBound (before.TYPES.length+sts.length) sts)
    (hg : Gen.support (group c.TYPES before.TYPES.length hle sts hb) (.RecT outs)) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Rectype_ok c (.RecT outs)⟩)
      n (.success (.of (extend c sts.length (groupValue c.TYPES before.TYPES.length hle sts hb)))) n := by
  have hcandidate := CandidateRectypeTable.rectype_success_candidateContext before after sts start finish hrect
  have hsource := CandidateSourceChecks.rectype_success_sourceChecks before after after sts start finish hrect hcandidate
  cases ht : CandidateRectypeTable.transformed before sts with
  | none => simp [CandidateRectypeTable.candidateContext,ht] at hcandidate
  | some r =>
    have hafter : after=extend before sts.length r := by
      simpa [CandidateRectypeTable.candidateContext,ht,extend,defs] using hcandidate.symm
    have hprefix : c.TYPES=before.TYPES++(defs sts.length r++tail) := by
      rw [he,hafter]
      simp only [extend,List.append_assoc]
    have ht' := SubstPrefixDeftype.substRectypeResult_prefix
      (.RecT (rollSubtypes sts before.TYPES.length (sts.length+before.TYPES.length)))
      before.TYPES (defs sts.length r++tail) r ht
    rw [←hprefix] at ht'
    have hvalue := group_value_correct c.TYPES before.TYPES.length hle sts hb
    have hvalue' : groupValue c.TYPES before.TYPES.length hle sts hb=r := by
      apply Option.some.inj
      exact hvalue.symm.trans (by simpa only [Nat.add_comm] using ht')
    rw [hvalue']
    have hgroup : ∀ i<sts.length,c.TYPES[before.TYPES.length+i]?=some (.DefT r i) := by
      intro i hi
      have hi' : after.TYPES[before.TYPES.length+i]?=some (.DefT r i) := by
        rw [hafter]
        exact new_lookup before sts.length r i hi
      rw [he,List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi').1]
      exact hi'
    have hr := CandidateTypeReady.validated_types_ready c hc
    have hn : CandidateNestedReady.nestedTableReady c=true :=
      (CandidateNestedReady.nestedTableReady_true_iff c).2
        (fun p hp => ValidatedNestedReferences.validated_type_unrolled_nested_references c p hc hp)
    have hva := ValidatedTypeChain.ValidatedTypes.append before after sts start finish hbefore hrect
    have hra := CandidateTypeReady.validated_types_ready after hva
    have hna := CandidateNestedReady.rectype_success_nestedTableReady before after sts start finish hbefore hrect
    have hpairedOld := CandidatePairedCompleteness.pairedChecks_of_success before after sts start finish hbefore hrect
    have hpairedCurrent := paired_prefix after c tail he hra hr hna before.TYPES.length
      (List.range sts.length) sts hsource hpairedOld
    have htraverse : Gen.support
        (each (SubBound (before.TYPES.length+sts.length))
          (sub c.TYPES before.TYPES.length sts.length hle) sts hb) outs := by
      simpa [group] using hg
    have hpairedNew := paired_preserved c before.TYPES.length sts.length r hle hgroup hr hn
      (List.range sts.length) sts outs hb htraverse hpairedCurrent
    obtain ⟨hlen,hbounds,htout⟩ := (group_exact_original c before.TYPES.length hle sts hb outs).1 hg
    rw [hvalue'] at htout
    have hsourceNew := group_source_valid c.TYPES before.TYPES.length hle after (extend c sts.length r)
      sts outs (extend_length c sts.length r) hb hsource hg
    have hrNew := copied_ready c before.TYPES.length sts.length r hgroup hr
    have hnNew := copied_nested c before.TYPES.length sts.length r hgroup hn
    have hresult := CandidateRectypeConstruction.rectype_success_of_checks c outs r n htout
      (by simpa [hlen,extend,defs] using hsourceNew)
      (by simpa [hlen,extend,defs] using hrNew)
      (by simpa [hlen,extend,defs] using hnNew)
      (by simpa [hlen,extend,defs] using hpairedNew)
    simpa [hlen,extend,defs] using hresult

#print axioms copy_sound
end properties.wasm_module_ok.ConstructiveTypeCopySoundness
