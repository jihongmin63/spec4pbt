import properties.wasm_module_ok.ConstructiveTypeCopySoundness
import properties.wasm_module_ok.SubstRectypeLength
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyCompleteness
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveTypeCopyExact ConstructiveTypeCopySource
open properties.wasm_module_ok.ConstructiveTypeCopyRealization

/-- The total stored-group closure agrees with its original successful
transformation after arbitrary later groups have extended the prefix. -/
theorem stored_closure (before after c : context) (sts : List SpecTec.subtype)
    (start finish : Nat) (tail : List deftype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (he : c.TYPES=after.TYPES++tail)
    (hle : before.TYPES.length≤c.TYPES.length)
    (hb : GroupBound (before.TYPES.length+sts.length) sts) :
    CandidateRectypeTable.transformed before sts=
      some (groupValue c.TYPES before.TYPES.length hle sts hb) := by
  have hcandidate := CandidateRectypeTable.rectype_success_candidateContext before after sts start finish hrect
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
    have hv := group_value_correct c.TYPES before.TYPES.length hle sts hb
    exact ht'.symm.trans (by simpa only [Nat.add_comm] using hv)

/-- Backward coverage for the complete same-closed-group class of original
valid ASTs. No normalized syntax or chosen representative is imposed. -/
theorem copy_complete (before after c result : context) (sts outs : List SpecTec.subtype)
    (start finish newStart newFinish : Nat) (tail : List deftype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (he : c.TYPES=after.TYPES++tail)
    (hle : before.TYPES.length≤c.TYPES.length)
    (hb : GroupBound (before.TYPES.length+sts.length) sts)
    (hout : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Rectype_ok c (.RecT outs)⟩)
      newStart (.success (.of result)) newFinish)
    (hsame : CandidateRectypeTable.transformed c outs=CandidateRectypeTable.transformed before sts) :
    Gen.support (group c.TYPES before.TYPES.length hle sts hb) (.RecT outs) := by
  have htrans := hsame.trans (stored_closure before after c sts start finish tail hrect he hle hb)
  have hbout := original_bound c result outs newStart newFinish hout
  obtain ⟨closed,hclosed,hlen⟩ := SubstRectypeLength.substRectypeResult_length
    (rollSubtypes outs c.TYPES.length (outs.length+c.TYPES.length)) c.TYPES
    (groupValue c.TYPES before.TYPES.length hle sts hb) htrans
  have hclosed' : closed.length=sts.length := by
    have hEq := rectype.RecT.inj hclosed
    have hLen := congrArg List.length hEq
    simpa [groupValue] using hLen.symm
  have hlen' : outs.length=sts.length := by
    simpa [rollSubtypes] using hlen.symm.trans hclosed'
  exact (group_exact_original c before.TYPES.length hle sts hb outs).2 ⟨hlen',hbout,htrans⟩

#print axioms copy_complete
end properties.wasm_module_ok.ConstructiveTypeCopyCompleteness
