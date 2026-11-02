import properties.wasm_module_ok.ConstructiveFreshCompleteness
import properties.wasm_module_ok.ConstructiveTypeCopyCompleteness

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeHistory
open SpecTec properties.wasm_module_ok
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveSignaturePlan
open ConstructiveSignatureState ConstructiveTypeSkeletonTrace

/-- Only base and raw source group are runtime data. Provenance records an
earlier successful group; it is not a test of a newly generated candidate. -/
structure Stored (c : context) where
  base : Nat
  source : List SpecTec.subtype
  within : base ≤ c.TYPES.length
  bound : GroupBound (base+source.length) source
  provenance : ∃ before after : context, ∃ start finish : Nat, ∃ tail : List deftype,
    ValidatedTypeChain.ValidatedTypes before ∧
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok before (.RecT source)⟩)
      start (.success (.of after)) finish ∧
    c.TYPES = after.TYPES ++ tail ∧ base = before.TYPES.length

def closed (c : context) (s : Stored c) : rectype :=
  groupValue c.TYPES s.base s.within s.source s.bound

def copy (c : context) (s : Stored c) : Gen rectype :=
  group c.TYPES s.base s.within s.source s.bound

theorem copy_audit (c : context) (s : Stored c) : ConstructiveGenAudit.Structural (copy c s) :=
  ConstructiveGenAudit.finite_audit _ (group_finite c.TYPES s.base s.within s.source s.bound)

theorem copy_sound (c : context) (hc : ValidatedTypeChain.ValidatedTypes c)
    (s : Stored c) (rt : rectype) (hg : Gen.support (copy c s) rt) (n : Nat) :
    ∃ out : context, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c rt⟩) n (.success (.of out)) n := by
  obtain ⟨before,after,start,finish,tail,hbefore,hrect,he,hbase⟩ := s.provenance
  cases rt with
  | RecT outs =>
    have hle : before.TYPES.length ≤ c.TYPES.length := hbase ▸ s.within
    have hb : GroupBound (before.TYPES.length+s.source.length) s.source := hbase ▸ s.bound
    exact ⟨_,ConstructiveTypeCopySoundness.copy_sound before after c s.source outs start finish n tail
      hbefore hc hrect he hle hb (by simpa only [copy,hbase] using hg)⟩

theorem copy_complete (c result : context) (s : Stored c) (outs : List SpecTec.subtype)
    (start finish : Nat)
    (hout : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT outs)⟩)
      start (.success (.of result)) finish)
    (hclosed : CandidateRectypeTable.transformed c outs = some (closed c s)) :
    Gen.support (copy c s) (.RecT outs) := by
  obtain ⟨before,after,oldStart,oldFinish,tail,hbefore,hrect,he,hbase⟩ := s.provenance
  have hle : before.TYPES.length ≤ c.TYPES.length := hbase ▸ s.within
  have hb : GroupBound (before.TYPES.length+s.source.length) s.source := hbase ▸ s.bound
  have hold := ConstructiveTypeCopyCompleteness.stored_closure before after c s.source
    oldStart oldFinish tail hrect he hle hb
  have hsame : CandidateRectypeTable.transformed c outs = CandidateRectypeTable.transformed before s.source := by
    rw [hold]
    simpa only [closed,hbase] using hclosed
  have hg := ConstructiveTypeCopyCompleteness.copy_complete before after c result s.source outs
    oldStart oldFinish start finish tail hrect he hle hb hout hsame
  simpa only [copy,hbase] using hg

/-- Every old definition has a stored source group. The union proof uses this
history only to cover whole-group equality; runtime never tests freshness. -/
def Covers (c : context) (history : List (Stored c)) : Prop :=
  ∀ (p : Nat) (dt : deftype), c.TYPES[p]? = some dt →
    ∃ s ∈ history, ∃ i : Nat, dt = .DefT (closed c s) i

def groups (c : context) (env : List (Signature c)) (history : List (Stored c)) : Gen rectype :=
  match history with
  | [] => ConstructiveFreshSignatures.fresh c env
  | s::ss => Gen.pick (ConstructiveFreshSignatures.fresh c env)
      (ConstructiveTypeAtoms.choose s ss >>= copy c)

theorem groups_support (c : context) (env : List (Signature c)) (history : List (Stored c)) (rt : rectype) :
    Gen.support (groups c env history) rt ↔
      Gen.support (ConstructiveFreshSignatures.fresh c env) rt ∨
        ∃ s ∈ history, Gen.support (copy c s) rt := by
  cases history <;> simp [groups]

theorem groups_audit (c : context) (env : List (Signature c)) (history : List (Stored c)) :
    ConstructiveGenAudit.Structural (groups c env history) := by
  cases history with
  | nil => exact ConstructiveFreshSignatures.fresh_audit c env
  | cons s ss =>
    exact ⟨ConstructiveFreshSignatures.fresh_audit c env,
      ConstructiveGenAudit.finite_audit _ (ConstructiveTypeAtoms.finite_choose s ss),copy_audit c⟩

theorem groups_sound (c : context) (env : List (Signature c)) (history : List (Stored c))
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hmeta : Tracks c (headers c env)) (hdenote : Describes c c env)
    (rt : rectype) (hg : Gen.support (groups c env history) rt) (n : Nat) :
    ∃ out : context, SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c rt⟩) n (.success (.of out)) n := by
  rcases (groups_support c env history rt).1 hg with hf | ⟨s,_,hs⟩
  · exact ConstructiveFreshSoundness.fresh_sound c env (CandidateTypeReady.validated_types_ready c hc)
      ((CandidateNestedReady.nestedTableReady_true_iff c).2
        (fun p hp => ValidatedNestedReferences.validated_type_unrolled_nested_references c p hc hp))
      hmeta hdenote rt hf n
  · exact copy_sound c hc s rt hs n

/-- Full original recursive-group coverage, including equality-essential
groups and every raw alias. The fresh/copy case split is proof-only. -/
theorem groups_complete (c result : context) (env : List (Signature c)) (history : List (Stored c))
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hmeta : Tracks c (headers c env)) (hdenote : Describes c c env) (hhistory : Covers c history)
    (sts : List SpecTec.subtype) (start finish : Nat)
    (hout : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) : Gen.support (groups c env history) (.RecT sts) := by
  classical
  have hb := ConstructiveTypeCopySource.original_bound c result sts start finish hout
  let rt := groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts hb
  apply (groups_support c env history _).2
  by_cases hfresh : ∀ p i : Nat, c.TYPES[p]? ≠ some (.DefT rt i)
  · exact Or.inl (ConstructiveFreshCompleteness.fresh_complete c result env hc hmeta hdenote
      sts start finish hout hb hfresh)
  · push Not at hfresh
    obtain ⟨p,i,hget⟩ := hfresh
    obtain ⟨s,hs,j,heq⟩ := hhistory p (.DefT rt i) hget
    have heq' : rt = closed c s := (deftype.DefT.inj heq).1
    have htrans : CandidateRectypeTable.transformed c sts = some (closed c s) := by
      rw [← heq']
      simpa [CandidateRectypeTable.transformed,Nat.add_comm,rt] using
        group_value_correct c.TYPES c.TYPES.length (Nat.le_refl _) sts hb
    exact Or.inr ⟨s,hs,copy_complete c result s sts start finish hout htrans⟩

end properties.wasm_module_ok.ConstructiveTypeHistory
