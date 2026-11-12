import properties.wasm_module_ok.ConstructiveSignaturePlan
import properties.wasm_module_ok.ConstructiveTypeCopySource

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveSignatureTrace
open SpecTec properties.wasm_module_ok
open ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace ConstructiveVarianceShapes
open ConstructiveSignaturePlan ConstructiveTypeEnvironment

theorem parent_bound (c : context) (env : List (Signature c)) (e : Entry)
    (he : EntryAllowed (headers c env) e) (i : Nat) (hp : e.parent = some i) : i < env.length := by
  simp only [EntryAllowed, hp] at he
  obtain ⟨h,hget,_,_⟩ := he
  simpa [headers] using (List.getElem?_eq_some_iff.mp hget).1

theorem source_entry (c : context) (env : List (Signature c)) (e : Entry)
    (he : EntryAllowed (headers c env) e) (hcap : env.length ≤ c.TYPES.length)
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind}) :
    SubtypeValidation.subtypeValid c (.SubT e.header.finality (parentSyntax e.parent) s.val) = true := by
  have hv := (valid_shape_iff c s.val).1 s.property.1
  cases hp : e.parent with
  | none => simp [SubtypeValidation.subtypeValid,parentSyntax,hp,SubtypeHeadListValidation.allHeaptypesValid,hv]
  | some i =>
    have hi := Nat.lt_of_lt_of_le (parent_bound c env e he i hp) hcap
    simp [SubtypeValidation.subtypeValid,parentSyntax,hp,SubtypeHeadListValidation.allHeaptypesValid,
      HeaptypeValidation.heaptypeValid,hi,hv]

theorem entry_header (c : context) (e : Entry)
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind}) :
    header (.SubT e.header.finality (parentSyntax e.parent) s.val) = e.header := by
  have hk := s.property.2
  cases e with
  | mk h p => cases h; simp_all [header]

/-- The signature pass retains every chosen parent/header and produces actual
first-pass source validity. No completed candidate is checked at runtime. -/
theorem facts (c : context) (r : heaptype → heaptype → Bool)
    (env : List (Signature c)) (es : List Entry) (he : Allowed (headers c env) es)
    (sts : List SpecTec.subtype) (ht : Trace c r env es he sts)
    (hcap : env.length+es.length ≤ c.TYPES.length) :
    sts.length = es.length ∧ sts.map header = es.map Entry.header ∧
      CandidateSourceChecks.sourceChecks c sts = true := by
  induction es generalizing env sts with
  | nil => cases sts <;> simp_all [Trace,CandidateSourceChecks.sourceChecks]
  | cons e es ih =>
    cases sts with
    | nil => cases ht
    | cons st sts =>
      obtain ⟨s,rfl,_,htail⟩ := ht
      have htailCap : (env ++ [signature c e s]).length+es.length ≤ c.TYPES.length := by
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap
      obtain ⟨hlen,hmeta,hvalid⟩ := ih _ _ _ htail htailCap
      have hsource := source_entry c env e he.1 (by omega) s
      exact ⟨by simpa using hlen,by simp [entry_header,hmeta],by
        simp [CandidateSourceChecks.sourceChecks,hsource,hvalid]⟩

theorem layout (c : context) (r : heaptype → heaptype → Bool)
    (env : List (Signature c)) (es : List Entry) (he : Allowed (headers c env) es)
    (sts : List SpecTec.subtype) (ht : Trace c r env es he sts) :
    ParentLayout env.length sts (es.map Entry.parent) := by
  induction es generalizing env sts with
  | nil =>
    cases sts with
    | nil => simp [ParentLayout]
    | cons st sts => cases ht
  | cons e es ih =>
    cases sts with
    | nil => cases ht
    | cons st sts =>
      obtain ⟨s,rfl,_,htail⟩ := ht
      have ih' := ih _ _ _ htail
      constructor
      · simpa using congrArg Nat.succ ih'.1
      · intro i p hp
        cases i with
        | zero =>
          have hep : e.parent = p := by simpa using hp
          subst p
          refine ⟨e.header.finality,s.val,rfl,?_⟩
          intro k hk
          simpa using parent_bound c env e he.1 k hk
        | succ i =>
          have hp' : (es.map Entry.parent)[i]? = some p := by simpa using hp
          obtain ⟨f,t,hget,hbefore⟩ := ih'.2 i p hp'
          refine ⟨f,t,by simpa using hget,?_⟩
          intro k hk
          have hkb := hbefore k hk
          simpa [List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hkb

theorem bound (c : context) (r : heaptype → heaptype → Bool)
    (env : List (Signature c)) (es : List Entry) (he : Allowed (headers c env) es)
    (sts : List SpecTec.subtype) (ht : Trace c r env es he sts)
    (hcap : env.length+es.length ≤ c.TYPES.length) :
    ConstructiveTypeCopy.GroupBound c.TYPES.length sts :=
  ConstructiveTypeCopySource.group_bound c sts (facts c r env es he sts ht hcap).2.2

end properties.wasm_module_ok.ConstructiveSignatureTrace
