import properties.wasm_module_ok.ConstructiveKindShapes

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveSignaturePlan
open SpecTec properties.wasm_module_ok
open ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace ConstructiveVarianceShapes

/-- Runtime state stores raw signatures and the headers chosen before fields.
The invariant proofs are erased; no candidate validation is needed to extend it. -/
structure Signature (c : context) where
  header : Header
  shape : strtype
  valid : ValidShape c.TYPES.length shape
  agrees : kind shape = header.kind

def headers (c : context) (env : List (Signature c)) : List Header := env.map Signature.header

def parent (c : context) (env : List (Signature c)) (e : Entry)
    (he : EntryAllowed (headers c env) e) : Option {s : Signature c // s.header.kind = e.header.kind} := by
  rcases e with ⟨header,p⟩
  cases p with
  | none => exact none
  | some i =>
    have hi : i < env.length := by
      obtain ⟨old,hget,_,_⟩ := he
      simpa [headers] using (List.getElem?_eq_some_iff.mp hget).1
    have hk : env[i].header.kind = header.kind := by
      obtain ⟨old,hget,_,hk⟩ := he
      have hlookup : (headers c env)[i]? = some env[i].header := by
        simp [headers, List.getElem?_eq_getElem hi]
      have heq := Option.some.inj (hlookup.symm.trans hget)
      exact heq ▸ hk
    exact some ⟨env[i],hk⟩

def retag {c : context} {k k' : Kind} (hk : k = k')
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = k}) :
    {s : strtype // ValidShape c.TYPES.length s ∧ kind s = k'} :=
  ⟨s.val,s.property.1,s.property.2.trans hk⟩

def one (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (env : List (Signature c)) (e : Entry) (he : EntryAllowed (headers c env) e) :
    Gen {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind} :=
  match parent c env e he with
  | none => ConstructiveKindShapes.root c e.header.kind
  | some p => retag (p.val.agrees.trans p.property) <$>
      ConstructiveKindShapes.child c r hr p.val.shape p.val.valid

def Compatible (c : context) (r : heaptype → heaptype → Bool)
    (env : List (Signature c)) (e : Entry) (he : EntryAllowed (headers c env) e)
    (s : strtype) : Prop :=
  match parent c env e he with
  | none => True
  | some p => MatchStrtypeConditional.strMatch r s p.val.shape = true

theorem one_support (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (env : List (Signature c)) (e : Entry) (he : EntryAllowed (headers c env) e)
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind}) :
    Gen.support (one c r hr env e he) s ↔ Compatible c r env e he s.val := by
  cases hp : parent c env e he with
  | none =>
    simp only [one, Compatible, hp]
    exact iff_true_intro (ConstructiveKindShapes.root_covers c e.header.kind s)
  | some p =>
    simp only [one, Compatible, hp, Gen.Support.support_map]
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact (ConstructiveKindShapes.child_support c r hr p.val.shape p.val.valid t).1 ht
    · intro hs
      let t : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = kind p.val.shape} :=
        ⟨s.val,s.property.1,s.property.2.trans (p.val.agrees.trans p.property).symm⟩
      exact ⟨t,(ConstructiveKindShapes.child_support c r hr p.val.shape p.val.valid t).2 hs,rfl⟩

theorem one_audit (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (env : List (Signature c)) (e : Entry) (he : EntryAllowed (headers c env) e) :
    ConstructiveGenAudit.Structural (one c r hr env e he) := by
  unfold one
  split
  · exact ConstructiveKindShapes.root_audit c e.header.kind
  · exact ⟨ConstructiveKindShapes.child_audit _ _ _ _ _,fun _ => trivial⟩

def signature (c : context) (e : Entry)
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind}) : Signature c :=
  ⟨e.header,s.val,s.property.1,s.property.2⟩

theorem allowed_tail (c : context) (env : List (Signature c)) (e : Entry) (es : List Entry)
    (he : Allowed (headers c env) (e::es))
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind}) :
    Allowed (headers c (env ++ [signature c e s])) es := by
  simpa [headers,signature] using he.2

def fill (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (env : List (Signature c)) : (es : List Entry) →
    Allowed (headers c env) es → Gen (List SpecTec.subtype)
  | [], _ => pure []
  | e::es, he => do
    let s ← one c r hr env e he.1
    let tail ← fill c r hr (env ++ [signature c e s]) es (allowed_tail c env e es he s)
    pure (.SubT e.header.finality (ConstructiveTypeEnvironment.parentSyntax e.parent) s.val :: tail)

/-- Exact intermediate representation for the signature pass. Its matching
relation is the fixed plan; the original Rectype_ok bridge is separate. -/
def Trace (c : context) (r : heaptype → heaptype → Bool) (env : List (Signature c)) :
    (es : List Entry) → Allowed (headers c env) es → List SpecTec.subtype → Prop
  | [], _, [] => True
  | e::es, he, st::sts =>
    ∃ s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = e.header.kind},
      st = .SubT e.header.finality (ConstructiveTypeEnvironment.parentSyntax e.parent) s.val ∧
      Compatible c r env e he.1 s.val ∧
      Trace c r (env ++ [signature c e s]) es (allowed_tail c env e es he s) sts
  | _, _, _ => False

theorem fill_support (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (env : List (Signature c)) (es : List Entry) (he : Allowed (headers c env) es)
    (sts : List SpecTec.subtype) :
    Gen.support (fill c r hr env es he) sts ↔ Trace c r env es he sts := by
  induction es generalizing env sts with
  | nil => cases sts <;> simp [fill,Trace]
  | cons e es ih =>
    cases sts with
    | nil => simp [fill,Trace]
    | cons st sts =>
      simp [fill,Trace,ih,one_support,and_assoc,and_left_comm,and_comm]

theorem fill_audit (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (env : List (Signature c)) (es : List Entry) (he : Allowed (headers c env) es) :
    ConstructiveGenAudit.Structural (fill c r hr env es he) := by
  induction es generalizing env with
  | nil => trivial
  | cons e es ih =>
    exact ⟨one_audit c r hr env e he.1,fun s => ⟨ih _ _,fun _ => trivial⟩⟩

theorem fill_total (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (env : List (Signature c)) (es : List Entry) (he : Allowed (headers c env) es) :
    Gen.total (fill c r hr env es he) :=
  ConstructiveGenAudit.audit_total _ (fill_audit c r hr env es he)

end properties.wasm_module_ok.ConstructiveSignaturePlan
