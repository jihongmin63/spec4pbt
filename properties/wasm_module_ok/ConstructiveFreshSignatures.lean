import properties.wasm_module_ok.ConstructiveSignatureTrace
import properties.wasm_module_ok.ConstructiveTypeMetadata

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveFreshSignatures
open SpecTec properties.wasm_module_ok
open ConstructiveTypeSkeleton ConstructiveSignaturePlan ConstructiveVarianceAtoms ConstructiveVarianceShapes

theorem heap_weaken (a b : Nat) (hab : a ≤ b) (h : heaptype)
    (hh : ConstructiveTypeCopy.HeapBound a h) : ConstructiveTypeCopy.HeapBound b h := by
  cases h <;> try trivial
  case VarHT v =>
    cases v with
    | StatX i => exact Nat.lt_of_lt_of_le hh hab
    | RecX i => exact False.elim hh

theorem val_weaken (a b : Nat) (hab : a ≤ b) (v : valtype) (hv : ValidVal a v) : ValidVal b v := by
  cases v <;> try trivial
  case RefT r => cases r; exact heap_weaken a b hab _ hv

theorem storage_weaken (a b : Nat) (hab : a ≤ b) (s : storagetype)
    (hs : ValidStorage a s) : ValidStorage b s := by
  cases s with
  | ValStorageT v => exact val_weaken a b hab v hs
  | PackStorageT p => exact hs

theorem field_weaken (a b : Nat) (hab : a ≤ b) (f : fieldtype)
    (hf : ValidField a f) : ValidField b f := by
  cases f; exact storage_weaken a b hab _ hf

theorem shape_weaken (a b : Nat) (hab : a ≤ b) (s : strtype)
    (hs : ValidShape a s) : ValidShape b s := by
  cases s with
  | DefStructT s => cases s; exact fun f hf => field_weaken a b hab f (hs f hf)
  | DefArrayT s => cases s; exact field_weaken a b hab _ hs
  | DefFuncT s => cases s; exact ⟨fun v hv => val_weaken a b hab v (hs.1 v hv),
      fun v hv => val_weaken a b hab v (hs.2 v hv)⟩

/-- Preallocate only the cardinality used by raw source type constructors.
No type matcher reads these slots; matching uses the old table and chosen graph.
Actual definitions are formed by structural closure after signatures are built. -/
def capacity (c : context) (count : Nat) : context :=
  {c with TYPES := c.TYPES ++ List.replicate count (.DefT (.RecT []) 0)}

@[simp] theorem capacity_length (c : context) (n : Nat) :
    (capacity c n).TYPES.length = c.TYPES.length+n := by simp [capacity]

def liftSignature (c : context) (n : Nat) (s : Signature c) : Signature (capacity c n) :=
  ⟨s.header,s.shape,shape_weaken _ _ (by simp) s.shape s.valid,s.agrees⟩

def liftEnv (c : context) (n : Nat) (env : List (Signature c)) : List (Signature (capacity c n)) :=
  env.map (liftSignature c n)

@[simp] theorem lift_headers (c : context) (n : Nat) (env : List (Signature c)) :
    headers (capacity c n) (liftEnv c n env) = headers c env := by
  simp [headers,liftEnv,liftSignature,List.map_map,Function.comp_def]

def relation (c : context) (hs : List Header) (es : List Entry) : heaptype → heaptype → Bool :=
  ConstructiveHeapPlan.heap (ConstructiveTypeMetadata.kindAt (hs ++ es.map Entry.header))
    (ConstructiveNominalPlan.matchPlanned (ValidatedMatchIndexFuel.matchIndex c)
      c.TYPES.length (es.map Entry.parent))

theorem planned_refl (c : context) (ps : List (Option Nat)) (p : Nat) :
    ConstructiveNominalPlan.matchPlanned (ValidatedMatchIndexFuel.matchIndex c)
      c.TYPES.length ps p p = true := by
  by_cases hp : p < c.TYPES.length
  · simp [ConstructiveNominalPlan.matchPlanned,ConstructiveNominalPlan.fuel,hp,
      ValidatedMatchIndexFuel.matchIndex,ValidatedMatchIndexFuel.matchIndexFuel,
      List.getElem?_eq_getElem hp]
  · simp [ConstructiveNominalPlan.matchPlanned,ConstructiveNominalPlan.fuel,hp]

theorem relation_refl (c : context) (hs : List Header) (es : List Entry) :
    ∀ h, ConstructiveTypeCopy.HeapBound (capacity c es.length).TYPES.length h →
      relation c hs es h h = true :=
  ConstructiveHeapPlan.heap_refl _ _ _ (fun p _ => planned_refl c _ p)

def plan (c : context) (env : List (Signature c)) :
    Gen {es : List Entry // Allowed (headers c env) es} :=
  ConstructiveAttach.refine (skeleton (headers c env)) (skeleton_audit _) _
    (fun es hes => (skeleton_support _ es).1 hes)

theorem plan_covers (c : context) (env : List (Signature c))
    (es : {es : List Entry // Allowed (headers c env) es}) : Gen.support (plan c env) es := by
  rw [plan,ConstructiveAttach.refine_support,skeleton_support]
  exact es.property

theorem plan_audit (c : context) (env : List (Signature c)) : ConstructiveGenAudit.Structural (plan c env) :=
  ConstructiveAttach.refine_audit _ _ _ _

def signatures (c : context) (env : List (Signature c))
    (es : List Entry) (he : Allowed (headers c env) es) : Gen (List SpecTec.subtype) :=
  fill (capacity c es.length) (relation c (headers c env) es) (relation_refl c _ es)
    (liftEnv c es.length env) es (by simpa using he)

/-- Arbitrary finite group size, parent forest and fields. This component is
still connected to original Rectype_ok by separate forward/backward proofs. -/
def fresh (c : context) (env : List (Signature c)) : Gen rectype := do
  let es ← plan c env
  rectype.RecT <$> signatures c env es.val es.property

theorem signatures_audit (c : context) (env : List (Signature c))
    (es : List Entry) (he : Allowed (headers c env) es) :
    ConstructiveGenAudit.Structural (signatures c env es he) := fill_audit _ _ _ _ _ _

theorem fresh_audit (c : context) (env : List (Signature c)) :
    ConstructiveGenAudit.Structural (fresh c env) :=
  ⟨plan_audit c env,fun es => ⟨signatures_audit c env es.val es.property,fun _ => trivial⟩⟩

theorem fresh_total (c : context) (env : List (Signature c)) : Gen.total (fresh c env) :=
  ConstructiveGenAudit.audit_total _ (fresh_audit c env)

theorem fresh_covers (c : context) (env : List (Signature c))
    (es : List Entry) (he : Allowed (headers c env) es) (sts : List SpecTec.subtype)
    (hs : Gen.support (signatures c env es he) sts) : Gen.support (fresh c env) (.RecT sts) :=
  ⟨⟨es,he⟩,plan_covers c env ⟨es,he⟩,sts,hs,rfl⟩

end properties.wasm_module_ok.ConstructiveFreshSignatures
