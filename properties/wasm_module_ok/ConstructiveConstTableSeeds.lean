import properties.wasm_module_ok.ConstructiveConstTableCore
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTableSeeds
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstLiteralGen

def literalEntries (c : context) (hp : CandidateUniverseReady.Provenance c) : List (Entry c) :=
  [entry c hp (.NumT .I32T) (number c (.I32 0)) ⟨numbers c .I32T,numbers_audit c .I32T⟩,
   entry c hp (.NumT .I64T) (number c (.I64 0)) ⟨numbers c .I64T,numbers_audit c .I64T⟩,
   entry c hp (.NumT .F32T) (number c (.F32 (.POS .INF))) ⟨numbers c .F32T,numbers_audit c .F32T⟩,
   entry c hp (.NumT .F64T) (number c (.F64 (.POS .INF))) ⟨numbers c .F64T,numbers_audit c .F64T⟩,
   entry c hp (.VecT .V128T) (vector c (.V128 0)) ⟨vectors c,vectors_audit c⟩]

def nullEntries (c : context) (hp : CandidateUniverseReady.Provenance c) : List (Entry c) :=
  (FiniteValidTypes.heapCandidates c).attach.map fun ht =>
    let t := nullRef c ht.val ((FiniteValidTypes.heapCandidates_spec c ht.val).1 ht.property)
    entry c hp _ t (Audited.pure t)

def functionEntries (c : context) (hp : CandidateUniverseReady.Provenance c) : List (Entry c) :=
  (List.finRange c.FUNCS.length).flatMap fun x =>
    if href : ConstRefFuncProduction.hasFuncBool c.REFS x.val=true then
      let t := funcRef c x.val c.FUNCS[x.val]
        (by simp) ((ConstRefFuncProduction.has_func_bool_iff c.REFS x.val).1 href)
      [entry c hp _ t (Audited.pure t)]
    else []

def globalEntries (c : context) (hp : CandidateUniverseReady.Provenance c) : List (Entry c) :=
  (List.finRange c.GLOBALS.length).flatMap fun x =>
    match hg : c.GLOBALS[x.val] with
    | .GlobalT .Cons u =>
      let t := global c x.val u (by simpa [hg] using (List.getElem?_eq_getElem (as:=c.GLOBALS) x.isLt))
      [entry c hp _ t (Audited.pure t)]
    | .GlobalT .Var _ => []

/-- Only the already validated type table is inspected to form bounded indices.
No expression is constructed until its type constructor is known. -/
def structIndices (c : context) : List (StructIndex c) :=
  (List.finRange c.TYPES.length).flatMap fun x =>
    match he : UnrollInterface.expandResult c.TYPES[x.val] with
    | some (.DefStructT (.StructT fields)) => [⟨x.val,c.TYPES[x.val],fields,by simp,he⟩]
    | _ => []

def arrayIndices (c : context) : List (ArrayIndex c) :=
  (List.finRange c.TYPES.length).flatMap fun x =>
    match he : UnrollInterface.expandResult c.TYPES[x.val] with
    | some (.DefArrayT (.ArrayT field)) => [⟨x.val,c.TYPES[x.val],field,by simp,he⟩]
    | _ => []

def implicitStructEntries (c : context) (hp : CandidateUniverseReady.Provenance c) : List (Entry c) :=
  (structIndices c).flatMap fun index =>
    if hd : StructImplicitFieldsDecision.structFieldsDefaultable index.fields=true then
      let t := structImplicit c index hd
      [entry c hp _ t (Audited.pure t)]
    else []

def emptyArrayEntries (c : context) (hp : CandidateUniverseReady.Provenance c) : List (Entry c) :=
  (arrayIndices c).map fun index =>
    let t := arrayFixed c index 0 (emptyOperands c)
    entry c hp _ t (Audited.pure t)

def seeds (c : context) (hp : CandidateUniverseReady.Provenance c) : List (Entry c) :=
  literalEntries c hp ++ nullEntries c hp ++ functionEntries c hp ++ globalEntries c hp ++
    implicitStructEntries c hp ++ emptyArrayEntries c hp

theorem seeds_nonempty (c : context) (hp : CandidateUniverseReady.Provenance c) : seeds c hp≠[] := by
  simp [seeds,literalEntries]

end properties.wasm_module_ok.ConstructiveConstTableSeeds
