import properties.wasm_module_ok.ConstructiveTypeSkeletonTrace
import properties.wasm_module_ok.ConstructiveTypeEnvironment
import properties.wasm_module_ok.ReadyHeapMatch

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveHeapPlan
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace ConstructiveTypeCopy

/-- The kind-level portion of heap subtyping has no signature dependency. -/
def kindBase (k : Kind) (target : heaptype) : Bool :=
  match k with
  | .structK => decide (target = .AnyHT ∨ target = .EqHT ∨ target = .StructHT)
  | .arrayK => decide (target = .AnyHT ∨ target = .EqHT ∨ target = .ArrayHT)
  | .funcK => decide (target = .FuncHT)

def baseKind (source : heaptype) (k : Kind) : Bool :=
  match source with
  | .NoneHT => kindBase k .AnyHT
  | .NoFuncHT => kindBase k .FuncHT
  | .NoExnHT => kindBase k .ExnHT
  | .NoExternHT => kindBase k .ExternHT
  | .BotHT => true
  | _ => false

/-- Used to select legal atomic references before generating signature fields.
The inputs are the preselected kind and parent graph, not a candidate AST. -/
def heap (kinds : Nat → Kind) (indices : Nat → Nat → Bool) : heaptype → heaptype → Bool
  | .VarHT (.StatX p), .VarHT (.StatX q) => indices p q
  | .VarHT (.StatX p), b => kindBase (kinds p) b
  | a, .VarHT (.StatX q) => baseKind a (kinds q)
  | a, b => ReadyHeapMatchBase.baseMatch a b

def TracksKinds (c : context) (kinds : Nat → Kind) : Prop :=
  ∀ p dt, c.TYPES[p]? = some dt → ∃ f ps st,
    unrollDeftypeResult dt = some (.SubT f ps st) ∧ kind st = kinds p

theorem kind_base_correct (dt : deftype) (f : final) (ps : List heaptype)
    (st : strtype) (hu : unrollDeftypeResult dt = some (.SubT f ps st)) (b : heaptype) :
    ReadyHeapMatchDefBase.readyDefBaseMatch dt b = kindBase (kind st) b := by
  cases b <;> cases st <;>
    simp only [ReadyHeapMatchDefBase.readyDefBaseMatch, MatchReadyDefFixed.anyBaseMatch,
      MatchReadyDefFixed.eqBaseMatch, MatchReadyDefFixed.structBaseMatch,
      MatchReadyDefFixed.arrayBaseMatch, MatchReadyDefFixed.funcBaseMatch,
      UnrollInterface.expandResult, hu] <;> rfl

theorem base_kind_correct (dt : deftype) (f : final) (ps : List heaptype)
    (st : strtype) (hu : unrollDeftypeResult dt = some (.SubT f ps st))
    (b : heaptype) (hb : Base b) :
    (ReadyHeapMatch.baseIndexedMatch b dt).getD false = baseKind b (kind st) := by
  cases b <;> simp_all only [Base, not_false_eq_true]
  all_goals simp only [ReadyHeapMatch.baseIndexedMatch,
    ReadyHeapMatchSpecialIndexed.specialBaseSources, MatchBaseDefTotal.simpleBaseHeaptypes,
    List.mem_cons, List.mem_singleton, reduceCtorEq, or_true, true_or, or_self,
    ↓reduceIte, Option.getD_some, ReadyHeapMatchSpecialIndexed.specialBaseMatch,
    kind_base_correct dt f ps st hu, ReadyHeapMatchSimpleBase.simpleBaseMatch, baseKind]
  all_goals rfl

theorem base_mem (b : heaptype) (hb : Base b) : b ∈ HeaptypeValidation.baseHeaptypes := by
  cases b <;> simp_all [Base, HeaptypeValidation.baseHeaptypes]

theorem heap_base_base (k : Nat → Kind) (r : Nat → Nat → Bool)
    (a b : heaptype) (ha : Base a) (hb : Base b) :
    heap k r a b = ReadyHeapMatchBase.baseMatch a b := by
  cases a <;> cases b <;> simp_all [Base, heap]

theorem heap_base_stat (k : Nat → Kind) (r : Nat → Nat → Bool)
    (a : heaptype) (ha : Base a) (q : Nat) :
    heap k r a (.VarHT (.StatX q)) = baseKind a (k q) := by
  cases a <;> simp_all [Base, heap]

theorem heap_stat_base (k : Nat → Kind) (r : Nat → Nat → Bool)
    (b : heaptype) (hb : Base b) (p : Nat) :
    heap k r (.VarHT (.StatX p)) b = kindBase (k p) b := by
  cases b <;> simp_all [Base, heap]

theorem heap_sound (c : context) (k : Nat → Kind) (r : Nat → Nat → Bool)
    (hk : TracksKinds c k)
    (hr : ∀ p q, p < c.TYPES.length → q < c.TYPES.length →
      r p q = true → ValidatedMatchIndexFuel.matchIndex c p q = true)
    (a b : heaptype) (ha : HeapBound c.TYPES.length a) (hb : HeapBound c.TYPES.length b) :
    heap k r a b = true → (ReadyHeapMatch.readyHeapMatch c a b).getD false = true := by
  rcases raw_cases _ a ha with ha | ⟨p,rfl,hp⟩
  · rcases raw_cases _ b hb with hb | ⟨q,rfl,hq⟩
    · rw [heap_base_base k r a b ha hb,
        ReadyHeapMatch.readyHeapMatch_base_base c a b (base_mem a ha) (base_mem b hb)]
      exact id
    · obtain ⟨f,ps,st,hu,hkind⟩ := hk q c.TYPES[q] (List.getElem?_eq_getElem hq)
      rw [heap_base_stat k r a ha q,
        ReadyHeapMatch.readyHeapMatch_base_statx c q c.TYPES[q] a
          (List.getElem?_eq_getElem hq) (base_mem a ha)]
      simpa only [Option.getD_some, base_kind_correct _ f ps st hu a ha, hkind] using
        (id : baseKind a (k q) = true → baseKind a (k q) = true)
  · rcases raw_cases _ b hb with hb | ⟨q,rfl,hq⟩
    · obtain ⟨f,ps,st,hu,hkind⟩ := hk p c.TYPES[p] (List.getElem?_eq_getElem hp)
      rw [heap_stat_base k r b hb p,
        ReadyHeapMatch.readyHeapMatch_statx_base c p c.TYPES[p] b
          (List.getElem?_eq_getElem hp) (base_mem b hb)]
      simpa only [Option.getD_some, kind_base_correct _ f ps st hu b, hkind] using
        (id : kindBase (k p) b = true → kindBase (k p) b = true)
    · rw [ReadyHeapMatch.readyHeapMatch_statx_statx]
      exact hr p q hp hq

theorem heap_exact (c : context) (k : Nat → Kind) (r : Nat → Nat → Bool)
    (hk : TracksKinds c k)
    (hr : ∀ p q, p < c.TYPES.length → q < c.TYPES.length →
      r p q = ValidatedMatchIndexFuel.matchIndex c p q)
    (a b : heaptype) (ha : HeapBound c.TYPES.length a) (hb : HeapBound c.TYPES.length b) :
    heap k r a b = (ReadyHeapMatch.readyHeapMatch c a b).getD false := by
  rcases raw_cases _ a ha with ha | ⟨p,rfl,hp⟩
  · rcases raw_cases _ b hb with hb | ⟨q,rfl,hq⟩
    · rw [heap_base_base k r a b ha hb,
        ReadyHeapMatch.readyHeapMatch_base_base c a b (base_mem a ha) (base_mem b hb)]
      rfl
    · obtain ⟨f,ps,st,hu,hkind⟩ := hk q c.TYPES[q] (List.getElem?_eq_getElem hq)
      rw [heap_base_stat k r a ha q,
        ReadyHeapMatch.readyHeapMatch_base_statx c q c.TYPES[q] a
          (List.getElem?_eq_getElem hq) (base_mem a ha)]
      simp only [Option.getD_some, base_kind_correct _ f ps st hu a ha, hkind]
  · rcases raw_cases _ b hb with hb | ⟨q,rfl,hq⟩
    · obtain ⟨f,ps,st,hu,hkind⟩ := hk p c.TYPES[p] (List.getElem?_eq_getElem hp)
      rw [heap_stat_base k r b hb p,
        ReadyHeapMatch.readyHeapMatch_statx_base c p c.TYPES[p] b
          (List.getElem?_eq_getElem hp) (base_mem b hb)]
      simp only [Option.getD_some, kind_base_correct _ f ps st hu b, hkind]
    · rw [ReadyHeapMatch.readyHeapMatch_statx_statx]
      exact hr p q hp hq

theorem heap_refl (bound : Nat) (k : Nat → Kind) (r : Nat → Nat → Bool)
    (hr : ∀ p, p < bound → r p p = true) (a : heaptype) (ha : HeapBound bound a) :
    heap k r a a = true := by
  rcases raw_cases bound a ha with ha | ⟨p,rfl,hp⟩
  · rw [heap_base_base k r a a ha ha]
    cases a <;> simp_all [Base, ReadyHeapMatchBase.baseMatch, ReadyHeapMatchBase.baseMatchFuel,
      ReadyHeapMatchSimpleBase.simpleBaseMatch]
  · exact hr p hp

end properties.wasm_module_ok.ConstructiveHeapPlan
