import properties.wasm_module_ok.ConstructiveTypeCopyReady
import properties.wasm_module_ok.ConstructiveNominalMatch
import properties.wasm_module_ok.ReadyHeapMatch
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyHeapMatch
open SpecTec properties.wasm_module_ok
open ReadyHeapMatch

/-- A heap reference and its actual closed meaning in the current table. -/
inductive Resolves (c : context) : heaptype → heaptype → Prop
  | base (h : heaptype) (hb : h∈HeaptypeValidation.baseHeaptypes) : Resolves c h h
  | stat (p : Nat) (dt : deftype) (hp : c.TYPES[p]?=some dt) :
      Resolves c (.VarHT (.StatX p)) (.DefHT dt)
  | closed (p : Nat) (dt : deftype) (hp : c.TYPES[p]?=some dt) :
      Resolves c (.DefHT dt) (.DefHT dt)

def Canonical (c : context) (h : heaptype) : Prop :=
  h∈HeaptypeValidation.baseHeaptypes ∨ ∃ (p : Nat) (dt : deftype),c.TYPES[p]?=some dt ∧ h=.DefHT dt

theorem resolves_canonical (c : context) (a b : heaptype) (h : Resolves c a b) : Canonical c b := by
  cases h with
  | base h hb => exact .inl hb
  | stat p dt hp => exact .inr ⟨p,dt,hp,rfl⟩
  | closed p dt hp => exact .inr ⟨p,dt,hp,rfl⟩

theorem normalize (c : context) (hr : CandidateTypeReady.Ready c)
    (a b a' b' : heaptype) (ha : Resolves c a a') (hb : Resolves c b b') :
    readyHeapMatch c a b = readyHeapMatch c a' b' := by
  cases ha with
  | base a ha =>
    cases hb with
    | base b hb => rfl
    | stat q dt hq => rw [readyHeapMatch_base_statx c q dt a hq ha,readyHeapMatch_base_def c q dt a hq ha]
    | closed q dt hq => rfl
  | stat p dtP hp =>
    have hpb := (List.getElem?_eq_some_iff.1 hp).1
    cases hb with
    | base b hb => rw [readyHeapMatch_statx_base c p dtP b hp hb,readyHeapMatch_def_base c p dtP b hp hb]
    | stat q dtQ hq =>
      have hqb := (List.getElem?_eq_some_iff.1 hq).1
      rw [readyHeapMatch_statx_statx c p q,readyHeapMatch_def_def c p q 0 dtP dtQ hr hpb hqb hp hq]
    | closed q dtQ hq =>
      have hqb := (List.getElem?_eq_some_iff.1 hq).1
      rw [readyHeapMatch_statx_def c p q 0 dtP dtQ hr hpb hqb hp hq,
        readyHeapMatch_def_def c p q 0 dtP dtQ hr hpb hqb hp hq]
  | closed p dtP hp =>
    have hpb := (List.getElem?_eq_some_iff.1 hp).1
    cases hb with
    | base b hb => rfl
    | stat q dtQ hq =>
      have hqb := (List.getElem?_eq_some_iff.1 hq).1
      rw [readyHeapMatch_def_statx c p q 0 dtP dtQ hr hpb hqb hp hq,
        readyHeapMatch_def_def c p q 0 dtP dtQ hr hpb hqb hp hq]
    | closed q dtQ hq => rfl

theorem canonical_prefix (c d : context) (tail : List deftype)
    (he : d.TYPES=c.TYPES++tail)
    (hc : CandidateTypeReady.Ready c) (hd : CandidateTypeReady.Ready d)
    (a b : heaptype) (ha : Canonical c a) (hb : Canonical c b) :
    readyHeapMatch d a b=readyHeapMatch c a b := by
  have lookup : ∀ (p : Nat) (dt : deftype),c.TYPES[p]?=some dt → d.TYPES[p]?=some dt := by
    intro p dt hp
    rw [he,List.getElem?_append_left (List.getElem?_eq_some_iff.1 hp).1]
    exact hp
  rcases ha with ha | ⟨p,dtP,hp,rfl⟩
  · rcases hb with hb | ⟨q,dtQ,hq,rfl⟩
    · rw [readyHeapMatch_base_base d a b ha hb,readyHeapMatch_base_base c a b ha hb]
    · rw [readyHeapMatch_base_def d q dtQ a (lookup q dtQ hq) ha,
        readyHeapMatch_base_def c q dtQ a hq ha]
  · rcases hb with hb | ⟨q,dtQ,hq,rfl⟩
    · rw [readyHeapMatch_def_base d p dtP b (lookup p dtP hp) hb,
        readyHeapMatch_def_base c p dtP b hp hb]
    · have hp' := lookup p dtP hp
      have hq' := lookup q dtQ hq
      have hpb := (List.getElem?_eq_some_iff.1 hp).1
      have hqb := (List.getElem?_eq_some_iff.1 hq).1
      rw [readyHeapMatch_def_def d p q 0 dtP dtQ hd
        (List.getElem?_eq_some_iff.1 hp').1 (List.getElem?_eq_some_iff.1 hq').1 hp' hq',
        readyHeapMatch_def_def c p q 0 dtP dtQ hc hpb hqb hp hq,
        ConstructiveNominalMatch.index_prefix c d tail he p q hpb hqb]

/-- Original heap matching is invariant under arbitrary duplicate-index choices
in an extended ready table, in both matching directions. -/
theorem transfer (c d : context) (tail : List deftype) (he : d.TYPES=c.TYPES++tail)
    (hc : CandidateTypeReady.Ready c) (hd : CandidateTypeReady.Ready d)
    (a b ao bo av bv : heaptype)
    (ha : Resolves c a av) (hb : Resolves c b bv)
    (hao : Resolves d ao av) (hbo : Resolves d bo bv) :
    readyHeapMatch d ao bo = readyHeapMatch c a b := by
  rw [normalize d hd ao bo av bv hao hbo,
    canonical_prefix c d tail he hc hd av bv
      (resolves_canonical c a av ha) (resolves_canonical c b bv hb),
    normalize c hc a b av bv ha hb]

#print axioms transfer
end properties.wasm_module_ok.ConstructiveTypeCopyHeapMatch
