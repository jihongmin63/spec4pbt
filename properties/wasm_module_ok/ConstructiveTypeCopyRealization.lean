import properties.wasm_module_ok.ConstructiveTypeCopyRelations
import properties.wasm_module_ok.ConstructiveTypeCopyOrder
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyRealization
open SpecTec properties.wasm_module_ok
open ConstructiveRelocateIndices ConstructiveTypeCopy
open properties.wasm_module_ok.ConstructiveTypeCopyHeapMatch properties.wasm_module_ok.ConstructiveTypeCopyRelations

def defs (width : Nat) (rect : rectype) : List deftype :=
  (List.range width).map (fun i => .DefT rect i)
def extend (c : context) (width : Nat) (rect : rectype) : context :=
  {c with TYPES := c.TYPES++defs width rect}

@[simp] theorem extend_length (c : context) (w : Nat) (r : rectype) :
    (extend c w r).TYPES.length=c.TYPES.length+w := by simp [extend,defs]

theorem old_lookup (c : context) (w : Nat) (r : rectype) (i : Nat) (dt : deftype)
    (h : c.TYPES[i]?=some dt) : (extend c w r).TYPES[i]?=some dt := by
  simp only [extend,List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1,h]

theorem new_lookup (c : context) (w : Nat) (r : rectype) (i : Nat) (hi : i<w) :
    (extend c w r).TYPES[c.TYPES.length+i]?=some (.DefT r i) := by
  simp [extend,defs,List.getElem?_append_right (by omega : c.TYPES.length≤c.TYPES.length+i),
    List.getElem?_range hi]

def HeapRel (c d : context) (a b : heaptype) : Prop :=
  ∃ v,Resolves c a v ∧ Resolves d b v

theorem heap_realizes (c : context) (base w : Nat) (r : rectype) (hle : base≤c.TYPES.length)
    (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i))
    (ht out : heaptype) (h : HeapBound (base+w) ht)
    (hg : Gen.support (heap c.TYPES base w hle ht h) out) :
    HeapRel c (extend c w r) ht out := by
  rcases raw_cases (base+w) ht h with hb | ⟨i,rfl,hi⟩
  · rw [heap_base c.TYPES base w hle ht h hb] at hg
    simp only [Gen.Support.support_pure] at hg
    subst out
    have hb' : ht∈HeaptypeValidation.baseHeaptypes := by
      cases ht <;> simp_all [Base,HeaptypeValidation.baseHeaptypes]
    exact ⟨ht,.base ht hb',.base ht hb'⟩
  · simp only [heap,Gen.Support.support_map] at hg
    obtain ⟨j,hj,rfl⟩ := hg
    by_cases hl : base≤i
    · have hij : i-base<w := Nat.sub_lt_left_of_lt_add hl hi
      have hold : c.TYPES[i]?=some (.DefT r (i-base)) := by
        simpa [Nat.add_sub_of_le hl] using hgroup (i-base) hij
      have he : j=c.TYPES.length+(i-base) := by
        simpa only [relocate,dif_pos hl,Gen.Support.support_pure] using hj
      subst j
      exact ⟨.DefHT (.DefT r (i-base)),.stat i _ hold,
        .stat _ _ (new_lookup c w r (i-base) hij)⟩
    · have hib : i<c.TYPES.length := Nat.lt_of_lt_of_le (Nat.lt_of_not_ge hl) hle
      let dt := c.TYPES[i]'hib
      have hi' : c.TYPES[i]?=some dt := List.getElem?_eq_getElem hib
      have hj' : c.TYPES[j]?=some dt := by
        have hslots : Gen.support (ConstructiveAliases.aliases c.TYPES dt i) j := by
          simpa only [relocate,dif_neg hl] using hj
        exact (ConstructiveAliases.aliases_support c.TYPES dt i hi' j).1 hslots
      exact ⟨.DefHT dt,.stat i dt hi',.stat j dt (old_lookup c w r j dt hj')⟩

private theorem each_rel {α β : Type} (P : α → Prop) (f : (x : α) → P x → Gen β)
    (R : α → β → Prop) (hf : ∀ x hx y,Gen.support (f x hx) y → R x y)
    (xs : List α) (hx : ∀ x∈xs,P x) (ys : List β)
    (hg : Gen.support (each P f xs hx) ys) : List.Forall₂ R xs ys := by
  have hh := (each_support P f xs hx ys).1 hg
  clear hg hx
  induction hh with
  | nil => exact .nil
  | cons h ht ih =>
    obtain ⟨hp,hg⟩ := h
    exact .cons (hf _ hp _ hg) ih

section Shapes
variable (c : context) (base w : Nat) (r : rectype) (hle : base≤c.TYPES.length)
variable (hgroup : ∀ i<w,c.TYPES[base+i]?=some (.DefT r i))
include hgroup

theorem ref_realizes (rt out : reftype) (h : RefBound (base+w) rt)
    (hg : Gen.support (ref c.TYPES base w hle rt h) out) :
    RefRel (HeapRel c (extend c w r)) rt out := by
  rcases rt with ⟨nu,ht⟩
  simp only [ref,Gen.Support.support_map] at hg
  obtain ⟨ho,hg,rfl⟩ := hg
  exact .mk nu ht ho (heap_realizes c base w r hle hgroup ht ho h hg)

theorem val_realizes (vt out : valtype) (h : ValBound (base+w) vt)
    (hg : Gen.support (val c.TYPES base w hle vt h) out) :
    ValRel (HeapRel c (extend c w r)) vt out := by
  cases vt with
  | NumT nt =>
    have he : out=.NumT nt := by simpa [val] using hg
    subst out
    exact .num nt
  | VecT vct =>
    have he : out=.VecT vct := by simpa [val] using hg
    subst out
    exact .vec vct
  | BotT =>
    have he : out=.BotT := by simpa [val] using hg
    subst out
    exact .bot
  | RefT rt =>
    simp only [val,Gen.Support.support_map] at hg
    obtain ⟨ro,hg,rfl⟩ := hg
    exact .ref rt ro (ref_realizes c base w r hle hgroup rt ro h hg)

theorem storage_realizes (st out : storagetype) (h : StorageBound (base+w) st)
    (hg : Gen.support (storage c.TYPES base w hle st h) out) :
    StorageRel (HeapRel c (extend c w r)) st out := by
  cases st with
  | ValStorageT vt =>
    simp only [storage,Gen.Support.support_map] at hg
    obtain ⟨vo,hg,rfl⟩ := hg
    exact .val vt vo (val_realizes c base w r hle hgroup vt vo h hg)
  | PackStorageT pt =>
    simp only [storage,Gen.Support.support_pure] at hg
    subst out
    exact .pack pt

theorem field_realizes (ft out : fieldtype) (h : FieldBound (base+w) ft)
    (hg : Gen.support (field c.TYPES base w hle ft h) out) :
    FieldRel (HeapRel c (extend c w r)) ft out := by
  rcases ft with ⟨mu,st⟩
  simp only [field,Gen.Support.support_map] at hg
  obtain ⟨so,hg,rfl⟩ := hg
  exact .mk mu st so (storage_realizes c base w r hle hgroup st so h hg)

theorem str_realizes (st out : strtype) (h : StrBound (base+w) st)
    (hg : Gen.support (str c.TYPES base w hle st h) out) :
    StrRel (HeapRel c (extend c w r)) st out := by
  cases st with
  | DefStructT st =>
    rcases st with ⟨fs⟩
    simp only [str,Gen.Support.support_map] at hg
    obtain ⟨fo,hg,rfl⟩ := hg
    exact .struct fs fo (each_rel _ _ _ (fun x hx y => field_realizes c base w r hle hgroup x y hx) fs h fo hg)
  | DefArrayT ar =>
    rcases ar with ⟨f⟩
    simp only [str,Gen.Support.support_map] at hg
    obtain ⟨fo,hg,rfl⟩ := hg
    exact .array f fo (field_realizes c base w r hle hgroup f fo h hg)
  | DefFuncT ft =>
    rcases ft with ⟨ins,outs⟩
    simp only [str,Gen.Support.support_bind,Gen.Support.support_pure] at hg
    obtain ⟨io,hi,oo,ho,rfl⟩ := hg
    exact .func ins io outs oo
      (each_rel _ _ _ (fun x hx y => val_realizes c base w r hle hgroup x y hx) ins h.1 io hi)
      (each_rel _ _ _ (fun x hx y => val_realizes c base w r hle hgroup x y hx) outs h.2 oo ho)
end Shapes

#print axioms str_realizes
end properties.wasm_module_ok.ConstructiveTypeCopyRealization
