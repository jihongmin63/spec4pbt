import properties.wasm_module_ok.ConstructiveTypeCopySource
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyPreserve
open SpecTec properties.wasm_module_ok
open properties.wasm_module_ok.ConstructiveTypeCopy properties.wasm_module_ok.ConstructiveTypeCopyExact properties.wasm_module_ok.ConstructiveTypeCopySource

/-- Universal source obligations follow actual structural traversal support. -/
theorem each_preserves {α β : Type} (P A : α → Prop) (B : β → Prop)
    (f : (x : α) → P x → Gen β)
    (hf : ∀ x hx y, A x → Gen.support (f x hx) y → B y)
    (xs : List α) (hx : ∀ x ∈ xs, P x) (ys : List β)
    (ha : ∀ x ∈ xs, A x) (hg : Gen.support (each P f xs hx) ys) :
    xs.length=ys.length ∧ ∀ y ∈ ys, B y := by
  have hh := (each_support P f xs hx ys).1 hg
  clear hg hx
  induction hh with
  | nil => simp
  | @cons x y xs ys hhead htail ih =>
    obtain ⟨hp,hg⟩ := hhead
    obtain ⟨hlen,hb⟩ := ih (fun x hh => ha x (by simp [hh]))
    exact ⟨by simp [hlen],by simpa using And.intro (hf x hp y (ha x (by simp)) hg) hb⟩

section Scalar
variable (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
variable (c d : context) (hd : d.TYPES.length=table.length+width)
include hd

theorem heap_valid (ht out : heaptype) (h : HeapBound (base+width) ht)
    (hg : Gen.support (heap table base width hle ht h) out) :
    HeaptypeValidation.heaptypeValid d out=true := by
  apply (heap_bound d out).2
  rw [hd]
  exact ((heap_exact table base width hle ht h out).1 hg).1

theorem val_valid (vt out : valtype) (h : ValBound (base+width) vt)
    (hv : ValtypeValidation.valtypeValid c vt=true)
    (hg : Gen.support (val table base width hle vt h) out) :
    ValtypeValidation.valtypeValid d out=true := by
  cases vt with
  | NumT nt =>
    have he : out = .NumT nt := by simpa [val] using hg
    subst out
    rfl
  | VecT vct =>
    have he : out = .VecT vct := by simpa [val] using hg
    subst out
    rfl
  | BotT => simp [ValtypeValidation.valtypeValid] at hv
  | RefT rt =>
    simp only [val,Gen.Support.support_map] at hg
    obtain ⟨ro,hg,rfl⟩ := hg
    obtain ⟨hb,_⟩ := (ref_exact_value table base width hle rt h ro).1 hg
    rcases ro with ⟨nu,ht⟩
    apply (heap_bound d ht).2
    simpa only [hd,RefBound] using hb

theorem storage_valid (st out : storagetype) (h : StorageBound (base+width) st)
    (hv : StoragetypeValidation.storagetypeValid c st=true)
    (hg : Gen.support (storage table base width hle st h) out) :
    StoragetypeValidation.storagetypeValid d out=true := by
  cases st with
  | ValStorageT vt =>
    simp only [storage,Gen.Support.support_map] at hg
    obtain ⟨vo,hg,rfl⟩ := hg
    exact val_valid table base width hle c d hd vt vo h hv hg
  | PackStorageT pt =>
    simp only [storage,Gen.Support.support_pure] at hg
    subst out
    exact hv

theorem field_valid (ft out : fieldtype) (h : FieldBound (base+width) ft)
    (hv : FieldtypeValidation.fieldtypeValid c ft=true)
    (hg : Gen.support (field table base width hle ft h) out) :
    FieldtypeValidation.fieldtypeValid d out=true := by
  rcases ft with ⟨mu,st⟩
  simp only [field,Gen.Support.support_map] at hg
  obtain ⟨so,hg,rfl⟩ := hg
  exact storage_valid table base width hle c d hd st so h hv hg

theorem str_valid (st out : strtype) (h : StrBound (base+width) st)
    (hv : StrtypeValidation.strtypeValid c st=true)
    (hg : Gen.support (str table base width hle st h) out) :
    StrtypeValidation.strtypeValid d out=true := by
  cases st with
  | DefStructT st =>
    rcases st with ⟨fs⟩
    simp only [str,Gen.Support.support_map] at hg
    obtain ⟨fo,hg,rfl⟩ := hg
    apply (fields_valid d fo).2
    exact (each_preserves _ _ _ _
      (fun x hx y ha hg => field_valid table base width hle c d hd x y hx ha hg)
      fs h fo ((fields_valid c fs).1 hv) hg).2
  | DefArrayT ar =>
    rcases ar with ⟨f⟩
    simp only [str,Gen.Support.support_map] at hg
    obtain ⟨fo,hg,rfl⟩ := hg
    exact field_valid table base width hle c d hd f fo h hv hg
  | DefFuncT ft =>
    rcases ft with ⟨ins,outs⟩
    simp only [str,Gen.Support.support_bind,Gen.Support.support_pure] at hg
    obtain ⟨io,hi,oo,ho,rfl⟩ := hg
    have hh : (∀ t∈ins,ValtypeValidation.valtypeValid c t=true) ∧
        (∀ t∈outs,ValtypeValidation.valtypeValid c t=true) := by
      simpa [StrtypeValidation.strtypeValid,FunctypeValidation.functypeValid,
        FunctypeValidation.resulttypeValid] using hv
    have hi' := (each_preserves _ _ _ _
      (fun x hx y ha hg => val_valid table base width hle c d hd x y hx ha hg)
      ins h.1 io hh.1 hi).2
    have ho' := (each_preserves _ _ _ _
      (fun x hx y ha hg => val_valid table base width hle c d hd x y hx ha hg)
      outs h.2 oo hh.2 ho).2
    simpa [StrtypeValidation.strtypeValid,FunctypeValidation.functypeValid,
      FunctypeValidation.resulttypeValid] using And.intro hi' ho'

theorem sub_valid (st out : SpecTec.subtype) (h : SubBound (base+width) st)
    (hv : SubtypeValidation.subtypeValid c st=true)
    (hg : Gen.support (sub table base width hle st h) out) :
    SubtypeValidation.subtypeValid d out=true := by
  rcases st with ⟨fin,hs,st⟩
  simp only [sub,Gen.Support.support_bind,Gen.Support.support_pure] at hg
  obtain ⟨ho,hh,so,hst,rfl⟩ := hg
  have hv' : (hs.length ≤ 1 ∧ ∀ ht∈hs,HeaptypeValidation.heaptypeValid c ht=true) ∧
      StrtypeValidation.strtypeValid c st=true := by
    simpa [SubtypeValidation.subtypeValid] using hv
  obtain ⟨hlen,hho⟩ := each_preserves _ _ _ _
    (fun x hx y _ hg => heap_valid table base width hle d hd x y hx hg)
    hs h.1 ho hv'.1.2 hh
  have hs' := str_valid table base width hle c d hd st so h.2 hv'.2 hst
  simpa [SubtypeValidation.subtypeValid] using
    And.intro (And.intro (by omega : ho.length≤1) hho) hs'
end Scalar

/-- Every generated copy preserves all original source-validation conditions.
The subtype compatibility pass is deliberately not claimed here. -/
theorem group_source_valid (table : List deftype) (base : Nat) (hle : base ≤ table.length)
    (c d : context) (ss os : List SpecTec.subtype)
    (hd : d.TYPES.length=table.length+ss.length)
    (hb : GroupBound (base+ss.length) ss)
    (hv : CandidateSourceChecks.sourceChecks c ss=true)
    (hg : Gen.support (group table base hle ss hb) (.RecT os)) :
    CandidateSourceChecks.sourceChecks d os=true := by
  have hh : Gen.support (each (SubBound (base+ss.length)) (sub table base ss.length hle) ss hb) os := by
    simpa [group] using hg
  apply (subs_valid d os).2
  exact (each_preserves _ _ _ _
    (fun x hx y ha hg => sub_valid table base ss.length hle c d hd x y hx ha hg)
    ss hb os ((subs_valid c ss).1 hv) hh).2

#print axioms group_source_valid
end properties.wasm_module_ok.ConstructiveTypeCopyPreserve
