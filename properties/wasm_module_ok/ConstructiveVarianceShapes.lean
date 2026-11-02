import properties.wasm_module_ok.ConstructiveVarianceAtoms

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveVarianceShapes
open SpecTec properties.wasm_module_ok
open ConstructiveVarianceAtoms

theorem each_conditions {α β : Type} (P : α → Prop) (Q : β → Prop)
    (g : (x : α) → P x → Gen β) (R : α → β → Prop)
    (hg : ∀ x hx y, Gen.support (g x hx) y ↔ Q y ∧ R x y)
    (xs : List α) (hx : ∀ x ∈ xs, P x) (ys : List β) :
    Gen.support (ConstructiveTypeCopy.each P g xs hx) ys ↔
      (∀ y ∈ ys, Q y) ∧ List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [ConstructiveTypeCopy.each]
  | cons x xs ih =>
    cases ys <;> simp [ConstructiveTypeCopy.each, hg, ih,
      and_assoc, and_left_comm, and_comm]

theorem vals_relation (d : Direction) (r : heaptype → heaptype → Bool)
    (xs ys : List valtype) :
    List.Forall₂ (fun x y => directed d (MatchValtypeConditional.matchValtypeResult r) y x = true) xs ys ↔
      directed d (MatchFunctionConditional.resultMatch r) ys xs = true := by
  induction xs generalizing ys with
  | nil => cases ys <;> cases d <;>
      simp [directed, MatchFunctionConditional.resultMatch,
        MatchResulttypeConditional.matchResulttypeResult, MatchResulttypeConditional.allMatched]
  | cons x xs ih =>
    cases ys with
    | nil => cases d <;>
        simp [directed, MatchFunctionConditional.resultMatch,
          MatchResulttypeConditional.matchResulttypeResult, MatchResulttypeConditional.allMatched]
    | cons y ys =>
      rw [List.forall₂_cons, ih]
      cases d <;> simp [directed, MatchFunctionConditional.resultMatch,
        MatchResulttypeConditional.matchResulttypeResult, MatchResulttypeConditional.allMatched,
        MatchFunctionConditional.valMatch, and_assoc, and_left_comm, and_comm]

theorem fields_relation (r : heaptype → heaptype → Bool) (xs ys : List fieldtype) :
    List.Forall₂ (fun x y => MatchFieldConditional.fieldMatch r y x = true) xs ys ↔
      MatchStructtypeConditional.allFieldsMatched (MatchFieldConditional.fieldMatch r) ys xs = true := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [MatchStructtypeConditional.allFieldsMatched]
  | cons x xs ih => cases ys <;> simp [MatchStructtypeConditional.allFieldsMatched, ih]

def values (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (xs : List valtype) (hx : ∀ x ∈ xs, ValidVal bound x) : Gen (List valtype) :=
  ConstructiveTypeCopy.each (ValidVal bound) (vals bound d r) xs hx

theorem values_support (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound bound h → r h h = true)
    (xs : List valtype) (hx : ∀ x ∈ xs, ValidVal bound x) (ys : List valtype) :
    Gen.support (values bound d r xs hx) ys ↔
      (∀ y ∈ ys, ValidVal bound y) ∧ directed d (MatchFunctionConditional.resultMatch r) ys xs = true := by
  rw [values, each_conditions (ValidVal bound) (ValidVal bound) (vals bound d r)
    _ (vals_support bound d r hr), vals_relation]

def inheritedFields (bound : Nat) (r : heaptype → heaptype → Bool)
    (fs : List fieldtype) (hf : ∀ f ∈ fs, ValidField bound f) : Gen (List fieldtype) :=
  ConstructiveTypeCopy.each (ValidField bound) (fields bound r) fs hf

theorem inherited_support (bound : Nat) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound bound h → r h h = true)
    (fs : List fieldtype) (hf : ∀ f ∈ fs, ValidField bound f) (ys : List fieldtype) :
    Gen.support (inheritedFields bound r fs hf) ys ↔
      (∀ y ∈ ys, ValidField bound y) ∧
      List.Forall₂ (fun f y => MatchFieldConditional.fieldMatch r y f = true) fs ys :=
  each_conditions (ValidField bound) (ValidField bound) (fields bound r)
    _ (fields_support bound r hr) fs hf ys

def extendedFields (c : context) (r : heaptype → heaptype → Bool)
    (fs : List fieldtype) (hf : ∀ f ∈ fs, ValidField c.TYPES.length f) : Gen (List fieldtype) := do
  let inherited ← inheritedFields c.TYPES.length r fs hf
  let extra ← ConstructiveLists.all (ConstructiveTypeShapes.fields c)
  pure (inherited ++ extra)

theorem extended_support (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (fs : List fieldtype) (hf : ∀ f ∈ fs, ValidField c.TYPES.length f) (ys : List fieldtype) :
    Gen.support (extendedFields c r fs hf) ys ↔
      (∀ y ∈ ys, ValidField c.TYPES.length y) ∧
      MatchStructtypeConditional.structMatch (MatchFieldConditional.fieldMatch r)
        (.StructT ys) (.StructT fs) = true := by
  simp only [extendedFields, Gen.Support.support_bind, Gen.Support.support_pure]
  constructor
  · rintro ⟨ins,hins,extra,hextra,rfl⟩
    obtain ⟨hv,hm⟩ := (inherited_support c.TYPES.length r hr fs hf ins).1 hins
    have hl := hm.length_eq
    have he : ∀ y ∈ extra, ValidField c.TYPES.length y := by
      simpa only [ConstructiveLists.all_support, ConstructiveTypeShapes.fields_support,
        ← valid_field_iff] using hextra
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hv y hy
      · exact he y hy
    have hmatch := (fields_relation r fs ins).1 hm
    simpa [MatchStructtypeConditional.structMatch, hl, hmatch] using
      (show ins.length ≤ ins.length+extra.length from Nat.le_add_right _ _)
  · rintro ⟨hv,hm⟩
    have hm' : fs.length ≤ ys.length ∧
        MatchStructtypeConditional.allFieldsMatched (MatchFieldConditional.fieldMatch r)
          (ys.take fs.length) fs = true := by simpa [MatchStructtypeConditional.structMatch] using hm
    refine ⟨ys.take fs.length, ?_, ys.drop fs.length, ?_, ?_⟩
    · apply (inherited_support c.TYPES.length r hr fs hf _).2
      exact ⟨fun y hy => hv y (List.mem_of_mem_take hy), (fields_relation r fs _).2 hm'.2⟩
    · rw [ConstructiveLists.all_support]
      intro y hy
      rw [ConstructiveTypeShapes.fields_support, ← valid_field_iff]
      exact hv y (List.mem_of_mem_drop hy)
    · exact (List.take_append_drop _ _).symm

def ValidShape (bound : Nat) : strtype → Prop
  | .DefStructT (.StructT fs) => ∀ f ∈ fs, ValidField bound f
  | .DefArrayT (.ArrayT f) => ValidField bound f
  | .DefFuncT (.FuncT ins outs) =>
    (∀ v ∈ ins, ValidVal bound v) ∧ (∀ v ∈ outs, ValidVal bound v)

/-- Inherited fields are generated with the required variance. Structs append
arbitrarily many fresh fields; function parameter/result lengths stay exact. -/
def below (c : context) (r : heaptype → heaptype → Bool)
    (target : strtype) (ht : ValidShape c.TYPES.length target) : Gen strtype :=
  match target with
  | .DefStructT (.StructT fs) =>
    (fun fs => .DefStructT (.StructT fs)) <$> extendedFields c r fs ht
  | .DefArrayT (.ArrayT f) =>
    (fun f => .DefArrayT (.ArrayT f)) <$> fields c.TYPES.length r f ht
  | .DefFuncT (.FuncT ins outs) => do
    let ins' ← values c.TYPES.length .above r ins ht.1
    let outs' ← values c.TYPES.length .below r outs ht.2
    pure (.DefFuncT (.FuncT ins' outs'))

theorem below_support (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (target : strtype) (ht : ValidShape c.TYPES.length target) (out : strtype) :
    Gen.support (below c r target ht) out ↔ ValidShape c.TYPES.length out ∧
      MatchStrtypeConditional.strMatch r out target = true := by
  cases target with
  | DefStructT t =>
    cases t
    cases out with
    | DefStructT o =>
      cases o
      simpa [below, ValidShape, MatchStrtypeConditional.strMatch] using
        extended_support c r hr _ ht _
    | DefArrayT o => simp [below, MatchStrtypeConditional.strMatch]
    | DefFuncT o => simp [below, MatchStrtypeConditional.strMatch]
  | DefArrayT t =>
    cases t
    cases out with
    | DefArrayT o =>
      cases o
      simpa [below, ValidShape, MatchStrtypeConditional.strMatch,
        MatchArrayConditional.arrayMatch] using fields_support c.TYPES.length r hr _ ht _
    | DefStructT o => simp [below, MatchStrtypeConditional.strMatch]
    | DefFuncT o => simp [below, MatchStrtypeConditional.strMatch]
  | DefFuncT t =>
    rcases t with ⟨ins,outs⟩
    cases out with
    | DefFuncT o =>
      cases o
      simp [below, ValidShape, values_support c.TYPES.length _ r hr,
        MatchStrtypeConditional.strMatch, MatchFunctionConditional.functionMatch,
        MatchFunctypeCalls.matchFunctypeResult, directed, and_assoc, and_left_comm, and_comm]
    | DefStructT o => simp [below, MatchStrtypeConditional.strMatch]
    | DefArrayT o => simp [below, MatchStrtypeConditional.strMatch]

theorem values_finite (b : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (xs : List valtype) (hx : ∀ x ∈ xs, ValidVal b x) :
    ConstructiveTypeAtoms.FiniteConstruction (values b d r xs hx) :=
  ConstructiveTypeCopy.each_finite _ _ (vals_finite b d r) xs hx

theorem inherited_finite (b : Nat) (r : heaptype → heaptype → Bool)
    (xs : List fieldtype) (hx : ∀ x ∈ xs, ValidField b x) :
    ConstructiveTypeAtoms.FiniteConstruction (inheritedFields b r xs hx) :=
  ConstructiveTypeCopy.each_finite _ _ (fields_finite b r) xs hx

theorem below_audit (c : context) (r : heaptype → heaptype → Bool)
    (target : strtype) (ht : ValidShape c.TYPES.length target) :
    ConstructiveGenAudit.Structural (below c r target ht) := by
  cases target with
  | DefStructT t =>
    cases t
    exact ⟨⟨ConstructiveGenAudit.finite_audit _ (inherited_finite _ _ _ _), fun _ =>
      ⟨ConstructiveLists.all_audit _ (ConstructiveTypeShapes.fields_audit c), fun _ => trivial⟩⟩,
      fun _ => trivial⟩
  | DefArrayT t =>
    cases t
    exact ⟨ConstructiveGenAudit.finite_audit _ (fields_finite _ _ _ _), fun _ => trivial⟩
  | DefFuncT t =>
    cases t
    exact ⟨ConstructiveGenAudit.finite_audit _ (values_finite _ _ _ _ _), fun _ =>
      ⟨ConstructiveGenAudit.finite_audit _ (values_finite _ _ _ _ _), fun _ => trivial⟩⟩

theorem below_total (c : context) (r : heaptype → heaptype → Bool)
    (target : strtype) (ht : ValidShape c.TYPES.length target) :
    Gen.total (below c r target ht) :=
  ConstructiveGenAudit.audit_total _ (below_audit c r target ht)

theorem valid_vals_iff (c : context) (vs : List valtype) :
    (∀ v ∈ vs, ValidVal c.TYPES.length v) ↔ FunctypeValidation.resulttypeValid c vs = true := by
  change (∀ v ∈ vs, ValidVal c.TYPES.length v) ↔
    ResulttypeListValidation.allValtypesValid c vs = true
  induction vs with
  | nil => simp [ResulttypeListValidation.allValtypesValid]
  | cons v vs ih => simp [ResulttypeListValidation.allValtypesValid, valid_val_iff, ← ih]

theorem valid_fields_iff (c : context) (fs : List fieldtype) :
    (∀ f ∈ fs, ValidField c.TYPES.length f) ↔
      StructtypeFieldListValidation.allFieldsValid c fs = true := by
  induction fs with
  | nil => simp [StructtypeFieldListValidation.allFieldsValid]
  | cons f fs ih => simp [StructtypeFieldListValidation.allFieldsValid, valid_field_iff, ← ih]

theorem valid_shape_iff (c : context) (st : strtype) :
    ValidShape c.TYPES.length st ↔ StrtypeValidation.strtypeValid c st = true := by
  cases st with
  | DefStructT s => cases s; exact valid_fields_iff c _
  | DefArrayT s => cases s; exact valid_field_iff c _
  | DefFuncT s => cases s; simp [ValidShape, StrtypeValidation.strtypeValid,
      FunctypeValidation.functypeValid, valid_vals_iff]

end properties.wasm_module_ok.ConstructiveVarianceShapes
