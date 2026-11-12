import properties.wasm_module_ok.ConstructiveTypeSignatures

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveVarianceMonotone
open SpecTec properties.wasm_module_ok
open ConstructiveTypeCopy

section Lift
variable (bound : Nat) (f g : heaptype → heaptype → Bool)
variable (hf : ∀ a b, HeapBound bound a → HeapBound bound b → f a b = true → g a b = true)
include hf

theorem refs (a b : reftype) (ha : RefBound bound a) (hb : RefBound bound b) :
    MatchReftypeConditional.matchReftypeResult f a b = true →
      MatchReftypeConditional.matchReftypeResult g a b = true := by
  rcases a with ⟨nu,a⟩
  rcases b with ⟨mu,b⟩
  simp only [MatchReftypeConditional.matchReftypeResult, Bool.and_eq_true]
  rintro ⟨hn,hh⟩
  exact ⟨hn,hf a b ha hb hh⟩

theorem vals (a b : valtype) (ha : ValBound bound a) (hb : ValBound bound b) :
    MatchValtypeConditional.matchValtypeResult f a b = true →
      MatchValtypeConditional.matchValtypeResult g a b = true := by
  cases a <;> cases b <;> try exact id
  case RefT.RefT a b => exact refs bound f g hf a b ha hb

theorem storage (a b : storagetype) (ha : StorageBound bound a) (hb : StorageBound bound b) :
    MatchStorageConditional.storageMatch f a b = true →
      MatchStorageConditional.storageMatch g a b = true := by
  cases a <;> cases b <;> try exact id
  case ValStorageT.ValStorageT a b => exact vals bound f g hf a b ha hb

theorem fields (a b : fieldtype) (ha : FieldBound bound a) (hb : FieldBound bound b) :
    MatchFieldConditional.fieldMatch f a b = true →
      MatchFieldConditional.fieldMatch g a b = true := by
  rcases a with ⟨mu,a⟩
  rcases b with ⟨nu,b⟩
  cases mu <;> cases nu <;> try exact id
  · exact storage bound f g hf a b ha hb
  · simp only [MatchFieldConditional.fieldMatch, Bool.and_eq_true]
    rintro ⟨hforward,hbackward⟩
    exact ⟨storage bound f g hf a b ha hb hforward, storage bound f g hf b a hb ha hbackward⟩

theorem allVals (as bs : List valtype)
    (ha : ∀ a ∈ as, ValBound bound a) (hb : ∀ b ∈ bs, ValBound bound b) :
    MatchResulttypeConditional.allMatched (MatchValtypeConditional.matchValtypeResult f) as bs = true →
      MatchResulttypeConditional.allMatched (MatchValtypeConditional.matchValtypeResult g) as bs = true := by
  induction as generalizing bs with
  | nil => cases bs <;> exact id
  | cons a as ih =>
    cases bs with
    | nil => exact id
    | cons b bs =>
      simp only [MatchResulttypeConditional.allMatched, Bool.and_eq_true]
      rintro ⟨hhead,htail⟩
      exact ⟨vals bound f g hf a b (ha a (by simp)) (hb b (by simp)) hhead,
        ih bs (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])) htail⟩

theorem results (as bs : List valtype)
    (ha : ∀ a ∈ as, ValBound bound a) (hb : ∀ b ∈ bs, ValBound bound b) :
    MatchFunctionConditional.resultMatch f as bs = true →
      MatchFunctionConditional.resultMatch g as bs = true := by
  simp only [MatchFunctionConditional.resultMatch, MatchResulttypeConditional.matchResulttypeResult,
    MatchFunctionConditional.valMatch, Bool.and_eq_true]
  rintro ⟨hlen,hm⟩
  exact ⟨hlen,allVals bound f g hf as bs ha hb hm⟩

theorem allFields (as bs : List fieldtype)
    (ha : ∀ a ∈ as, FieldBound bound a) (hb : ∀ b ∈ bs, FieldBound bound b) :
    MatchStructtypeConditional.allFieldsMatched (MatchFieldConditional.fieldMatch f) as bs = true →
      MatchStructtypeConditional.allFieldsMatched (MatchFieldConditional.fieldMatch g) as bs = true := by
  induction as generalizing bs with
  | nil => cases bs <;> exact id
  | cons a as ih =>
    cases bs with
    | nil => exact id
    | cons b bs =>
      simp only [MatchStructtypeConditional.allFieldsMatched, Bool.and_eq_true]
      rintro ⟨hhead,htail⟩
      exact ⟨fields bound f g hf a b (ha a (by simp)) (hb b (by simp)) hhead,
        ih bs (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])) htail⟩

/-- All structural matching occurrences are positive, including both directions
for mutable fields and reversed operands for function inputs. Thus conservative
planned heap matches remain sound even if closing adds accidental aliases. -/
theorem shapes (a b : strtype) (ha : StrBound bound a) (hb : StrBound bound b) :
    MatchStrtypeConditional.strMatch f a b = true →
      MatchStrtypeConditional.strMatch g a b = true := by
  cases a <;> cases b <;> try exact id
  case DefStructT.DefStructT a b =>
    rcases a with ⟨as⟩
    rcases b with ⟨bs⟩
    simp only [MatchStrtypeConditional.strMatch, MatchStructtypeConditional.structMatch, Bool.and_eq_true]
    rintro ⟨hlen,hm⟩
    exact ⟨hlen,allFields bound f g hf (as.take bs.length) bs
      (fun x hx => ha x (List.mem_of_mem_take hx)) hb hm⟩
  case DefArrayT.DefArrayT a b =>
    cases a
    cases b
    exact fields bound f g hf _ _ ha hb
  case DefFuncT.DefFuncT a b =>
    rcases a with ⟨ai,ao⟩
    rcases b with ⟨bi,bo⟩
    simp only [MatchStrtypeConditional.strMatch, MatchFunctionConditional.functionMatch,
      MatchFunctypeCalls.matchFunctypeResult, Bool.and_eq_true]
    rintro ⟨hi,ho⟩
    exact ⟨results bound f g hf bi ai hb.1 ha.1 hi,results bound f g hf ao bo ha.2 hb.2 ho⟩
end Lift

end properties.wasm_module_ok.ConstructiveVarianceMonotone
