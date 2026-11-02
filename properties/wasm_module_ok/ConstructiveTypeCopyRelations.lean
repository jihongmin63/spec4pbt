import properties.wasm_module_ok.ConstructiveTypeCopyHeapMatch
import properties.wasm_module_ok.ConstructiveTypeCopyPreserve
import properties.wasm_module_ok.MatchStrtypeConditional
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyRelations
open SpecTec properties.wasm_module_ok

inductive RefRel (H : heaptype → heaptype → Prop) : reftype → reftype → Prop
  | mk (nu : null) (a b : heaptype) (h : H a b) : RefRel H (.«% %» nu a) (.«% %» nu b)
inductive ValRel (H : heaptype → heaptype → Prop) : valtype → valtype → Prop
  | num (n : numtype) : ValRel H (.NumT n) (.NumT n)
  | vec (v : vectype) : ValRel H (.VecT v) (.VecT v)
  | ref (a b : reftype) (h : RefRel H a b) : ValRel H (.RefT a) (.RefT b)
  | bot : ValRel H .BotT .BotT
inductive StorageRel (H : heaptype → heaptype → Prop) : storagetype → storagetype → Prop
  | val (a b : valtype) (h : ValRel H a b) : StorageRel H (.ValStorageT a) (.ValStorageT b)
  | pack (p : packtype) : StorageRel H (.PackStorageT p) (.PackStorageT p)
inductive FieldRel (H : heaptype → heaptype → Prop) : fieldtype → fieldtype → Prop
  | mk (mu : SpecTec.mut) (a b : storagetype) (h : StorageRel H a b) :
      FieldRel H (.FieldT mu a) (.FieldT mu b)
inductive StrRel (H : heaptype → heaptype → Prop) : strtype → strtype → Prop
  | struct (as bs : List fieldtype) (h : List.Forall₂ (FieldRel H) as bs) :
      StrRel H (.DefStructT (.StructT as)) (.DefStructT (.StructT bs))
  | array (a b : fieldtype) (h : FieldRel H a b) :
      StrRel H (.DefArrayT (.ArrayT a)) (.DefArrayT (.ArrayT b))
  | func (ai bi ao bo : List valtype) (hi : List.Forall₂ (ValRel H) ai bi)
      (ho : List.Forall₂ (ValRel H) ao bo) :
      StrRel H (.DefFuncT (.FuncT ai ao)) (.DefFuncT (.FuncT bi bo))

private theorem take_rel {α β : Type} (R : α → β → Prop) (xs : List α) (ys : List β)
    (h : List.Forall₂ R xs ys) (n : Nat) : List.Forall₂ R (xs.take n) (ys.take n) := by
  induction h generalizing n with
  | nil => simp
  | cons h ht ih =>
    cases n with
    | zero => simp
    | succ n => exact .cons h (ih n)

section Match
variable (H : heaptype → heaptype → Prop) (f g : heaptype → heaptype → Bool)
variable (hh : ∀ a a' b b',H a a' → H b b' → g a' b'=f a b)
include hh

theorem ref_match (a a' b b' : reftype) (ha : RefRel H a a') (hb : RefRel H b b') :
    MatchReftypeConditional.matchReftypeResult g a' b' =
      MatchReftypeConditional.matchReftypeResult f a b := by
  cases ha with
  | mk nu x x' hx =>
    cases hb with
    | mk mu y y' hy => simp only [MatchReftypeConditional.matchReftypeResult,hh x x' y y' hx hy]

theorem val_match (a a' b b' : valtype) (ha : ValRel H a a') (hb : ValRel H b b') :
    MatchValtypeConditional.matchValtypeResult g a' b' =
      MatchValtypeConditional.matchValtypeResult f a b := by
  cases ha <;> cases hb <;> try rfl
  rename_i a a' ha b b' hb
  exact ref_match H f g hh a a' b b' ha hb

theorem storage_match (a a' b b' : storagetype)
    (ha : StorageRel H a a') (hb : StorageRel H b b') :
    MatchStorageConditional.storageMatch g a' b' = MatchStorageConditional.storageMatch f a b := by
  cases ha <;> cases hb <;> try rfl
  rename_i a a' ha b b' hb
  exact val_match H f g hh a a' b b' ha hb

theorem field_match (a a' b b' : fieldtype)
    (ha : FieldRel H a a') (hb : FieldRel H b b') :
    MatchFieldConditional.fieldMatch g a' b' = MatchFieldConditional.fieldMatch f a b := by
  cases ha with
  | mk mu a a' ha =>
    cases hb with
    | mk nu b b' hb =>
      cases mu <;> cases nu <;> simp only [MatchFieldConditional.fieldMatch]
      · exact storage_match H f g hh a a' b b' ha hb
      · rw [storage_match H f g hh a a' b b' ha hb,
          storage_match H f g hh b b' a a' hb ha]

theorem all_vals_match (as as' bs bs' : List valtype)
    (ha : List.Forall₂ (ValRel H) as as') (hb : List.Forall₂ (ValRel H) bs bs') :
    MatchResulttypeConditional.allMatched (MatchValtypeConditional.matchValtypeResult g) as' bs' =
      MatchResulttypeConditional.allMatched (MatchValtypeConditional.matchValtypeResult f) as bs := by
  induction ha generalizing bs bs' with
  | nil => cases hb <;> rfl
  | @cons a a' as as' ha ht ih =>
    cases hb with
    | nil => rfl
    | @cons b b' bs bs' hb hbTail =>
      simp only [MatchResulttypeConditional.allMatched]
      rw [val_match H f g hh a a' b b' ha hb,ih bs bs' hbTail]

theorem result_match (as as' bs bs' : List valtype)
    (ha : List.Forall₂ (ValRel H) as as') (hb : List.Forall₂ (ValRel H) bs bs') :
    MatchFunctionConditional.resultMatch g as' bs' = MatchFunctionConditional.resultMatch f as bs := by
  simp only [MatchFunctionConditional.resultMatch,MatchResulttypeConditional.matchResulttypeResult,
    MatchFunctionConditional.valMatch]
  rw [←ha.length_eq,←hb.length_eq,all_vals_match H f g hh as as' bs bs' ha hb]

theorem all_fields_match (as as' bs bs' : List fieldtype)
    (ha : List.Forall₂ (FieldRel H) as as') (hb : List.Forall₂ (FieldRel H) bs bs') :
    MatchStructtypeConditional.allFieldsMatched (MatchFieldConditional.fieldMatch g) as' bs' =
      MatchStructtypeConditional.allFieldsMatched (MatchFieldConditional.fieldMatch f) as bs := by
  induction ha generalizing bs bs' with
  | nil => cases hb <;> rfl
  | @cons a a' as as' ha ht ih =>
    cases hb with
    | nil => rfl
    | @cons b b' bs bs' hb hbTail =>
      simp only [MatchStructtypeConditional.allFieldsMatched]
      rw [field_match H f g hh a a' b b' ha hb,ih bs bs' hbTail]

theorem str_match (a a' b b' : strtype) (ha : StrRel H a a') (hb : StrRel H b b') :
    MatchStrtypeConditional.strMatch g a' b' = MatchStrtypeConditional.strMatch f a b := by
  cases ha <;> cases hb <;> try rfl
  · rename_i as as' ha bs bs' hb
    simp only [MatchStrtypeConditional.strMatch,MatchStructtypeConditional.structMatch]
    rw [←ha.length_eq,←hb.length_eq]
    rw [all_fields_match H f g hh (as.take bs.length) (as'.take bs.length) bs bs'
      (take_rel _ _ _ ha bs.length) hb]
  · rename_i a a' ha b b' hb
    exact field_match H f g hh a a' b b' ha hb
  · rename_i ai ai' ao ao' hi ho bi bi' bo bo' hbi hbo
    simp only [MatchStrtypeConditional.strMatch,MatchFunctionConditional.functionMatch,
      MatchFunctypeCalls.matchFunctypeResult]
    rw [result_match H f g hh bi bi' ai ai' hbi hi,
      result_match H f g hh ao ao' bo bo' ho hbo]
end Match

#print axioms str_match
end properties.wasm_module_ok.ConstructiveTypeCopyRelations
