import properties.wasm_module_ok.ConstructiveBodyStorageMetadata
import properties.wasm_module_ok.ConstructiveBodyTypeClassifiers
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyArrayBulk
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyAggregateMetadata ConstructiveBodyStorageMetadata ConstructiveBodyTypeClassifiers ConstructiveConstAggregateBuilders

theorem newElem (c : context) (stack : inferresulttype) (a : ArrayIndex c) (y : Nat)
    (rt : reftype) (hy : c.ELEMS[y]?=some rt)
    (hm : ∀n,Eval SpecTec.specTecProgram (.call ⟨Bool,SpecTecCall.«$match_valtype» c.TYPES (.RefT rt) (UnpackedFieldDecision.unpackedFieldResult a.field)⟩) n (.success (.of true)) n)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.NEW_ELEM» a.index y)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT .I32T,.NumT .I32T] [.RefT (.«% %» .NoNull (.DefHT a.definition))]))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.NEW_ELEM» a.index y) 67 (by decide) rfl (by decide) _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:67» c stack (.«ARRAY.NEW_ELEM» a.index y)) n _ n
  unfold SpecTec.«Instr_ok:clause:67»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_field_total a.field n)
  apply Eval.bind_success (hm n)
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  rw [a.lookup]
  exact Eval.pure _

theorem newData (c : context) (stack : inferresulttype) (a : ArrayIndex c) (y : Nat)
    (hy : c.DATAS[y]?=some .OK)
    (hn : numeric (UnpackedFieldDecision.unpackedFieldResult a.field)=true ∨ vector (UnpackedFieldDecision.unpackedFieldResult a.field)=true)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.NEW_DATA» a.index y)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT .I32T,.NumT .I32T] [.RefT (.«% %» .NoNull (.DefHT a.definition))]))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.NEW_DATA» a.index y) 68 (by decide) rfl (by decide) _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:68» c stack (.«ARRAY.NEW_DATA» a.index y)) n _ n
  unfold SpecTec.«Instr_ok:clause:68»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_field_total a.field n)
  apply Eval.bind_success (numeric_total (UnpackedFieldDecision.unpackedFieldResult a.field) n)
  apply Eval.bind_success (vector_total (UnpackedFieldDecision.unpackedFieldResult a.field) n)
  apply Eval.bind_success (Eval.guard_true hn)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  rw [a.lookup]
  exact Eval.pure _

theorem initData (c : context) (stack : inferresulttype) (a : ArrayIndex c) (y : Nat)
    (st : storagetype) (hf : a.field=.FieldT .Var st)
    (hy : c.DATAS[y]?=some .OK)
    (hn : numeric (UnpackedFieldDecision.unpackedStorageResult st)=true ∨ vector (UnpackedFieldDecision.unpackedStorageResult st)=true)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.INIT_DATA» a.index y)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,.NumT .I32T,.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.INIT_DATA» a.index y) 75 (by decide) rfl (by decide) _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:75» c stack (.«ARRAY.INIT_DATA» a.index y)) n _ n
  unfold SpecTec.«Instr_ok:clause:75»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  rw [hf]
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (numeric_total (UnpackedFieldDecision.unpackedStorageResult st) n)
  apply Eval.bind_success (vector_total (UnpackedFieldDecision.unpackedStorageResult st) n)
  apply Eval.bind_success (Eval.guard_true hn)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  rw [a.lookup]
  exact Eval.pure _

theorem initElem (c : context) (stack : inferresulttype) (a : ArrayIndex c) (y : Nat)
    (st : storagetype) (hf : a.field=.FieldT .Var st)
    (rt : reftype) (hy : c.ELEMS[y]?=some rt)
    (hm : ∀n,Eval SpecTec.specTecProgram (.call ⟨Bool,SpecTecCall.«$match_valtype» c.TYPES (.RefT rt) (UnpackedFieldDecision.unpackedStorageResult st)⟩) n (.success (.of true)) n)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.INIT_ELEM» a.index y)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,.NumT .I32T,.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.INIT_ELEM» a.index y) 76 (by decide) rfl (by decide) _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:76» c stack (.«ARRAY.INIT_ELEM» a.index y)) n _ n
  unfold SpecTec.«Instr_ok:clause:76»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  rw [hf]
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (hm n)
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  rw [a.lookup]
  exact Eval.pure _

theorem copy (c : context) (stack : inferresulttype) (a b : ArrayIndex c)
    (st1 st2 : storagetype) (mut2 : SpecTec.«mut»)
    (ha : a.field=.FieldT .Var st1) (hb : b.field=.FieldT mut2 st2)
    (hm : ∀n,Eval SpecTec.specTecProgram (.call ⟨Bool,SpecTecCall.«$match_storagetype» c.TYPES st2 st1⟩) n (.success (.of true)) n)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.COPY» a.index b.index)⟩)
      n (.success (.of (ConstructiveBodyControl.effect
        [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,.RefT (.«% %» .Null (.DefHT b.definition)),.NumT .I32T,.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.COPY» a.index b.index) 73 (by decide) rfl (by decide) _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:73» c stack (.«ARRAY.COPY» a.index b.index)) n _ n
  unfold SpecTec.«Instr_ok:clause:73»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  rw [ha]
  apply Eval.bind_success (arrayCall b n)
  rw [hb]
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (hm n)
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp b.lookup).1)
  simp only [a.lookup,b.lookup]
  exact Eval.pure _

#print axioms copy
end properties.wasm_module_ok.ConstructiveBodyArrayBulk
