import properties.wasm_module_ok.ConstructiveBodyGetDispatch
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateAccess
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyAggregateMetadata ConstructiveBodyStorageMetadata ConstructiveConstAggregateBuilders

theorem structGetSome (c : context) (stack : inferresulttype) (s : StructIndex c) (f : ConstructiveBodyLookup.Entry s.fields)
    (mutability : SpecTec.«mut») (st : storagetype) (hf : f.value=.FieldT mutability st) (ext : extension)
    (hp : packed st=true)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.GET» s.index f.index (some ext))⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT s.definition))] [UnpackedFieldDecision.unpackedStorageResult st]))) n := by
  apply (ConstructiveBodyGetDispatch.structSome c stack s.index f.index ext _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:61» c stack (.«STRUCT.GET» s.index f.index (some ext))) n _ n
  unfold SpecTec.«Instr_ok:clause:61»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (structCall s n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp f.lookup).1)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp f.lookup).1)
  simp only [f.lookup]
  rw [hf]
  apply Eval.bind_success (packed_call st n)
  apply Eval.bind_success (Eval.guard_true hp)
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp s.lookup).1)
  rw [s.lookup]
  exact Eval.pure _

theorem structGetNone (c : context) (stack : inferresulttype) (s : StructIndex c) (f : ConstructiveBodyLookup.Entry s.fields)
    (mutability : SpecTec.«mut») (st : storagetype) (hf : f.value=.FieldT mutability st)
    (hp : ¬packed st=true)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.GET» s.index f.index none)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT s.definition))] [UnpackedFieldDecision.unpackedStorageResult st]))) n := by
  apply (ConstructiveBodyGetDispatch.structNone c stack s.index f.index _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:62» c stack (.«STRUCT.GET» s.index f.index none)) n _ n
  unfold SpecTec.«Instr_ok:clause:62»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (structCall s n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp f.lookup).1)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp f.lookup).1)
  simp only [f.lookup]
  rw [hf]
  apply Eval.bind_success (packed_call st n)
  apply Eval.bind_success (Eval.guard_true hp)
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp s.lookup).1)
  rw [s.lookup]
  exact Eval.pure _

theorem structSet (c : context) (stack : inferresulttype) (s : StructIndex c) (f : ConstructiveBodyLookup.Entry s.fields)
    (mutability : SpecTec.«mut») (st : storagetype) (hf : f.value=.FieldT mutability st)
    (hm : mutability=.Var)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.SET» s.index f.index)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT s.definition)),UnpackedFieldDecision.unpackedStorageResult st] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«STRUCT.SET» s.index f.index) 63 (by decide) rfl (by decide) _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:63» c stack (.«STRUCT.SET» s.index f.index)) n _ n
  unfold SpecTec.«Instr_ok:clause:63»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (structCall s n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp f.lookup).1)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp f.lookup).1)
  simp only [f.lookup]
  rw [hf]
  apply Eval.bind_success (Eval.guard_true (by simp [hm,SpecTec.«exec:match:mut:Var»]))
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp s.lookup).1)
  rw [s.lookup]
  exact Eval.pure _

theorem arrayGetSome (c : context) (stack : inferresulttype) (a : ArrayIndex c)
    (mutability : SpecTec.«mut») (st : storagetype) (hf : a.field=.FieldT mutability st) (ext : extension)
    (hp : packed st=true)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.GET» a.index (some ext))⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T] [UnpackedFieldDecision.unpackedStorageResult st]))) n := by
  apply (ConstructiveBodyGetDispatch.arraySome c stack a.index ext _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:69» c stack (.«ARRAY.GET» a.index (some ext))) n _ n
  unfold SpecTec.«Instr_ok:clause:69»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  rw [hf]
  apply Eval.bind_success (packed_call st n)
  apply Eval.bind_success (Eval.guard_true hp)
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  rw [a.lookup]
  exact Eval.pure _

theorem arrayGetNone (c : context) (stack : inferresulttype) (a : ArrayIndex c)
    (mutability : SpecTec.«mut») (st : storagetype) (hf : a.field=.FieldT mutability st)
    (hp : ¬packed st=true)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.GET» a.index none)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T] [UnpackedFieldDecision.unpackedStorageResult st]))) n := by
  apply (ConstructiveBodyGetDispatch.arrayNone c stack a.index _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:70» c stack (.«ARRAY.GET» a.index none)) n _ n
  unfold SpecTec.«Instr_ok:clause:70»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  rw [hf]
  apply Eval.bind_success (packed_call st n)
  apply Eval.bind_success (Eval.guard_true hp)
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  rw [a.lookup]
  exact Eval.pure _

theorem arraySet (c : context) (stack : inferresulttype) (a : ArrayIndex c)
    (mutability : SpecTec.«mut») (st : storagetype) (hf : a.field=.FieldT mutability st)
    (hm : mutability=.Var)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.SET» a.index)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,UnpackedFieldDecision.unpackedStorageResult st] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.SET» a.index) 71 (by decide) rfl (by decide) _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:71» c stack (.«ARRAY.SET» a.index)) n _ n
  unfold SpecTec.«Instr_ok:clause:71»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  rw [hf]
  apply Eval.bind_success (Eval.guard_true (by simp [hm,SpecTec.«exec:match:mut:Var»]))
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  rw [a.lookup]
  exact Eval.pure _

theorem arrayFill (c : context) (stack : inferresulttype) (a : ArrayIndex c)
    (mutability : SpecTec.«mut») (st : storagetype) (hf : a.field=.FieldT mutability st)
    (hm : mutability=.Var)
    (n : Nat) : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.FILL» a.index)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,UnpackedFieldDecision.unpackedStorageResult st,.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.FILL» a.index) 74 (by decide) rfl (by decide) _ n n).2
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:74» c stack (.«ARRAY.FILL» a.index)) n _ n
  unfold SpecTec.«Instr_ok:clause:74»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (arrayCall a n)
  rw [hf]
  apply Eval.bind_success (Eval.guard_true (by simp [hm,SpecTec.«exec:match:mut:Var»]))
  apply Eval.bind_success (UnpackedFieldDecision.unpacked_storage_total st n)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp a.lookup).1)
  rw [a.lookup]
  exact Eval.pure _

#print axioms arrayFill
end properties.wasm_module_ok.ConstructiveBodyAggregateAccess
