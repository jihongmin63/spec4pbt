import properties.wasm_module_ok.ConstructiveBodyAggregateAccess
import properties.wasm_module_ok.ConstructiveBodyArrayBulk
import properties.wasm_module_ok.ConstructiveBodyIndexedProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyAggregateMetadata ConstructiveBodyStorageMetadata ConstructiveBodyIndexedProductions ConstructiveConstAggregateBuilders

def fixedList (c : context) (stack : inferresulttype) (env : Env c) (ins outs : List valtype)
    (hi : StackBacked c (.NoEllipses,ins)) (ho : StackBacked c (.NoEllipses,outs)) (i : instr)
    (hs : ∀n,SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack i⟩)
      n (.success (.of (ConstructiveBodyControl.effect ins outs))) n) : Production c stack :=
  fixed c stack env (.NoEllipses,ins) (.NoEllipses,outs) hi ho i hs

def getOptions : storagetype → List (Option extension)
  | .ValStorageT _ => [none]
  | .PackStorageT _ => [some .SX,some .ZX]

theorem getOptions_spec (st : storagetype) (ext : Option extension) :
    ext∈getOptions st ↔ ext.isSome=packed st := by
  cases st <;> cases ext with
  | none => simp [getOptions,packed]
  | some ext => cases ext <;> simp [getOptions,packed]

theorem structField {c : context} (s : StructIndex c) (env : Env c) (f : ConstructiveBodyLookup.Entry s.fields)
    (m : SpecTec.«mut») (st : storagetype) (hf : f.value=.FieldT m st) :
    CandidateValMatch.InTableVal c (UnpackedFieldDecision.unpackedStorageResult st) := by
  simpa only [hf,UnpackedFieldDecision.unpackedFieldResult] using fieldBacked s env f

theorem arrayField {c : context} (a : ArrayIndex c) (env : Env c)
    (m : SpecTec.«mut») (st : storagetype) (hf : a.field=.FieldT m st) :
    CandidateValMatch.InTableVal c (UnpackedFieldDecision.unpackedStorageResult st) := by
  simpa only [hf,UnpackedFieldDecision.unpackedFieldResult] using arrayInput a env

def structGet (c : context) (stack : inferresulttype) (env : Env c) (s : StructIndex c)
    (f : ConstructiveBodyLookup.Entry s.fields) (m : SpecTec.«mut») (st : storagetype) (hf : f.value=.FieldT m st)
    (ext : Option extension) (he : ext.isSome=packed st) : Production c stack :=
  fixedList c stack env [.RefT (.«% %» .Null (.DefHT s.definition))] [UnpackedFieldDecision.unpackedStorageResult st]
    (cons_backed .NoEllipses (structRef s .Null) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (structField s env f m st hf) (nil_backed c .NoEllipses))
    (.«STRUCT.GET» s.index f.index ext) (by
      intro n
      cases ext with
      | none => exact ConstructiveBodyAggregateAccess.structGetNone c stack s f m st hf (by simp only [Option.isSome_none] at he; rw [←he]; decide) n
      | some ext => exact ConstructiveBodyAggregateAccess.structGetSome c stack s f m st hf ext he.symm n)

def structSet (c : context) (stack : inferresulttype) (env : Env c) (s : StructIndex c)
    (f : ConstructiveBodyLookup.Entry s.fields) (st : storagetype) (hf : f.value=.FieldT .Var st) : Production c stack :=
  fixedList c stack env [.RefT (.«% %» .Null (.DefHT s.definition)),UnpackedFieldDecision.unpackedStorageResult st] []
    (cons_backed .NoEllipses (structRef s .Null) (cons_backed .NoEllipses (structField s env f .Var st hf) (nil_backed c .NoEllipses)))
    (nil_backed c .NoEllipses) (.«STRUCT.SET» s.index f.index)
    (ConstructiveBodyAggregateAccess.structSet c stack s f .Var st hf rfl)

def arrayGet (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (m : SpecTec.«mut») (st : storagetype) (hf : a.field=.FieldT m st)
    (ext : Option extension) (he : ext.isSome=packed st) : Production c stack :=
  fixedList c stack env [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T] [UnpackedFieldDecision.unpackedStorageResult st]
    (cons_backed .NoEllipses (arrayRef a .Null) (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))
    (cons_backed .NoEllipses (arrayField a env m st hf) (nil_backed c .NoEllipses))
    (.«ARRAY.GET» a.index ext) (by
      intro n
      cases ext with
      | none => exact ConstructiveBodyAggregateAccess.arrayGetNone c stack a m st hf (by simp only [Option.isSome_none] at he; rw [←he]; decide) n
      | some ext => exact ConstructiveBodyAggregateAccess.arrayGetSome c stack a m st hf ext he.symm n)

def arraySet (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (st : storagetype) (hf : a.field=.FieldT .Var st) : Production c stack :=
  fixedList c stack env [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,UnpackedFieldDecision.unpackedStorageResult st] []
    (cons_backed .NoEllipses (arrayRef a .Null) (cons_backed .NoEllipses (num_backed c _)
      (cons_backed .NoEllipses (arrayField a env .Var st hf) (nil_backed c .NoEllipses))))
    (nil_backed c .NoEllipses) (.«ARRAY.SET» a.index)
    (ConstructiveBodyAggregateAccess.arraySet c stack a .Var st hf rfl)

def arrayFill (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (st : storagetype) (hf : a.field=.FieldT .Var st) : Production c stack :=
  fixedList c stack env [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,UnpackedFieldDecision.unpackedStorageResult st,.NumT .I32T] []
    (cons_backed .NoEllipses (arrayRef a .Null) (cons_backed .NoEllipses (num_backed c _)
      (cons_backed .NoEllipses (arrayField a env .Var st hf) (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))))
    (nil_backed c .NoEllipses) (.«ARRAY.FILL» a.index)
    (ConstructiveBodyAggregateAccess.arrayFill c stack a .Var st hf rfl)

#print axioms arrayFill
end properties.wasm_module_ok.ConstructiveBodyAggregateProductions
