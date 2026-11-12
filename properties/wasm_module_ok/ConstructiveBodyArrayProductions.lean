import properties.wasm_module_ok.ConstructiveBodyAggregateProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyArrayProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyAggregateMetadata ConstructiveBodyStorageMetadata ConstructiveBodyIndexedProductions ConstructiveBodyAggregateProductions ConstructiveConstAggregateBuilders

def numericStorage (t : valtype) : Bool := ConstructiveBodyTypeClassifiers.numeric t || ConstructiveBodyTypeClassifiers.vector t

theorem dataLookup {c : context} (e : ConstructiveBodyLookup.Entry c.DATAS) : c.DATAS[e.index]?=some .OK := by
  have he : e.value=datatype.OK := by cases e.value; rfl
  simpa only [he] using e.lookup

def newElem (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (e : ConstructiveBodyLookup.Entry c.ELEMS)
    (hm : CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedFieldResult a.field)=true) : Production c stack :=
  fixedList c stack env [.NumT .I32T,.NumT .I32T] [.RefT (.«% %» .NoNull (.DefHT a.definition))]
    (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))
    (cons_backed .NoEllipses (arrayRef a .NoNull) (nil_backed c .NoEllipses))
    (.«ARRAY.NEW_ELEM» a.index e.index) (by
      apply ConstructiveBodyArrayBulk.newElem c stack a e.index e.value e.lookup
      intro n
      simpa only [hm] using CandidateValMatch.candidate_val_match_total c (.RefT e.value)
        (UnpackedFieldDecision.unpackedFieldResult a.field) n env.ready (env.elems _ e.mem) (arrayInput a env))

def newData (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (e : ConstructiveBodyLookup.Entry c.DATAS)
    (hn : numericStorage (UnpackedFieldDecision.unpackedFieldResult a.field)=true) : Production c stack :=
  fixedList c stack env [.NumT .I32T,.NumT .I32T] [.RefT (.«% %» .NoNull (.DefHT a.definition))]
    (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))
    (cons_backed .NoEllipses (arrayRef a .NoNull) (nil_backed c .NoEllipses))
    (.«ARRAY.NEW_DATA» a.index e.index)
    (ConstructiveBodyArrayBulk.newData c stack a e.index (dataLookup e) (Bool.or_eq_true_iff.mp hn))

def initElem (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (st : storagetype) (hf : a.field=.FieldT .Var st) (e : ConstructiveBodyLookup.Entry c.ELEMS)
    (hm : CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedStorageResult st)=true) : Production c stack :=
  fixedList c stack env [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,.NumT .I32T,.NumT .I32T] []
    (cons_backed .NoEllipses (arrayRef a .Null) (cons_backed .NoEllipses (num_backed c _)
      (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))))
    (nil_backed c .NoEllipses) (.«ARRAY.INIT_ELEM» a.index e.index) (by
      apply ConstructiveBodyArrayBulk.initElem c stack a e.index st hf e.value e.lookup
      intro n
      simpa only [hm] using CandidateValMatch.candidate_val_match_total c (.RefT e.value)
        (UnpackedFieldDecision.unpackedStorageResult st) n env.ready (env.elems _ e.mem) (arrayField a env .Var st hf))

def initData (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (st : storagetype) (hf : a.field=.FieldT .Var st) (e : ConstructiveBodyLookup.Entry c.DATAS)
    (hn : numericStorage (UnpackedFieldDecision.unpackedStorageResult st)=true) : Production c stack :=
  fixedList c stack env [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,.NumT .I32T,.NumT .I32T] []
    (cons_backed .NoEllipses (arrayRef a .Null) (cons_backed .NoEllipses (num_backed c _)
      (cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))))
    (nil_backed c .NoEllipses) (.«ARRAY.INIT_DATA» a.index e.index)
    (ConstructiveBodyArrayBulk.initData c stack a e.index st hf (dataLookup e) (Bool.or_eq_true_iff.mp hn))

def copy (c : context) (stack : inferresulttype) (env : Env c) (a b : ArrayIndex c)
    (st1 st2 : storagetype) (m2 : SpecTec.«mut»)
    (ha : a.field=.FieldT .Var st1) (hb : b.field=.FieldT m2 st2)
    (hm : storageMatch c st2 st1=true) : Production c stack :=
  fixedList c stack env [.RefT (.«% %» .Null (.DefHT a.definition)),.NumT .I32T,
      .RefT (.«% %» .Null (.DefHT b.definition)),.NumT .I32T,.NumT .I32T] []
    (cons_backed .NoEllipses (arrayRef a .Null) (cons_backed .NoEllipses (num_backed c _)
      (cons_backed .NoEllipses (arrayRef b .Null) (cons_backed .NoEllipses (num_backed c _)
        (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))))))
    (nil_backed c .NoEllipses) (.«ARRAY.COPY» a.index b.index) (by
      apply ConstructiveBodyArrayBulk.copy c stack a b st1 st2 m2 ha hb
      intro n
      simpa only [hm] using storage_call c st2 st1 n env (arrayField b env m2 st2 hb) (arrayField a env .Var st1 ha))

#print axioms copy
end properties.wasm_module_ok.ConstructiveBodyArrayProductions
