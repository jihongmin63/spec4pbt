import properties.wasm_module_ok.ConstructiveBodyAggregateBind
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyArrayBulkOriginal
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyAggregateBind ConstructiveBodyEvalReduction ConstructiveBodyAggregateMetadata ConstructiveBodyAggregateCatalog ConstructiveBodyStorageMetadata ConstructiveBodyAggregateProductions ConstructiveBodyTypeClassifiers ConstructiveConstAggregateBuilders

theorem newElem (c : context) (stack : inferresulttype) (env : ConstructiveBodyEnvironment.Env c) (x y : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.NEW_ELEM» x y)⟩) n (.success (.of effect)) finish) :
    ∃(a : ArrayIndex c) (e : ConstructiveBodyLookup.Entry c.ELEMS),a.index=x ∧ e.index=y ∧ CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedFieldResult a.field)=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.NEW_ELEM» x y) 67 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:67» c stack (.«ARRAY.NEW_ELEM» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:67» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨a,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hy : c.ELEMS[y]? with
  | none => rw [hy] at hs; cases hs
  | some value =>
    rw [hy] at hs
    rw [bind_known _ _ _ _ _ _ (UnpackedFieldDecision.unpacked_field_total a.field n)] at hs
    rw [bind_known _ _ _ _ _ _ (CandidateValMatch.candidate_val_match_total c (.RefT value) (UnpackedFieldDecision.unpackedFieldResult a.field) n env.ready
      (env.elems value (List.mem_iff_getElem?.mpr ⟨y,hy⟩)) (arrayInput a env))] at hs
    obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
    exact ⟨a,⟨y,value,hy⟩,hx,rfl,hp⟩

theorem newData (c : context) (stack : inferresulttype) (env : ConstructiveBodyEnvironment.Env c) (x y : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.NEW_DATA» x y)⟩) n (.success (.of effect)) finish) :
    ∃(a : ArrayIndex c) (e : ConstructiveBodyLookup.Entry c.DATAS),a.index=x ∧ e.index=y ∧ ConstructiveBodyArrayProductions.numericStorage (UnpackedFieldDecision.unpackedFieldResult a.field)=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.NEW_DATA» x y) 68 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:68» c stack (.«ARRAY.NEW_DATA» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:68» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨a,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hy : c.DATAS[y]? with
  | none => rw [hy] at hs; cases hs
  | some value =>
    rw [hy] at hs
    cases value
    obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
    rw [bind_known _ _ _ _ _ _ (UnpackedFieldDecision.unpacked_field_total a.field n)] at hs
    rw [bind_known _ _ _ _ _ _ (numeric_total (UnpackedFieldDecision.unpackedFieldResult a.field) n)] at hs
    rw [bind_known _ _ _ _ _ _ (vector_total (UnpackedFieldDecision.unpackedFieldResult a.field) n)] at hs
    obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
    exact ⟨a,⟨y,.OK,hy⟩,hx,rfl,Bool.or_eq_true_iff.mpr hp⟩

theorem initData (c : context) (stack : inferresulttype) (env : ConstructiveBodyEnvironment.Env c) (x y : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.INIT_DATA» x y)⟩) n (.success (.of effect)) finish) :
    ∃(f : ArrayField c) (e : ConstructiveBodyLookup.Entry c.DATAS),f.owner.index=x ∧ e.index=y ∧ f.mutability=.Var ∧ ConstructiveBodyArrayProductions.numericStorage (UnpackedFieldDecision.unpackedStorageResult f.storage)=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.INIT_DATA» x y) 75 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:75» c stack (.«ARRAY.INIT_DATA» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:75» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨a,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  cases hf : a.field with | FieldT mutability storage =>
    rw [hf] at hs
    obtain ⟨hm,hs⟩ := (bind_guard _ _ _ _ _).1 hs
    have hm : mutability=.Var := hm.symm
    obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
    cases hy : c.DATAS[y]? with
    | none => rw [hy] at hs; cases hs
    | some value =>
      rw [hy] at hs
      cases value
      obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
      rw [bind_known _ _ _ _ _ _ (UnpackedFieldDecision.unpacked_storage_total storage n)] at hs
      rw [bind_known _ _ _ _ _ _ (numeric_total (UnpackedFieldDecision.unpackedStorageResult storage) n)] at hs
      rw [bind_known _ _ _ _ _ _ (vector_total (UnpackedFieldDecision.unpackedStorageResult storage) n)] at hs
      obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
      exact ⟨⟨a,mutability,storage,hf⟩,⟨y,.OK,hy⟩,hx,rfl,hm,Bool.or_eq_true_iff.mpr hp⟩

theorem initElem (c : context) (stack : inferresulttype) (env : ConstructiveBodyEnvironment.Env c) (x y : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.INIT_ELEM» x y)⟩) n (.success (.of effect)) finish) :
    ∃(f : ArrayField c) (e : ConstructiveBodyLookup.Entry c.ELEMS),f.owner.index=x ∧ e.index=y ∧ f.mutability=.Var ∧ CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedStorageResult f.storage)=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.INIT_ELEM» x y) 76 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:76» c stack (.«ARRAY.INIT_ELEM» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:76» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨a,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  cases hf : a.field with | FieldT mutability storage =>
    rw [hf] at hs
    obtain ⟨hm,hs⟩ := (bind_guard _ _ _ _ _).1 hs
    have hm : mutability=.Var := hm.symm
    obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
    cases hy : c.ELEMS[y]? with
    | none => rw [hy] at hs; cases hs
    | some value =>
      rw [hy] at hs
      rw [bind_known _ _ _ _ _ _ (UnpackedFieldDecision.unpacked_storage_total storage n)] at hs
      rw [bind_known _ _ _ _ _ _ (CandidateValMatch.candidate_val_match_total c (.RefT value) (UnpackedFieldDecision.unpackedStorageResult storage) n env.ready
        (env.elems value (List.mem_iff_getElem?.mpr ⟨y,hy⟩)) (arrayField a env mutability storage hf))] at hs
      obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
      exact ⟨⟨a,mutability,storage,hf⟩,⟨y,value,hy⟩,hx,rfl,hm,hp⟩

theorem copy (c : context) (stack : inferresulttype) (env : ConstructiveBodyEnvironment.Env c) (x y : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.COPY» x y)⟩) n (.success (.of effect)) finish) :
    ∃f g : ArrayField c,f.owner.index=x ∧ g.owner.index=y ∧ f.mutability=.Var ∧ storageMatch c g.storage f.storage=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.COPY» x y) 73 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:73» c stack (.«ARRAY.COPY» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:73» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨a,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  cases ha : a.field with | FieldT m1 st1 =>
    rw [ha] at hs
    obtain ⟨b,hy,hs⟩ := array_bind c y _ n finish (.of effect) hs
    cases hb : b.field with | FieldT m2 st2 =>
      rw [hb] at hs
      obtain ⟨hm,hs⟩ := (bind_guard _ _ _ _ _).1 hs
      have hm : m1=.Var := hm.symm
      rw [bind_known _ _ _ _ _ _ (storage_call c st2 st1 n env (arrayField b env m2 st2 hb) (arrayField a env m1 st1 ha))] at hs
      obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
      exact ⟨⟨a,m1,st1,ha⟩,⟨b,m2,st2,hb⟩,hx,hy,hm,hp⟩

#print axioms copy
end properties.wasm_module_ok.ConstructiveBodyArrayBulkOriginal
