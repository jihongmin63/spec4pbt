import properties.wasm_module_ok.ConstructiveBodyAggregateBind
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateAccessOriginal
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEvalReduction ConstructiveBodyAggregateBind ConstructiveBodyAggregateCatalog ConstructiveBodyStorageMetadata

theorem structGetSome (c : context) (stack : inferresulttype) (x y : Nat) (ext : extension) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.GET» x y (some ext))⟩) n (.success (.of effect)) finish) :
    ∃f : StructField c,f.owner.index=x ∧ f.entry.index=y ∧ packed f.storage=true := by
  have hs := (ConstructiveBodyGetDispatch.structSome c stack x y ext effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:61» c stack (.«STRUCT.GET» x y (some ext))) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:61» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨owner,hx,hs⟩ := struct_bind c x _ n finish (.of effect) hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hf : owner.fields[y]? with
  | none => rw [hf] at hs; cases hs
  | some value =>
    cases value with | FieldT mutability storage =>
      simp only [hf] at hs
      rw [bind_known _ _ _ _ _ _ (packed_call storage n)] at hs
      obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
      exact ⟨⟨owner,⟨y,.FieldT mutability storage,hf⟩,mutability,storage,rfl⟩,hx,rfl,hp⟩

theorem structGetNone (c : context) (stack : inferresulttype) (x y : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.GET» x y none)⟩) n (.success (.of effect)) finish) :
    ∃f : StructField c,f.owner.index=x ∧ f.entry.index=y ∧ ¬packed f.storage=true := by
  have hs := (ConstructiveBodyGetDispatch.structNone c stack x y effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:62» c stack (.«STRUCT.GET» x y none)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:62» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨owner,hx,hs⟩ := struct_bind c x _ n finish (.of effect) hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hf : owner.fields[y]? with
  | none => rw [hf] at hs; cases hs
  | some value =>
    cases value with | FieldT mutability storage =>
      simp only [hf] at hs
      rw [bind_known _ _ _ _ _ _ (packed_call storage n)] at hs
      obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
      exact ⟨⟨owner,⟨y,.FieldT mutability storage,hf⟩,mutability,storage,rfl⟩,hx,rfl,hp⟩

theorem structSet (c : context) (stack : inferresulttype) (x y : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.SET» x y)⟩) n (.success (.of effect)) finish) :
    ∃f : StructField c,f.owner.index=x ∧ f.entry.index=y ∧ f.mutability=.Var := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«STRUCT.SET» x y) 63 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:63» c stack (.«STRUCT.SET» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:63» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨owner,hx,hs⟩ := struct_bind c x _ n finish (.of effect) hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hf : owner.fields[y]? with
  | none => rw [hf] at hs; cases hs
  | some value =>
    cases value with | FieldT mutability storage =>
      simp only [hf] at hs
      obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
      exact ⟨⟨owner,⟨y,.FieldT mutability storage,hf⟩,mutability,storage,rfl⟩,hx,rfl,hp.symm⟩

theorem arrayGetSome (c : context) (stack : inferresulttype) (x : Nat) (ext : extension) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.GET» x (some ext))⟩) n (.success (.of effect)) finish) :
    ∃f : ArrayField c,f.owner.index=x ∧ packed f.storage=true := by
  have hs := (ConstructiveBodyGetDispatch.arraySome c stack x ext effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:69» c stack (.«ARRAY.GET» x (some ext))) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:69» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨owner,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  cases hf : owner.field with | FieldT mutability storage =>
    rw [hf] at hs
    rw [bind_known _ _ _ _ _ _ (packed_call storage n)] at hs
    obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
    exact ⟨⟨owner,mutability,storage,hf⟩,hx,hp⟩

theorem arrayGetNone (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.GET» x none)⟩) n (.success (.of effect)) finish) :
    ∃f : ArrayField c,f.owner.index=x ∧ ¬packed f.storage=true := by
  have hs := (ConstructiveBodyGetDispatch.arrayNone c stack x effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:70» c stack (.«ARRAY.GET» x none)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:70» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨owner,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  cases hf : owner.field with | FieldT mutability storage =>
    rw [hf] at hs
    rw [bind_known _ _ _ _ _ _ (packed_call storage n)] at hs
    obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
    exact ⟨⟨owner,mutability,storage,hf⟩,hx,hp⟩

theorem arraySet (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.SET» x)⟩) n (.success (.of effect)) finish) :
    ∃f : ArrayField c,f.owner.index=x ∧ f.mutability=.Var := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.SET» x) 71 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:71» c stack (.«ARRAY.SET» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:71» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨owner,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  cases hf : owner.field with | FieldT mutability storage =>
    rw [hf] at hs
    obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
    have hm : mutability=.Var := by
      cases mutability with
      | Cons => cases hp
      | Var => rfl
    exact ⟨⟨owner,mutability,storage,hf⟩,hx,hm⟩

theorem arrayFill (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.FILL» x)⟩) n (.success (.of effect)) finish) :
    ∃f : ArrayField c,f.owner.index=x ∧ f.mutability=.Var := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.FILL» x) 74 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:74» c stack (.«ARRAY.FILL» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:74» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨owner,hx,hs⟩ := array_bind c x _ n finish (.of effect) hs
  cases hf : owner.field with | FieldT mutability storage =>
    rw [hf] at hs
    obtain ⟨hp,_⟩ := (bind_guard _ _ _ _ _).1 hs
    exact ⟨⟨owner,mutability,storage,hf⟩,hx,hp.symm⟩

#print axioms arrayFill
end properties.wasm_module_ok.ConstructiveBodyAggregateAccessOriginal
