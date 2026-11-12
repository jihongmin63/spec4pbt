import properties.wasm_module_ok.ConstructiveBodyAggregateMetadata
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateNewOriginal
open SpecTec properties.wasm_module_ok ConstructiveBodyAggregateMetadata ConstructiveConstAggregateBuilders

theorem structExplicit (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«STRUCT.NEW» x .Explicit)⟩)
      n (.success (.of effect)) finish) :
    ∃s : StructIndex c,s.index=x := by
  have hr := ((ConstInstrDecision.struct_explicit_result_iff c stack x effect n finish).2 ⟨rfl,h⟩).1
  cases ht : StructTypeDecision.structTypeResult c x with
  | none => simp [ConstInstrDecision.structExplicitResult,ht] at hr
  | some shape =>
    cases shape with | StructT fields =>
      obtain ⟨s,hx,hf⟩ := structResult_inverse c x fields ht
      exact ⟨s,hx⟩

theorem structImplicit (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«STRUCT.NEW» x .Implicit)⟩)
      n (.success (.of effect)) finish) :
    ∃s : StructIndex c,s.index=x ∧ StructImplicitFieldsDecision.structFieldsDefaultable s.fields=true := by
  have hr := ((ConstInstrDecision.struct_implicit_result_iff c stack x effect n finish).2 ⟨rfl,h⟩).1
  cases ht : StructTypeDecision.structTypeResult c x with
  | none => simp [ConstInstrDecision.structImplicitResult,ht] at hr
  | some shape =>
    cases shape with | StructT fields =>
      obtain ⟨s,hx,hf⟩ := structResult_inverse c x fields ht
      have hd : StructImplicitFieldsDecision.structFieldsDefaultable fields=true := by
        by_contra hn
        have hget : c.TYPES[x]?=some s.definition := by rw [←hx]; exact s.lookup
        simp [ConstInstrDecision.structImplicitResult,ht,hget,hn] at hr
      exact ⟨s,hx,by simpa only [hf] using hd⟩

theorem arrayExplicit (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.NEW» x .Explicit)⟩)
      n (.success (.of effect)) finish) :
    ∃a : ArrayIndex c,a.index=x := by
  have hr := ((ConstInstrDecision.array_explicit_result_iff c stack x effect n finish).2 ⟨rfl,h⟩).1
  cases ht : ArrayTypeDecision.arrayTypeResult c x with
  | none => simp [ConstInstrDecision.arrayExplicitResult,ht] at hr
  | some shape =>
    cases shape with | ArrayT field =>
      obtain ⟨a,hx,hf⟩ := arrayResult_inverse c x field ht
      exact ⟨a,hx⟩

theorem arrayImplicit (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.NEW» x .Implicit)⟩)
      n (.success (.of effect)) finish) :
    ∃a : ArrayIndex c,a.index=x ∧ DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult a.field)=true := by
  have hr := ((ConstInstrDecision.array_implicit_result_iff c stack x effect n finish).2 ⟨rfl,h⟩).1
  cases ht : ArrayTypeDecision.arrayTypeResult c x with
  | none => simp [ConstInstrDecision.arrayImplicitResult,ht] at hr
  | some shape =>
    cases shape with | ArrayT field =>
      obtain ⟨a,hx,hf⟩ := arrayResult_inverse c x field ht
      have hd : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult field)=true := by
        by_contra hn
        have hget : c.TYPES[x]?=some a.definition := by rw [←hx]; exact a.lookup
        simp [ConstInstrDecision.arrayImplicitResult,ht,hget,hn] at hr
      exact ⟨a,hx,by simpa only [hf] using hd⟩

theorem arrayFixed (c : context) (stack : inferresulttype) (x : Nat) (count : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.NEW_FIXED» x count)⟩)
      n (.success (.of effect)) finish) :
    ∃a : ArrayIndex c,a.index=x := by
  have hr := ((ConstInstrDecision.array_fixed_result_iff c stack x count effect n finish).2 ⟨rfl,h⟩).1
  cases ht : ArrayTypeDecision.arrayTypeResult c x with
  | none => simp [ConstInstrDecision.arrayFixedResult,ht] at hr
  | some shape =>
    cases shape with | ArrayT field =>
      obtain ⟨a,hx,hf⟩ := arrayResult_inverse c x field ht
      exact ⟨a,hx⟩

#print axioms structImplicit
#print axioms arrayFixed
end properties.wasm_module_ok.ConstructiveBodyAggregateNewOriginal
