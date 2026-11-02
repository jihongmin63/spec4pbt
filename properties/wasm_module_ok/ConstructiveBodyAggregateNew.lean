import properties.wasm_module_ok.ConstructiveBodyAggregateMetadata
import properties.wasm_module_ok.ConstructiveBodyIndexedProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateNew
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyAggregateMetadata ConstructiveBodyIndexedProductions ConstructiveBodyProductions ConstructiveConstAggregateBuilders

def structExplicit (c : context) (stack : inferresulttype) (env : Env c) (s : StructIndex c) : Production c stack :=
  fixed c stack env (.NoEllipses,StructExplicitFieldsDecision.structFieldInputs s.fields) (.NoEllipses,[.RefT (.«% %» .NoNull (.DefHT s.definition))])
    (structInputs s env) (cons_backed .NoEllipses (structRef s .NoNull) (nil_backed c .NoEllipses))
    (.«STRUCT.NEW» s.index .Explicit) (by
      intro n
      apply ((ConstInstrDecision.struct_explicit_result_iff c stack s.index _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.structExplicitResult,structResult s,s.lookup,ConstructiveBodyControl.effect],rfl⟩)

def structImplicit (c : context) (stack : inferresulttype) (env : Env c) (s : StructIndex c)
    (hd : StructImplicitFieldsDecision.structFieldsDefaultable s.fields=true) : Production c stack :=
  fixed c stack env (.NoEllipses,[]) (.NoEllipses,[.RefT (.«% %» .NoNull (.DefHT s.definition))])
    (nil_backed c .NoEllipses) (cons_backed .NoEllipses (structRef s .NoNull) (nil_backed c .NoEllipses))
    (.«STRUCT.NEW» s.index .Implicit) (by
      intro n
      apply ((ConstInstrDecision.struct_implicit_result_iff c stack s.index _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.structImplicitResult,structResult s,s.lookup,hd,ConstructiveBodyControl.effect],rfl⟩)

def arrayExplicit (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) : Production c stack :=
  fixed c stack env (.NoEllipses,[UnpackedFieldDecision.unpackedFieldResult a.field,.NumT .I32T]) (.NoEllipses,[.RefT (.«% %» .NoNull (.DefHT a.definition))])
    (cons_backed .NoEllipses (arrayInput a env) (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))
    (cons_backed .NoEllipses (arrayRef a .NoNull) (nil_backed c .NoEllipses))
    (.«ARRAY.NEW» a.index .Explicit) (by
      intro n
      apply ((ConstInstrDecision.array_explicit_result_iff c stack a.index _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.arrayExplicitResult,arrayResult a,a.lookup,ConstructiveBodyControl.effect],rfl⟩)

def arrayImplicit (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (hd : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult a.field)=true) : Production c stack :=
  fixed c stack env (.NoEllipses,[.NumT .I32T]) (.NoEllipses,[.RefT (.«% %» .NoNull (.DefHT a.definition))])
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (arrayRef a .NoNull) (nil_backed c .NoEllipses))
    (.«ARRAY.NEW» a.index .Implicit) (by
      intro n
      apply ((ConstInstrDecision.array_implicit_result_iff c stack a.index _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.arrayImplicitResult,arrayResult a,a.lookup,hd,ConstructiveBodyControl.effect],rfl⟩)

def arrayFixed (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (count : Nat) : Production c stack :=
  fixed c stack env (.NoEllipses,MakeValidation.makeResult (UnpackedFieldDecision.unpackedFieldResult a.field) count)
    (.NoEllipses,[.RefT (.«% %» .NoNull (.DefHT a.definition))])
    (by
      rw [ConstructiveConstTableExpand.make_replicate]
      intro t ht
      have he := (List.mem_replicate.mp ht).2
      subst t
      exact arrayInput a env)
    (cons_backed .NoEllipses (arrayRef a .NoNull) (nil_backed c .NoEllipses))
    (.«ARRAY.NEW_FIXED» a.index count) (by
      intro n
      apply ((ConstInstrDecision.array_fixed_result_iff c stack a.index count _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.arrayFixedResult,arrayResult a,a.lookup,ConstructiveBodyControl.effect],rfl⟩)

/-- Arity is part of the structural size plan. The outer arbitrary natural depth
makes these plans unbounded; no AST or sampled count is checked or rejected. -/
def all (c : context) (stack : inferresulttype) (env : Env c) (bound : Nat) : List (Production c stack) :=
  ((ConstructiveConstTableSeeds.structIndices c).flatMap fun s =>
    [structExplicit c stack env s] ++
    (if hd : StructImplicitFieldsDecision.structFieldsDefaultable s.fields=true then [structImplicit c stack env s hd] else [])) ++
  ((ConstructiveConstTableSeeds.arrayIndices c).flatMap fun a =>
    [arrayExplicit c stack env a] ++
    (if hd : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult a.field)=true then [arrayImplicit c stack env a hd] else []) ++
    ((List.range (bound+1)).map fun count => arrayFixed c stack env a count))

#print axioms arrayFixed
end properties.wasm_module_ok.ConstructiveBodyAggregateNew
