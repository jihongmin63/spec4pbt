import properties.wasm_module_ok.ConstructiveConstBuilders
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open SpecTec properties.wasm_module_ok ConstructiveConstTree
open properties.wasm_module_ok.ConstructiveConstBuilders

/-- Operands already have executable completed trees and ordered typing. -/
structure Operands (c : context) (need : List valtype) where
  trees : List Tree
  good : ∀ t∈trees,Good c t
  matching : ∀ n,SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs trees) need⟩)
    n (.success (.of ())) n

def emptyOperands (c : context) : Operands c [] :=
  ⟨[],by simp,MatchResulttypeValidation.match_resulttype_nil_total c⟩

structure StructIndex (c : context) where
  index : Nat
  definition : deftype
  fields : List fieldtype
  lookup : c.TYPES[index]?=some definition
  expansion : UnrollInterface.expandResult definition=some (.DefStructT (.StructT fields))
structure ArrayIndex (c : context) where
  index : Nat
  definition : deftype
  field : fieldtype
  lookup : c.TYPES[index]?=some definition
  expansion : UnrollInterface.expandResult definition=some (.DefArrayT (.ArrayT field))

/-- Original calls are used only as erased proofs. The executable constructor
contains just the supplied instruction, type, and existing child trees. -/
def independentNode (c : context) (i : instr) (u : valtype) (need : List valtype)
    (args : Operands c need) (hs : ConstAdditionalSyntaxValidation.Syntax c i)
    (hi : ∀ irt n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c irt i⟩)
      n (.success (.of (effect need u))) n) : Typed c u :=
  ⟨.node i u args.trees,⟨Good.node i u args.trees need hs (fun _ n => hi _ n) args.matching args.good,rfl⟩⟩

def structExplicit (c : context) (index : StructIndex c)
    (args : Operands c (StructExplicitFieldsDecision.structFieldInputs index.fields)) :
    Typed c (.RefT (.«% %» .NoNull (.DefHT index.definition))) :=
  independentNode c (.«STRUCT.NEW» index.index .Explicit) _ _ args (.structNew _ _) (by
    intro irt n
    apply ((ConstInstrDecision.struct_explicit_result_iff c irt index.index _ n n).1 ?_).2
    exact ⟨by simp [ConstInstrDecision.structExplicitResult,StructTypeDecision.structTypeResult,
      index.lookup,index.expansion,effect],rfl⟩)

def structImplicit (c : context) (index : StructIndex c)
    (hdefault : StructImplicitFieldsDecision.structFieldsDefaultable index.fields=true) :
    Typed c (.RefT (.«% %» .NoNull (.DefHT index.definition))) :=
  independentNode c (.«STRUCT.NEW» index.index .Implicit) _ [] (emptyOperands c) (.structNew _ _) (by
    intro irt n
    apply ((ConstInstrDecision.struct_implicit_result_iff c irt index.index _ n n).1 ?_).2
    exact ⟨by simp [ConstInstrDecision.structImplicitResult,StructTypeDecision.structTypeResult,
      index.lookup,index.expansion,hdefault,effect],rfl⟩)

def arrayExplicit (c : context) (index : ArrayIndex c)
    (args : Operands c [UnpackedFieldDecision.unpackedFieldResult index.field,.NumT .I32T]) :
    Typed c (.RefT (.«% %» .NoNull (.DefHT index.definition))) :=
  independentNode c (.«ARRAY.NEW» index.index .Explicit) _ _ args (.arrayNew _ _) (by
    intro irt n
    apply ((ConstInstrDecision.array_explicit_result_iff c irt index.index _ n n).1 ?_).2
    exact ⟨by simp [ConstInstrDecision.arrayExplicitResult,ArrayTypeDecision.arrayTypeResult,
      index.lookup,index.expansion,effect],rfl⟩)

def arrayImplicit (c : context) (index : ArrayIndex c)
    (hdefault : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult index.field)=true)
    (args : Operands c [.NumT .I32T]) :
    Typed c (.RefT (.«% %» .NoNull (.DefHT index.definition))) :=
  independentNode c (.«ARRAY.NEW» index.index .Implicit) _ _ args (.arrayNew _ _) (by
    intro irt n
    apply ((ConstInstrDecision.array_implicit_result_iff c irt index.index _ n n).1 ?_).2
    exact ⟨by simp [ConstInstrDecision.arrayImplicitResult,ArrayTypeDecision.arrayTypeResult,
      index.lookup,index.expansion,hdefault,effect],rfl⟩)

def arrayFixed (c : context) (index : ArrayIndex c) (count : Nat)
    (args : Operands c (MakeValidation.makeResult (UnpackedFieldDecision.unpackedFieldResult index.field) count)) :
    Typed c (.RefT (.«% %» .NoNull (.DefHT index.definition))) :=
  independentNode c (.«ARRAY.NEW_FIXED» index.index count) _ _ args (.arrayNewFixed _ _) (by
    intro irt n
    apply ((ConstInstrDecision.array_fixed_result_iff c irt index.index count _ n n).1 ?_).2
    exact ⟨by simp [ConstInstrDecision.arrayFixedResult,ArrayTypeDecision.arrayTypeResult,
      index.lookup,index.expansion,effect],rfl⟩)

def externConvert (c : context) (op : externop_) (nu : null) (ht : heaptype)
    (child : Typed c (.RefT (.«% %» nu ht)))
    (hm : ∀ n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c [.RefT (.«% %» nu ht)]
        [.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1)]⟩)
      n (.success (.of ())) n) :
    Typed c (.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).2)) :=
  ⟨.node (.«EXTERN.CONVERT» op) _ [child.val],by
    refine ⟨Good.node _ _ _ [.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1)]
      (.externConvert op) ?_ ?_ ?_,rfl⟩
    · intro stack n
      apply ((ConstInstrDecision.extern_convert_result_iff c _ op _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.externConvertResult,PeekDecision.peekResult,
        PeekRefDecision.peekRefResult,outputs,child.property.2,effect],rfl⟩
    · intro n
      simpa [outputs,child.property.2] using hm n
    · intro t ht
      have he : t=child.val := by simpa using ht
      simpa only [he] using child.property.1⟩

def externBottom (c : context) (op : externop_) (child : Typed c .BotT)
    (hm : ∀ n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c [.BotT]
        [.RefT (.«% %» .NoNull (ExternopTypeDecision.typeExternopResult op).1)]⟩)
      n (.success (.of ())) n) :
    Typed c (.RefT (.«% %» .NoNull (ExternopTypeDecision.typeExternopResult op).2)) :=
  ⟨.node (.«EXTERN.CONVERT» op) _ [child.val],by
    refine ⟨Good.node _ _ _ [.RefT (.«% %» .NoNull (ExternopTypeDecision.typeExternopResult op).1)]
      (.externConvert op) ?_ ?_ ?_,rfl⟩
    · intro stack n
      apply ((ConstInstrDecision.extern_convert_result_iff c _ op _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.externConvertResult,PeekDecision.peekResult,
        PeekRefDecision.peekRefResult,outputs,child.property.2,effect],rfl⟩
    · intro n
      simpa [outputs,child.property.2] using hm n
    · intro t ht
      have he : t=child.val := by simpa using ht
      simpa only [he] using child.property.1⟩

#print axioms structExplicit
#print axioms arrayFixed
#print axioms externConvert
end properties.wasm_module_ok.ConstructiveConstAggregateBuilders
