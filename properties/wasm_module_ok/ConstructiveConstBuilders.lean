import properties.wasm_module_ok.ConstructiveConstTreeTarget
import properties.wasm_module_ok.ConstNumericConsumer
import properties.wasm_module_ok.ConstRefFuncCombined
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstBuilders
open SpecTec properties.wasm_module_ok ConstructiveConstTree

abbrev Typed (c : context) (u : valtype) := {tree : Tree // Good c tree ∧ tree.output=u}
abbrev Witness (c : context) := {tree : Tree // Good c tree}

def number (c : context) (v : num_) : Typed c (.NumT (ConstLiteralEffect.numericType v)) :=
  ⟨.node (.CONST v) (.NumT (ConstLiteralEffect.numericType v)) [],by
    refine ⟨Good.node _ _ _ [] (.num v) ?_ ?_ (by simp),rfl⟩
    · intro stack n
      exact ConstLiteralDispatch.const_dispatch_total c _ v n
    · exact MatchResulttypeValidation.match_resulttype_nil_total c⟩

def vector (c : context) (v : vec_) : Typed c (.VecT .V128T) :=
  ⟨.node (.«VEC.CONST» v) (.VecT .V128T) [],by
    refine ⟨Good.node _ _ _ [] (.vec v) ?_ ?_ (by simp),rfl⟩
    · intro stack n
      exact ConstVectorDispatch.vec_dispatch_total c _ v n
    · exact MatchResulttypeValidation.match_resulttype_nil_total c⟩

def nullRef (c : context) (ht : heaptype) (hh : HeaptypeValidation.heaptypeValid c ht=true) :
    Typed c (.RefT (.«% %» .Null ht)) :=
  ⟨.node (.«REF.NULL» ht) (.RefT (.«% %» .Null ht)) [],by
    refine ⟨Good.node _ _ _ [] (.refNull ht) ?_ ?_ (by simp),rfl⟩
    · intro stack n
      exact ConstRefNullDispatch.ref_null_dispatch_total c _ ht n hh
    · exact MatchResulttypeValidation.match_resulttype_nil_total c⟩

def funcRef (c : context) (x : Nat) (dt : deftype)
    (hx : c.FUNCS[x]?=some dt) (hr : FreeUnionValidation.HasFunc c.REFS x) :
    Typed c (.RefT (.«% %» .NoNull (.DefHT dt))) :=
  ⟨.node (.«REF.FUNC» x) (.RefT (.«% %» .NoNull (.DefHT dt))) [],by
    refine ⟨Good.node _ _ _ [] (.refFunc x) ?_ ?_ (by simp),rfl⟩
    · intro stack n
      exact ((ConstRefFuncCombined.ref_func_constant_instruction_iff c _ x _ n n).2
        ⟨dt,hx,hr,rfl,rfl⟩).2
    · exact MatchResulttypeValidation.match_resulttype_nil_total c⟩

def global (c : context) (x : Nat) (u : valtype) (hx : c.GLOBALS[x]?=some (.GlobalT .Cons u)) :
    Typed c u :=
  ⟨.node (.«GLOBAL.GET» x) u [],by
    refine ⟨Good.node _ _ _ [] (.globalGet x u hx) ?_ ?_ (by simp),rfl⟩
    · intro stack n
      exact ConstGlobalGetDispatch.global_get_dispatch_total c _ x .Cons u n hx
    · exact MatchResulttypeValidation.match_resulttype_nil_total c⟩

def i31 (c : context) (child : Typed c (.NumT .I32T)) : Typed c (.RefT (.«% %» .NoNull .I31HT)) :=
  ⟨.node .«REF.I31» (.RefT (.«% %» .NoNull .I31HT)) [child.val],by
    refine ⟨Good.node _ _ _ [.NumT .I32T] .refI31 ?_ ?_ ?_,rfl⟩
    · intro stack n
      exact ConstI31Dispatch.i31_dispatch_total c _ n
    · intro n
      simpa [outputs,child.property.2] using ConstNumericConsumer.match_numeric_singleton c .I32T n
    · intro t ht
      have he : t=child.val := by simpa using ht
      simpa only [he] using child.property.1⟩

/-- The metadata supplies a typed numeric operator; neither operand is
sampled as a candidate requiring later validation. -/
def arithmetic (c : context) (op : binop_)
    (hop : .BINOP op∈ConstArithmeticValidation.arithmeticOps)
    (a b : Typed c (.NumT (ConstInstrDecision.arithmeticType op))) :
    Typed c (.NumT (ConstInstrDecision.arithmeticType op)) :=
  ⟨.node (.BINOP op) (.NumT (ConstInstrDecision.arithmeticType op)) [a.val,b.val],by
    refine ⟨Good.node _ _ _ [.NumT (ConstInstrDecision.arithmeticType op),.NumT (ConstInstrDecision.arithmeticType op)]
      (.arithmetic (.BINOP op) hop) ?_ ?_ ?_,rfl⟩
    · intro stack n
      apply ((ConstInstrDecision.arithmetic_result_iff c _ op _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.arithmeticResult,hop,effect],rfl⟩
    · intro n
      simpa [outputs,a.property.2,b.property.2] using
        ConstNumericConsumer.match_numeric_pair c (ConstInstrDecision.arithmeticType op) n
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · exact a.property.1
      · exact b.property.1⟩

#print axioms number
#print axioms arithmetic
end properties.wasm_module_ok.ConstructiveConstBuilders
