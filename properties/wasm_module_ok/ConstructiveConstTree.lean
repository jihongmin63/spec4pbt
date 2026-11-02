import properties.wasm_module_ok.ConstConsumerTrace
import properties.wasm_module_ok.ConstConstructiveProducer
import properties.wasm_module_ok.ConstSyntaxSingleton
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTree
open SpecTec properties.wasm_module_ok

/-- A lossless postfix tree; the annotation records its actual produced type. -/
inductive Tree : Type where
  | node (instruction : instr) (output : valtype) (children : List Tree) : Tree

def Tree.output : Tree → valtype
  | .node _ u _ => u

def Tree.code : Tree → List instr
  | .node i _ children => children.flatMap Tree.code ++ [i]

def outputs (trees : List Tree) : List valtype := trees.map Tree.output

def effect (need : List valtype) (u : valtype) : inferinstrtype :=
  (⟨{INS := (.NoEllipses,need),OUTS := (.NoEllipses,[u])},([] : List localidx)⟩ : inferinstrtype)

/-- Primitive rules carry original typed calls. Executable construction builds
these witnesses by typed constructors; there is no validity decision here. -/
inductive Good (c : context) : Tree → Prop where
  | node (i : instr) (u : valtype) (children : List Tree) (need : List valtype)
      (hsyntax : ConstAdditionalSyntaxValidation.Syntax c i)
      (instruction : ∀ stack n,SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,stack++outputs children) i⟩)
        n (.success (.of (effect need u))) n)
      (matching : ∀ n,SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs children) need⟩)
        n (.success (.of ())) n)
      (children_good : ∀ t∈children,Good c t) : Good c (.node i u children)

private theorem forest_trace (c : context) (trees : List Tree)
    (hall : ∀ t∈trees,∀ stack n,
      ConstConstructiveTrace.Trace c (.NoEllipses,stack) t.code c
        (.NoEllipses,stack++[t.output]) n n) :
    ∀ stack n,ConstConstructiveTrace.Trace c (.NoEllipses,stack) (trees.flatMap Tree.code) c
      (.NoEllipses,stack++outputs trees) n n := by
  induction trees with
  | nil => intro stack n; simpa [outputs] using ConstConstructiveTrace.Trace.nil c (.NoEllipses,stack) n
  | cons t ts ih =>
    intro stack n
    have ht := hall t (by simp) stack n
    have htail := ih (fun t ht => hall t (by simp [ht])) (stack++[t.output]) n
    simpa [outputs,List.append_assoc] using ConstConstructiveTrace.trace_append ht htail

/-- Every completed tree executes above any existing stack without changing
that prefix or local context. Original instruction ordering and supply remain. -/
theorem tree_trace (c : context) (tree : Tree) (h : Good c tree) :
    ∀ stack n,ConstConstructiveTrace.Trace c (.NoEllipses,stack) tree.code c
      (.NoEllipses,stack++[tree.output]) n n := by
  induction h with
  | node i u children need hsyntax hinstr hmatch hchildren ih =>
    intro stack n
    have hk := forest_trace c children ih stack n
    have hlen := ((MatchResulttypeValidation.match_resulttype_success_iff c
      (outputs children) need n n).1 (hmatch n)).1
    simpa only [Tree.code,Tree.output] using
      ConstConsumerTrace.trace_snoc_after_operands stack (outputs children) need u i hk
        (hinstr stack n) hlen (hmatch n)

theorem tree_syntax (c : context) (tree : Tree) (h : Good c tree) :
    ∀ i∈tree.code,ConstSyntaxDecision.syntaxAllowed c i=true := by
  induction h with
  | node i u children need hsyntax _ _ hchildren ih =>
    intro j hj
    simp only [Tree.code,List.mem_append,List.mem_singleton] at hj
    rcases hj with hj | rfl
    · obtain ⟨t,ht,hj⟩ := List.mem_flatMap.1 hj
      exact ih t ht j hj
    · exact (ConstSyntaxDecision.syntaxAllowed_iff c _).2 hsyntax

theorem tree_const_ok (c : context) (tree : Tree) (h : Good c tree) (target : valtype)
    (n : Nat)
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c [tree.output] [target]⟩)
      n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target tree.code⟩)
      n (.success (.of ())) n := by
  apply (ConstDecisionTrace.const_ok_decision_trace_iff c target tree.code n n).2
  refine ⟨tree_syntax c tree h,(.NoEllipses,[tree.output]),[],.NoEllipses,n,?_,?_⟩
  · exact ConstConstructiveTrace.trace_to_instrs (by simpa using tree_trace c tree h [] n)
  · exact ConstSingletonFinalPop.singleton_final_pop_of_match_resulttype c tree.output target n hmatch

/-- Backward parsing groups the existing suffix. It never changes, repairs or
normalizes an original instruction. This operation is not a candidate search. -/
def attach (forest : List Tree) (need : Nat) (i : instr) (u : valtype) : List Tree :=
  forest.take (forest.length-need) ++ [.node i u (forest.drop (forest.length-need))]

theorem attach_code (forest : List Tree) (need : Nat) (i : instr) (u : valtype) :
    (attach forest need i u).flatMap Tree.code=forest.flatMap Tree.code++[i] := by
  simp only [attach,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,Tree.code]
  rw [←List.append_assoc,←List.flatMap_append,List.take_append_drop]

theorem attach_outputs (forest : List Tree) (need : Nat) (i : instr) (u : valtype) :
    outputs (attach forest need i u)=
      (outputs forest).take ((outputs forest).length-need)++[u] := by
  simp [attach,outputs,Tree.output,List.map_take]

#print axioms tree_const_ok
#print axioms attach_code
end properties.wasm_module_ok.ConstructiveConstTree
