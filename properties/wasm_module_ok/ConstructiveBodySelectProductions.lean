import properties.wasm_module_ok.ConstructiveBodySelectCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodySelectProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyIndexedProductions ConstructiveBodySelectCalls

def plain (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (hp : plainAllowed stack=true) : Production c stack :=
  let hb := ConstructiveBodySimpleAtoms.peek_backed c stack hs 1
  fixed c stack env (.NoEllipses,[plainType stack,plainType stack,.NumT .I32T]) (.NoEllipses,[plainType stack])
    (cons_backed .NoEllipses hb (cons_backed .NoEllipses hb
      (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))))
    (cons_backed .NoEllipses hb (nil_backed c .NoEllipses)) (.SELECT none) (ConstructiveBodySelectCalls.plain c stack hp)

def typed (c : context) (stack : inferresulttype) (env : Env c) (t : valtype)
    (ht : t∈FiniteValidTypes.validCandidates c) : Production c stack :=
  let hb := CandidateValMembership.valid_candidate_in_table c t ht
  fixed c stack env (.NoEllipses,[t,t,.NumT .I32T]) (.NoEllipses,[t])
    (cons_backed .NoEllipses hb (cons_backed .NoEllipses hb
      (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))))
    (cons_backed .NoEllipses hb (nil_backed c .NoEllipses)) (.SELECT (some [t]))
    (ConstructiveBodySelectCalls.typed c stack t ((FiniteValidTypes.validCandidates_spec c t).1 ht))

def all (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) : List (Production c stack) :=
  ((FiniteValidTypes.validCandidates c).attach.map fun t => typed c stack env t.val t.property) ++
  if hp : plainAllowed stack=true then [plain c stack env hs hp] else []

#print axioms all
end properties.wasm_module_ok.ConstructiveBodySelectProductions
