import properties.wasm_module_ok.ConstructiveBodyProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyProductionCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyProductions

def Produces {c : context} {stack : inferresulttype} (p : Production c stack) (i : instr) : Prop :=
  ∃v,Gen.support p.instructions.generator v ∧ v.val=i

def Covers {c : context} {stack : inferresulttype} (ps : List (Production c stack))
    (i : instr) (effect : inferinstrtype) : Prop :=
  ∃p∈ps,p.effect=effect ∧ Produces p i

end properties.wasm_module_ok.ConstructiveBodyProductionCoverage
