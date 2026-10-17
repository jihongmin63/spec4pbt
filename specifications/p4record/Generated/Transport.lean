import Lean
import «specifications».«p4record».«Generated».«Spec»

set_option autoImplicit false
set_option linter.unusedVariables false

namespace «P4Observation»



private abbrev requiredToJson0 : _root_.Lean.ToJson (_root_.Int) := inferInstance
private abbrev requiredFromJson0 : _root_.Lean.FromJson (_root_.Int) := inferInstance

abbrev Type0 := _root_.Int
abbrev Type1 := _root_.SpecTec.«result»
noncomputable abbrev Relation0 := _root_.SpecTec.«Eval»

end «P4Observation»
