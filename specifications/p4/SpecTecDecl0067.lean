import SpecTecDecl0066

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$compat_concat:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_concat:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_concat:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_concat:matches:5:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_concat:matches:6:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_concat:matches:7:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «$result_concat:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option stringTypeIR) := match arg0 with | .STRING => some (stringTypeIR.STRING) | _ => none


def «$result_concat:case_1:downcast:1» (arg0 : typeIR) : (_root_.Option stringTypeIR) := match arg0 with | .STRING => some (stringTypeIR.STRING) | _ => none


def «$result_concat:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$result_concat:case_2:downcast:1» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$result_concat:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$result_concat:case_3:downcast:1» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$result_concat:case_4:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$result_concat:case_4:downcast:1» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$result_concat:case_5:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$result_concat:case_5:downcast:1» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$result_concat:case_6:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$result_concat:case_7:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$compat_logical:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.BOOL, typeIR.BOOL => 0
  | _, _ => 1


def «$compat_logical:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_logical:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_logical:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «$compat_array_index:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | _ => 1


def «$compat_array_index:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$compat_array_index:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$compat_array_index:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$compat_array_index:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$compat_bitslice_base:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | _ => 1


def «$compat_bitslice_base:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$compat_bitslice_base:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$compat_bitslice_base:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$compat_bitslice_base:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0

end SpecTec
