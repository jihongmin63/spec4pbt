import SpecTecDecl0029

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$cast_bool:case_4:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$cast_bool:case_5:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_int:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «$cast_int:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «$cast_int:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option intTypeIR) := match arg0 with | .INT => some (intTypeIR.INT) | _ => none


def «$cast_int:case_4:downcast:0» (arg0 : typeIR) : (_root_.Option intTypeIR) := match arg0 with | .INT => some (intTypeIR.INT) | _ => none


def «$cast_int:case_5:downcast:0» (arg0 : typeIR) : (_root_.Option intTypeIR) := match arg0 with | .INT => some (intTypeIR.INT) | _ => none


def «$cast_int:case_6:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$cast_int:case_7:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$cast_int:case_8:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$cast_int:case_9:downcast:0» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$cast_int:case_10:downcast:0» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$cast_int:case_11:downcast:0» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$cast_int:case_12:downcast:0» (arg0 : typeIR) : (_root_.Option varBitTypeIR) := match arg0 with | .«VARBIT `< % `>» field0 => some (varBitTypeIR.«VARBIT `< % `>» field0) | _ => none


def «$cast_int:case_13:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$cast_int:case_14:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$cast_int:case_15:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$cast_int:case_16:downcast:0» (arg0 : typeIR) : (_root_.Option enumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (enumTypeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (enumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_int:case_17:downcast:0» (arg0 : typeIR) : (_root_.Option enumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (enumTypeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (enumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_int:case_18:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_int:case_19:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_int:case_20:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_error:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option errorTypeIR) := match arg0 with | .ERROR => some (errorTypeIR.ERROR) | _ => none


def «$cast_error:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_string:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option stringTypeIR) := match arg0 with | .STRING => some (stringTypeIR.STRING) | _ => none


def «$cast_list:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «$cast_tuple:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$cast_tuple:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_array:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$cast_header_stack:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$cast_struct:case_1:downcast:2» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_header:case_1:downcast:2» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none

end SpecTec
