import SpecTecDecl0055

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Cast_impl_neq:tupleTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:tupleTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «Cast_impl_neq:arrayTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:arrayTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «Cast_impl_neq:headerStackTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:headerStackTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «Cast_impl_neq:structTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:structTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Cast_impl_neq:headerTypeIR_2:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:headerTypeIR_2:downcast:1» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Cast_impl_neq:sequenceTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:sequenceTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:tupleTypeIR_2:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:tupleTypeIR_2:downcast:1» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «Cast_impl_neq:arrayTypeIR_2:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:arrayTypeIR_2:downcast:1» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «Cast_impl_neq:headerStackTypeIR_2:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:headerStackTypeIR_2:downcast:1» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «Cast_impl_neq:structTypeIR_2:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:structTypeIR_2:downcast:1» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Cast_impl_neq:headerTypeIR_3:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Cast_impl_neq:headerTypeIR_3:downcast:1» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Cast_impl_neq:structTypeIR_3:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Cast_impl_neq:structTypeIR_3:downcast:1» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Cast_impl_neq:headerTypeIR_4:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Cast_impl_neq:headerTypeIR_4:downcast:1» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Cast_impl_neq:structTypeIR_4:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Cast_impl_neq:structTypeIR_4:downcast:1» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Cast_impl_neq:headerTypeIR_5:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Cast_impl_neq:headerTypeIR_5:downcast:1» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Expr_ok:booleanLiteral:downcast:0» (arg0 : expression) : (_root_.Option booleanLiteral) := match arg0 with | .TRUE => some (booleanLiteral.TRUE) | .FALSE => some (booleanLiteral.FALSE) | _ => none


def «Expr_ok:integerLiteral-arbint:downcast:0» (arg0 : expression) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none

end SpecTec
