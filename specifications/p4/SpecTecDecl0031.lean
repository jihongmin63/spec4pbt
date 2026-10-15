import SpecTecDecl0030

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$cast_header_union:case_1:downcast:2» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_enum:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «$cast_enum:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_enum:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_sequence:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_sequence:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «$cast_sequence:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$cast_sequence:case_4:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «$cast_sequence:case_5:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$cast_sequence:case_6:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$cast_sequence:case_7:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_sequence:case_8:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_sequence:case_9:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «$cast_sequence:case_10:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$cast_sequence:case_11:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$cast_sequence:case_12:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$cast_sequence:case_13:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_sequence:case_14:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_record:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_record:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_record:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$cast_record:case_4:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$cast_record:case_5:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_record:case_6:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_invalid_header:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_invalid_header:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_set:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_set:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$cast_set:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$sizeof_minSizeInBits':case_1:downcast:0» (arg0 : typeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «$sizeof_minSizeInBits':case_2:downcast:0» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$sizeof_minSizeInBits':case_3:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none

end SpecTec
