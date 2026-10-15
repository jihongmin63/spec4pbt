import SpecTecDecl0028

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Type_alpha:default_2:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Type_alpha:default_2:downcast:1» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Type_alpha:setTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «Type_alpha:setTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «Type_alpha:tableMetadataTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option tableMetadataTypeIR) := match arg0 with | .«TABLE_ENUM % `{ % `}» field0 field1 => some (tableMetadataTypeIR.«TABLE_ENUM % `{ % `}» field0 field1) | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (tableMetadataTypeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none


def «Type_alpha:tableMetadataTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option tableMetadataTypeIR) := match arg0 with | .«TABLE_ENUM % `{ % `}» field0 field1 => some (tableMetadataTypeIR.«TABLE_ENUM % `{ % `}» field0 field1) | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (tableMetadataTypeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none


def «ExternMethodTypeDef_alpha:rule:downcast:6» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «ExternMethodTypeDef_alpha:rule:downcast:8» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «ExternMethodTypeDef_alpha:rule:downcast:12» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «ExternMethodTypeDef_alpha:rule:downcast:14» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «$default:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «$default:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option errorTypeIR) := match arg0 with | .ERROR => some (errorTypeIR.ERROR) | _ => none


def «$default:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option stringTypeIR) := match arg0 with | .STRING => some (stringTypeIR.STRING) | _ => none


def «$default:case_4:downcast:0» (arg0 : typeIR) : (_root_.Option intTypeIR) := match arg0 with | .INT => some (intTypeIR.INT) | _ => none


def «$default:case_5:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$default:case_6:downcast:0» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$default:case_7:downcast:0» (arg0 : typeIR) : (_root_.Option varBitTypeIR) := match arg0 with | .«VARBIT `< % `>» field0 => some (varBitTypeIR.«VARBIT `< % `>» field0) | _ => none


def «$default:case_8:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$default:case_9:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$default:case_10:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$default:case_11:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$default:case_12:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$default:case_13:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$default:case_14:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$default:case_15:downcast:0» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$default:case_16:downcast:0» (arg0 : typeIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «$default:case_17:downcast:0» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$default:case_18:downcast:0» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_to_enum:case_1:downcast:0» (arg0 : enumTypeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$cast_bool:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «$cast_bool:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$cast_bool:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none

end SpecTec
