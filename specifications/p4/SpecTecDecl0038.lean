import SpecTecDecl0037

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$lift_typeIR:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option baseTypeIR) := match arg0 with | .VOID => some (baseTypeIR.VOID) | .BOOL => some (baseTypeIR.BOOL) | .ERROR => some (baseTypeIR.ERROR) | .MATCH_KIND => some (baseTypeIR.MATCH_KIND) | .STRING => some (baseTypeIR.STRING) | .INT => some (baseTypeIR.INT) | .«INT `< % `>» field0 => some (baseTypeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (baseTypeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (baseTypeIR.«VARBIT `< % `>» field0) | _ => none


def «$lift_typeIR:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$lift_typeIR:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option aliasTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (aliasTypeIR.TYPEDEF field0 field1) | .TYPE field0 field1 => some (aliasTypeIR.TYPE field0 field1) | _ => none


def «$lift_typeIR:case_4:downcast:0» (arg0 : typeIR) : (_root_.Option dataTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (dataTypeIR.«LIST `< % `>» field0) | .«TUPLE `< % `>» field0 => some (dataTypeIR.«TUPLE `< % `>» field0) | .«ARRAY % `[ % `]» field0 field1 => some (dataTypeIR.«ARRAY % `[ % `]» field0 field1) | .«HEADER_STACK % `[ % `]» field0 field1 => some (dataTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (dataTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (dataTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (dataTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | .«ENUM % `{ % `}» field0 field1 => some (dataTypeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (dataTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$lift_baseTypeIR:case_1:downcast:0» (arg0 : baseTypeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «$lift_baseTypeIR:case_2:downcast:0» (arg0 : baseTypeIR) : (_root_.Option errorTypeIR) := match arg0 with | .ERROR => some (errorTypeIR.ERROR) | _ => none


def «$lift_baseTypeIR:case_3:downcast:0» (arg0 : baseTypeIR) : (_root_.Option errorTypeIR) := match arg0 with | .ERROR => some (errorTypeIR.ERROR) | _ => none


def «$lift_baseTypeIR:case_4:downcast:0» (arg0 : baseTypeIR) : (_root_.Option matchKindTypeIR) := match arg0 with | .MATCH_KIND => some (matchKindTypeIR.MATCH_KIND) | _ => none


def «$lift_baseTypeIR:case_5:downcast:0» (arg0 : baseTypeIR) : (_root_.Option stringTypeIR) := match arg0 with | .STRING => some (stringTypeIR.STRING) | _ => none


def «$lift_baseTypeIR:case_6:downcast:0» (arg0 : baseTypeIR) : (_root_.Option intTypeIR) := match arg0 with | .INT => some (intTypeIR.INT) | _ => none


def «$lift_baseTypeIR:case_7:downcast:0» (arg0 : baseTypeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$lift_baseTypeIR:case_8:downcast:0» (arg0 : baseTypeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$lift_baseTypeIR:case_9:downcast:0» (arg0 : baseTypeIR) : (_root_.Option varBitTypeIR) := match arg0 with | .«VARBIT `< % `>» field0 => some (varBitTypeIR.«VARBIT `< % `>» field0) | _ => none


def «$lift_typeDefIR_as_typeName:case_1:downcast:0» (arg0 : typeDefIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$lift_typeDefIR_as_typeName:case_2:downcast:0» (arg0 : typeDefIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$lift_typeDefIR_as_typeName:case_3:downcast:0» (arg0 : typeDefIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$lift_typeDefIR_as_typeName:case_4:downcast:0» (arg0 : typeDefIR) : (_root_.Option structTypeDefIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeDefIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$lift_typeDefIR_as_typeName:case_5:downcast:0» (arg0 : typeDefIR) : (_root_.Option headerTypeDefIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeDefIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$lift_typeDefIR_as_typeName:case_6:downcast:0» (arg0 : typeDefIR) : (_root_.Option headerUnionTypeDefIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeDefIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$lift_typeDefIR_as_typeName:case_7:downcast:0» (arg0 : typeDefIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «$lift_typeDefIR_as_typeName:case_8:downcast:0» (arg0 : typeDefIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$lift_typeDefIR_as_typeName:case_9:downcast:0» (arg0 : typeDefIR) : (_root_.Option externObjectTypeDefIR) := match arg0 with | .«EXTERN % `< % ',' % `> %» field0 field1 field2 field3 => some (externObjectTypeDefIR.«EXTERN % `< % ',' % `> %» field0 field1 field2 field3) | _ => none


def «$lift_typeDefIR_as_typeName:case_10:downcast:0» (arg0 : typeDefIR) : (_root_.Option parserObjectTypeDefIR) := match arg0 with | .«PARSER % `< % ',' % `> `( % `)» field0 field1 field2 field3 => some (parserObjectTypeDefIR.«PARSER % `< % ',' % `> `( % `)» field0 field1 field2 field3) | _ => none


def «$lift_typeDefIR_as_typeName:case_11:downcast:0» (arg0 : typeDefIR) : (_root_.Option controlObjectTypeDefIR) := match arg0 with | .«CONTROL % `< % ',' % `> `( % `)» field0 field1 field2 field3 => some (controlObjectTypeDefIR.«CONTROL % `< % ',' % `> `( % `)» field0 field1 field2 field3) | _ => none


def «$lift_typeDefIR_as_typeName:case_12:downcast:0» (arg0 : typeDefIR) : (_root_.Option packageObjectTypeDefIR) := match arg0 with | .«PACKAGE % `< % ',' % `> `{ % `}» field0 field1 field2 field3 => some (packageObjectTypeDefIR.«PACKAGE % `< % ',' % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_typeDefIR_as_typeName:case_13:downcast:0» (arg0 : typeDefIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


def «$lift_aliasTypeIR:case_1:downcast:0» (arg0 : aliasTypeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$lift_aliasTypeIR:case_2:downcast:0» (arg0 : aliasTypeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$lift_dataTypeIR:case_1:downcast:0» (arg0 : dataTypeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «$lift_dataTypeIR:case_2:downcast:0» (arg0 : dataTypeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$lift_dataTypeIR:case_3:downcast:0» (arg0 : dataTypeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$lift_dataTypeIR:case_4:downcast:0» (arg0 : dataTypeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none

end SpecTec
