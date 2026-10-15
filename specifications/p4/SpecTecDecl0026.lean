import SpecTecDecl0025

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$free_callableTypeIR:case_7:downcast:0» (arg0 : callableTypeIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «$free_callableTypeIR:case_8:downcast:0» (arg0 : callableTypeIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «$free_callableTypeIR:case_9:downcast:0» (arg0 : callableTypeIR) : (_root_.Option tableApplyMethodTypeIR) := match arg0 with | .«TABLE_APPLY ':' %» field0 => some (tableApplyMethodTypeIR.«TABLE_APPLY ':' %» field0) | _ => none


abbrev theta : Type := (map typeId typeIR)


def «$subst_typeIR':case_1:downcast:0» (arg0 : typeIR) : (_root_.Option baseTypeIR) := match arg0 with | .VOID => some (baseTypeIR.VOID) | .BOOL => some (baseTypeIR.BOOL) | .ERROR => some (baseTypeIR.ERROR) | .MATCH_KIND => some (baseTypeIR.MATCH_KIND) | .STRING => some (baseTypeIR.STRING) | .INT => some (baseTypeIR.INT) | .«INT `< % `>» field0 => some (baseTypeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (baseTypeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (baseTypeIR.«VARBIT `< % `>» field0) | _ => none


def «$subst_typeIR':case_2:downcast:0» (arg0 : typeIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$subst_typeIR':case_3:downcast:0» (arg0 : typeIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$subst_typeIR':case_4:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$subst_typeIR':case_5:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$subst_typeIR':case_6:downcast:0» (arg0 : typeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «$subst_typeIR':case_7:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$subst_typeIR':case_8:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$subst_typeIR':case_9:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$subst_typeIR':case_10:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$subst_typeIR':case_11:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$subst_typeIR':case_12:downcast:0» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$subst_typeIR':case_13:downcast:0» (arg0 : typeIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «$subst_typeIR':case_14:downcast:0» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$subst_typeIR':case_15:downcast:0» (arg0 : typeIR) : (_root_.Option externObjectTypeIR) := match arg0 with | .«EXTERN % `< % `> %» field0 field1 field2 => some (externObjectTypeIR.«EXTERN % `< % `> %» field0 field1 field2) | _ => none


def «$subst_typeIR':case_15:downcast:9» (arg0 : callableTypeDefIR) : (_root_.Option externMethodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$subst_typeIR':case_16:downcast:0» (arg0 : typeIR) : (_root_.Option parserObjectTypeIR) := match arg0 with | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (parserObjectTypeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | _ => none


def «$subst_typeIR':case_17:downcast:0» (arg0 : typeIR) : (_root_.Option controlObjectTypeIR) := match arg0 with | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (controlObjectTypeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | _ => none


def «$subst_typeIR':case_18:downcast:0» (arg0 : typeIR) : (_root_.Option packageObjectTypeIR) := match arg0 with | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (packageObjectTypeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$subst_typeIR':case_19:downcast:0» (arg0 : typeIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


def «$subst_typeIR':case_20:downcast:0» (arg0 : typeIR) : (_root_.Option defaultTypeIR) := match arg0 with | .DEFAULT => some (defaultTypeIR.DEFAULT) | _ => none


def «$subst_typeIR':case_21:downcast:0» (arg0 : typeIR) : (_root_.Option invalidHeaderTypeIR) := match arg0 with | .HEADER_INVALID => some (invalidHeaderTypeIR.HEADER_INVALID) | _ => none


def «$subst_typeIR':case_22:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «$subst_typeIR':case_23:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «$subst_typeIR':case_24:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$subst_typeIR':case_25:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$subst_typeIR':case_26:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «$subst_typeIR':case_27:downcast:0» (arg0 : typeIR) : (_root_.Option tableMetadataTypeIR) := match arg0 with | .«TABLE_ENUM % `{ % `}» field0 field1 => some (tableMetadataTypeIR.«TABLE_ENUM % `{ % `}» field0 field1) | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (tableMetadataTypeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none

end SpecTec
