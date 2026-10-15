import SpecTecDecl0026

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$subst_callableTypeIR':case_1:downcast:0» (arg0 : callableTypeIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «$subst_callableTypeIR':case_2:downcast:0» (arg0 : callableTypeIR) : (_root_.Option definedFunctionTypeIR) := match arg0 with | .«FUNCTION % `( % `) ':' %» field0 field1 field2 => some (definedFunctionTypeIR.«FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «$subst_callableTypeIR':case_3:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externFunctionTypeIR) := match arg0 with | .«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2 => some (externFunctionTypeIR.«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «$subst_callableTypeIR':case_4:downcast:0» (arg0 : callableTypeIR) : (_root_.Option builtinMethodTypeIR) := match arg0 with | .BUILTIN_IS_VALID => some (builtinMethodTypeIR.BUILTIN_IS_VALID) | .BUILTIN_SET_VALID => some (builtinMethodTypeIR.BUILTIN_SET_VALID) | .BUILTIN_SET_INVALID => some (builtinMethodTypeIR.BUILTIN_SET_INVALID) | .BUILTIN_PUSH_FRONT => some (builtinMethodTypeIR.BUILTIN_PUSH_FRONT) | .BUILTIN_POP_FRONT => some (builtinMethodTypeIR.BUILTIN_POP_FRONT) | .BUILTIN_SIZE_OF => some (builtinMethodTypeIR.BUILTIN_SIZE_OF) | _ => none


def «$subst_callableTypeIR':case_5:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «$subst_callableTypeIR':case_6:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «$subst_callableTypeIR':case_7:downcast:0» (arg0 : callableTypeIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «$subst_callableTypeIR':case_8:downcast:0» (arg0 : callableTypeIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «$subst_callableTypeIR':case_9:downcast:0» (arg0 : callableTypeIR) : (_root_.Option tableApplyMethodTypeIR) := match arg0 with | .«TABLE_APPLY ':' %» field0 => some (tableApplyMethodTypeIR.«TABLE_APPLY ':' %» field0) | _ => none


def «$subst_callableTypeDefIR':case_1:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «$subst_callableTypeDefIR':case_1:downcast:2» (arg0 : callableTypeIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «$subst_callableTypeDefIR':case_2:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option definedFunctionTypeDefIR) := match arg0 with | .«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (definedFunctionTypeDefIR.«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$subst_callableTypeDefIR':case_3:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externFunctionTypeDefIR) := match arg0 with | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externFunctionTypeDefIR.«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$subst_callableTypeDefIR':case_4:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externMethodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$subst_callableTypeDefIR':case_5:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externMethodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$subst_callableTypeDefIR':case_6:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «$subst_callableTypeDefIR':case_6:downcast:2» (arg0 : callableTypeIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «$subst_callableTypeDefIR':case_7:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «$subst_callableTypeDefIR':case_7:downcast:2» (arg0 : callableTypeIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «Type_alpha:baseTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option baseTypeIR) := match arg0 with | .VOID => some (baseTypeIR.VOID) | .BOOL => some (baseTypeIR.BOOL) | .ERROR => some (baseTypeIR.ERROR) | .MATCH_KIND => some (baseTypeIR.MATCH_KIND) | .STRING => some (baseTypeIR.STRING) | .INT => some (baseTypeIR.INT) | .«INT `< % `>» field0 => some (baseTypeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (baseTypeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (baseTypeIR.«VARBIT `< % `>» field0) | _ => none


def «Type_alpha:baseTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option baseTypeIR) := match arg0 with | .VOID => some (baseTypeIR.VOID) | .BOOL => some (baseTypeIR.BOOL) | .ERROR => some (baseTypeIR.ERROR) | .MATCH_KIND => some (baseTypeIR.MATCH_KIND) | .STRING => some (baseTypeIR.STRING) | .INT => some (baseTypeIR.INT) | .«INT `< % `>» field0 => some (baseTypeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (baseTypeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (baseTypeIR.«VARBIT `< % `>» field0) | _ => none


def «Type_alpha:nameTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «Type_alpha:nameTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «Type_alpha:left:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «Type_alpha:right:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «Type_alpha:newTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «Type_alpha:newTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «Type_alpha:listTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «Type_alpha:listTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «Type_alpha:tupleTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «Type_alpha:tupleTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «Type_alpha:arrayTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none

end SpecTec
