import SpecTecDecl0023

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive externFunctionTypeDefIR : Type where
  | «EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → externFunctionTypeDefIR
deriving _root_.DecidableEq


inductive functionTypeDefIR : Type where
  | «FUNCTION % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → functionTypeDefIR
  | «EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → functionTypeDefIR
deriving _root_.DecidableEq


abbrev parserApplyMethodTypeDefIR : Type := parserApplyMethodTypeIR


abbrev controlApplyMethodTypeDefIR : Type := controlApplyMethodTypeIR


inductive methodTypeDefIR : Type where
  | «EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → methodTypeDefIR
  | «EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → methodTypeDefIR
  | «PARSER_APPLY `( % `)» : (_root_.List parameterIR) → methodTypeDefIR
  | «CONTROL_APPLY `( % `)» : (_root_.List parameterIR) → methodTypeDefIR
  | «TABLE_APPLY ':' %» : tableMetadataStructTypeIR → methodTypeDefIR
deriving _root_.DecidableEq


inductive callableTypeDefIR : Type where
  | «% ACTION % `( % `)» : annotationList → nameIR → (_root_.List parameterIR) → callableTypeDefIR
  | «FUNCTION % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → callableTypeDefIR
  | «EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → callableTypeDefIR
  | «EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → callableTypeDefIR
  | «EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → callableTypeDefIR
  | «PARSER_APPLY `( % `)» : (_root_.List parameterIR) → callableTypeDefIR
  | «CONTROL_APPLY `( % `)» : (_root_.List parameterIR) → callableTypeDefIR
  | «TABLE_APPLY ':' %» : tableMetadataStructTypeIR → callableTypeDefIR
deriving _root_.DecidableEq


def «$callableTypeIR_of_callableTypeDefIR:case_1:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «$callableTypeIR_of_callableTypeDefIR:case_2:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option definedFunctionTypeDefIR) := match arg0 with | .«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (definedFunctionTypeDefIR.«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$callableTypeIR_of_callableTypeDefIR:case_3:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externFunctionTypeDefIR) := match arg0 with | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externFunctionTypeDefIR.«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$callableTypeIR_of_callableTypeDefIR:case_4:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externMethodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$callableTypeIR_of_callableTypeDefIR:case_5:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externMethodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$callableTypeIR_of_callableTypeDefIR:case_6:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «$callableTypeIR_of_callableTypeDefIR:case_7:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «$typeParameterListIR_of_callableTypeDefIR:case_1:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «$typeParameterListIR_of_callableTypeDefIR:case_2:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option definedFunctionTypeDefIR) := match arg0 with | .«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (definedFunctionTypeDefIR.«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$typeParameterListIR_of_callableTypeDefIR:case_3:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externFunctionTypeDefIR) := match arg0 with | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externFunctionTypeDefIR.«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$typeParameterListIR_of_callableTypeDefIR:case_4:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externMethodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$typeParameterListIR_of_callableTypeDefIR:case_5:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option externMethodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$typeParameterListIR_of_callableTypeDefIR:case_6:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «$typeParameterListIR_of_callableTypeDefIR:case_7:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «$parameterListIR_of_callableTypeDefIR:case_1:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «$parameterListIR_of_callableTypeDefIR:case_2:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option functionTypeDefIR) := match arg0 with | .«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (functionTypeDefIR.«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (functionTypeDefIR.«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$parameterListIR_of_callableTypeDefIR:case_3:downcast:0» (arg0 : callableTypeDefIR) : (_root_.Option methodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (methodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (methodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«PARSER_APPLY `( % `)» field0 => some (methodTypeDefIR.«PARSER_APPLY `( % `)» field0) | .«CONTROL_APPLY `( % `)» field0 => some (methodTypeDefIR.«CONTROL_APPLY `( % `)» field0) | .«TABLE_APPLY ':' %» field0 => some (methodTypeDefIR.«TABLE_APPLY ':' %» field0) | _ => none


def «$parameterListIR_of_functionTypeDefIR:case_1:downcast:0» (arg0 : functionTypeDefIR) : (_root_.Option definedFunctionTypeDefIR) := match arg0 with | .«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (definedFunctionTypeDefIR.«FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$parameterListIR_of_functionTypeDefIR:case_2:downcast:0» (arg0 : functionTypeDefIR) : (_root_.Option externFunctionTypeDefIR) := match arg0 with | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externFunctionTypeDefIR.«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$parameterListIR_of_methodTypeDefIR:case_1:downcast:0» (arg0 : methodTypeDefIR) : (_root_.Option externMethodTypeDefIR) := match arg0 with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4 => some (externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» field0 field1 field2 field3 field4) | _ => none


def «$parameterListIR_of_methodTypeDefIR:case_2:downcast:0» (arg0 : methodTypeDefIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «$parameterListIR_of_methodTypeDefIR:case_3:downcast:0» (arg0 : methodTypeDefIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «$parameterListIR_of_methodTypeDefIR:case_4:downcast:0» (arg0 : methodTypeDefIR) : (_root_.Option tableApplyMethodTypeIR) := match arg0 with | .«TABLE_APPLY ':' %» field0 => some (tableApplyMethodTypeIR.«TABLE_APPLY ':' %» field0) | _ => none


abbrev constructorParameterIR : Type := parameterIR


inductive constructorTypeIR : Type where
  | «CONSTRUCTOR `( % `) ':' %» : (_root_.List constructorParameterIR) → typeIR → constructorTypeIR
deriving _root_.DecidableEq


inductive constructorTypeDefIR : Type where
  | «CONSTRUCTOR `< % ',' % `> `( % `) ':' %» : (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List constructorParameterIR) → typeIR → constructorTypeDefIR
deriving _root_.DecidableEq

end SpecTec
