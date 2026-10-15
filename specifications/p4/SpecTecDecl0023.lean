import SpecTecDecl0022

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$typeIR_of_typeDefIR:case_7:downcast:0» (arg0 : typeDefIR) : (_root_.Option externObjectTypeDefIR) := match arg0 with | .«EXTERN % `< % ',' % `> %» field0 field1 field2 field3 => some (externObjectTypeDefIR.«EXTERN % `< % ',' % `> %» field0 field1 field2 field3) | _ => none


def «$typeIR_of_typeDefIR:case_8:downcast:0» (arg0 : typeDefIR) : (_root_.Option parserObjectTypeDefIR) := match arg0 with | .«PARSER % `< % ',' % `> `( % `)» field0 field1 field2 field3 => some (parserObjectTypeDefIR.«PARSER % `< % ',' % `> `( % `)» field0 field1 field2 field3) | _ => none


def «$typeIR_of_typeDefIR:case_9:downcast:0» (arg0 : typeDefIR) : (_root_.Option controlObjectTypeDefIR) := match arg0 with | .«CONTROL % `< % ',' % `> `( % `)» field0 field1 field2 field3 => some (controlObjectTypeDefIR.«CONTROL % `< % ',' % `> `( % `)» field0 field1 field2 field3) | _ => none


def «$typeIR_of_typeDefIR:case_10:downcast:0» (arg0 : typeDefIR) : (_root_.Option packageObjectTypeDefIR) := match arg0 with | .«PACKAGE % `< % ',' % `> `{ % `}» field0 field1 field2 field3 => some (packageObjectTypeDefIR.«PACKAGE % `< % ',' % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$typeIR_of_typeDefIR:case_11:downcast:0» (arg0 : typeDefIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_1:downcast:0» (arg0 : typeDefIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_2:downcast:0» (arg0 : typeDefIR) : (_root_.Option aliasTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (aliasTypeIR.TYPEDEF field0 field1) | .TYPE field0 field1 => some (aliasTypeIR.TYPE field0 field1) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_3:downcast:0» (arg0 : typeDefIR) : (_root_.Option structTypeDefIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeDefIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_4:downcast:0» (arg0 : typeDefIR) : (_root_.Option headerTypeDefIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeDefIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_5:downcast:0» (arg0 : typeDefIR) : (_root_.Option headerUnionTypeDefIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeDefIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_6:downcast:0» (arg0 : typeDefIR) : (_root_.Option enumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (enumTypeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (enumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_7:downcast:0» (arg0 : typeDefIR) : (_root_.Option externObjectTypeDefIR) := match arg0 with | .«EXTERN % `< % ',' % `> %» field0 field1 field2 field3 => some (externObjectTypeDefIR.«EXTERN % `< % ',' % `> %» field0 field1 field2 field3) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_8:downcast:0» (arg0 : typeDefIR) : (_root_.Option parserObjectTypeDefIR) := match arg0 with | .«PARSER % `< % ',' % `> `( % `)» field0 field1 field2 field3 => some (parserObjectTypeDefIR.«PARSER % `< % ',' % `> `( % `)» field0 field1 field2 field3) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_9:downcast:0» (arg0 : typeDefIR) : (_root_.Option controlObjectTypeDefIR) := match arg0 with | .«CONTROL % `< % ',' % `> `( % `)» field0 field1 field2 field3 => some (controlObjectTypeDefIR.«CONTROL % `< % ',' % `> `( % `)» field0 field1 field2 field3) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_10:downcast:0» (arg0 : typeDefIR) : (_root_.Option packageObjectTypeDefIR) := match arg0 with | .«PACKAGE % `< % ',' % `> `{ % `}» field0 field1 field2 field3 => some (packageObjectTypeDefIR.«PACKAGE % `< % ',' % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$typeParameterListIR_of_typeDefIR:case_11:downcast:0» (arg0 : typeDefIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


def «$is_monomorphic_typeDefIR:case_1:downcast:0» (arg0 : typeDefIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$is_monomorphic_typeDefIR:case_2:downcast:0» (arg0 : typeDefIR) : (_root_.Option aliasTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (aliasTypeIR.TYPEDEF field0 field1) | .TYPE field0 field1 => some (aliasTypeIR.TYPE field0 field1) | _ => none


def «$is_monomorphic_typeDefIR:case_3:downcast:0» (arg0 : typeDefIR) : (_root_.Option enumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (enumTypeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (enumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$is_monomorphic_typeDefIR:case_4:downcast:0» (arg0 : typeDefIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


inductive initializerIR : Type where
  | «'=' %» : typedExpressionIR → initializerIR
deriving _root_.DecidableEq


inductive actionTypeIR : Type where
  | «% ACTION % `( % `)» : annotationList → nameIR → (_root_.List parameterIR) → actionTypeIR
deriving _root_.DecidableEq


inductive definedFunctionTypeIR : Type where
  | «FUNCTION % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → definedFunctionTypeIR
deriving _root_.DecidableEq


inductive externFunctionTypeIR : Type where
  | «EXTERN_FUNCTION % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → externFunctionTypeIR
deriving _root_.DecidableEq


inductive functionTypeIR : Type where
  | «FUNCTION % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → functionTypeIR
  | «EXTERN_FUNCTION % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → functionTypeIR
deriving _root_.DecidableEq


inductive externMethodTypeIR : Type where
  | «EXTERN_METHOD % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → externMethodTypeIR
  | «EXTERN_METHOD ABSTRACT % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → externMethodTypeIR
deriving _root_.DecidableEq


inductive parserApplyMethodTypeIR : Type where
  | «PARSER_APPLY `( % `)» : (_root_.List parameterIR) → parserApplyMethodTypeIR
deriving _root_.DecidableEq


inductive controlApplyMethodTypeIR : Type where
  | «CONTROL_APPLY `( % `)» : (_root_.List parameterIR) → controlApplyMethodTypeIR
deriving _root_.DecidableEq


inductive methodTypeIR : Type where
  | BUILTIN_IS_VALID : methodTypeIR
  | BUILTIN_SET_VALID : methodTypeIR
  | BUILTIN_SET_INVALID : methodTypeIR
  | BUILTIN_PUSH_FRONT : methodTypeIR
  | BUILTIN_POP_FRONT : methodTypeIR
  | BUILTIN_SIZE_OF : methodTypeIR
  | «EXTERN_METHOD % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → methodTypeIR
  | «EXTERN_METHOD ABSTRACT % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → methodTypeIR
  | «PARSER_APPLY `( % `)» : (_root_.List parameterIR) → methodTypeIR
  | «CONTROL_APPLY `( % `)» : (_root_.List parameterIR) → methodTypeIR
  | «TABLE_APPLY ':' %» : tableMetadataStructTypeIR → methodTypeIR
deriving _root_.DecidableEq


inductive callableTypeIR : Type where
  | «% ACTION % `( % `)» : annotationList → nameIR → (_root_.List parameterIR) → callableTypeIR
  | «FUNCTION % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → callableTypeIR
  | «EXTERN_FUNCTION % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → callableTypeIR
  | BUILTIN_IS_VALID : callableTypeIR
  | BUILTIN_SET_VALID : callableTypeIR
  | BUILTIN_SET_INVALID : callableTypeIR
  | BUILTIN_PUSH_FRONT : callableTypeIR
  | BUILTIN_POP_FRONT : callableTypeIR
  | BUILTIN_SIZE_OF : callableTypeIR
  | «EXTERN_METHOD % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → callableTypeIR
  | «EXTERN_METHOD ABSTRACT % `( % `) ':' %» : nameIR → (_root_.List parameterIR) → typeIR → callableTypeIR
  | «PARSER_APPLY `( % `)» : (_root_.List parameterIR) → callableTypeIR
  | «CONTROL_APPLY `( % `)» : (_root_.List parameterIR) → callableTypeIR
  | «TABLE_APPLY ':' %» : tableMetadataStructTypeIR → callableTypeIR
deriving _root_.DecidableEq


abbrev actionTypeDefIR : Type := actionTypeIR


inductive definedFunctionTypeDefIR : Type where
  | «FUNCTION % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → definedFunctionTypeDefIR
deriving _root_.DecidableEq

end SpecTec
