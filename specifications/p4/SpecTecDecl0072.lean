import SpecTecDecl0071

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$gen_constraint_pair:case_14:downcast:0» (arg0 : typeIR) : (_root_.Option controlObjectTypeIR) := match arg0 with | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (controlObjectTypeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_14:downcast:1» (arg0 : typeIR) : (_root_.Option controlObjectTypeIR) := match arg0 with | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (controlObjectTypeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_15:downcast:0» (arg0 : typeIR) : (_root_.Option packageObjectTypeIR) := match arg0 with | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (packageObjectTypeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_15:downcast:1» (arg0 : typeIR) : (_root_.Option packageObjectTypeIR) := match arg0 with | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (packageObjectTypeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$resolve_type_alias:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$resolve_type_alias:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option externObjectTypeIR) := match arg0 with | .«EXTERN % `< % `> %» field0 field1 field2 => some (externObjectTypeIR.«EXTERN % `< % `> %» field0 field1 field2) | _ => none


def «$resolve_type_alias:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option packageObjectTypeIR) := match arg0 with | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (packageObjectTypeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | _ => none


inductive storageReference : Type where
  | _BARE : nameIR → storageReference
  | «'.' %» : nameIR → storageReference
  | «% '.' %» : storageReference → nameIR → storageReference
  | «% `[ % `]» : storageReference → value → storageReference
  | «% `[ % % % `]» : storageReference → value → sliceop → value → storageReference
deriving _root_.DecidableEq


inductive actionDef : Type where
  | «% ACTION % `( % `) %» : annotationList → nameIR → parameterListIR → blockStatementIR → actionDef
deriving _root_.DecidableEq


inductive definedFunctionDef : Type where
  | «FUNCTION % `< % `> `( % `) %» : nameIR → typeParameterListIR → parameterListIR → blockStatementIR → definedFunctionDef
deriving _root_.DecidableEq


inductive externFunctionDef : Type where
  | «EXTERN_FUNCTION % `< % `> `( % `)» : nameIR → typeParameterListIR → parameterListIR → externFunctionDef
deriving _root_.DecidableEq


inductive functionDef : Type where
  | «FUNCTION % `< % `> `( % `) %» : nameIR → typeParameterListIR → parameterListIR → blockStatementIR → functionDef
  | «EXTERN_FUNCTION % `< % `> `( % `)» : nameIR → typeParameterListIR → parameterListIR → functionDef
deriving _root_.DecidableEq


inductive externMethodDef : Type where
  | «EXTERN_METHOD % `< % `> `( % `) %» : nameIR → typeParameterListIR → parameterListIR → (_root_.Option blockStatementIR) → externMethodDef
  | «EXTERN_METHOD ABSTRACT % `< % `> `( % `)» : nameIR → typeParameterListIR → parameterListIR → externMethodDef
deriving _root_.DecidableEq


inductive tableApplyMethodDef : Type where
  | «TABLE_APPLY `{ % `}» : tablePropertyListIR → tableApplyMethodDef
deriving _root_.DecidableEq


def «$parameterListIR_of_functionDef:case_1:downcast:0» (arg0 : functionDef) : (_root_.Option definedFunctionDef) := match arg0 with | .«FUNCTION % `< % `> `( % `) %» field0 field1 field2 field3 => some (definedFunctionDef.«FUNCTION % `< % `> `( % `) %» field0 field1 field2 field3) | _ => none


def «$parameterListIR_of_functionDef:case_2:downcast:0» (arg0 : functionDef) : (_root_.Option externFunctionDef) := match arg0 with | .«EXTERN_FUNCTION % `< % `> `( % `)» field0 field1 field2 => some (externFunctionDef.«EXTERN_FUNCTION % `< % `> `( % `)» field0 field1 field2) | _ => none


inductive actionCallee : Type where
  | «ACTION % '.' % `( % '#' % `) %» : cursor → nameIR → parameterListIR → (_root_.List id) → blockStatementIR → actionCallee
deriving _root_.DecidableEq


inductive definedFunctionCallee : Type where
  | «FUNCTION % `< % `> `( % '#' % `) %» : nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → blockStatementIR → definedFunctionCallee
deriving _root_.DecidableEq


inductive externFunctionCallee : Type where
  | «EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» : nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → (_root_.List id) → externFunctionCallee
deriving _root_.DecidableEq


inductive functionCallee : Type where
  | «FUNCTION % `< % `> `( % '#' % `) %» : nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → blockStatementIR → functionCallee
  | «EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» : nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → (_root_.List id) → functionCallee
deriving _root_.DecidableEq


inductive builtinIsValidMethodCallee : Type where
  | BUILTIN_IS_VALID : storageReference → builtinIsValidMethodCallee
deriving _root_.DecidableEq


inductive builtinSetValidMethodCallee : Type where
  | BUILTIN_SET_VALID : storageReference → builtinSetValidMethodCallee
deriving _root_.DecidableEq


inductive builtinSetInvalidMethodCallee : Type where
  | BUILTIN_SET_INVALID : storageReference → builtinSetInvalidMethodCallee
deriving _root_.DecidableEq


inductive builtinPushFrontMethodCallee : Type where
  | BUILTIN_PUSH_FRONT : storageReference → builtinPushFrontMethodCallee
deriving _root_.DecidableEq


inductive builtinPopFrontMethodCallee : Type where
  | BUILTIN_POP_FRONT : storageReference → builtinPopFrontMethodCallee
deriving _root_.DecidableEq


inductive builtinSizeMethodCallee : Type where
  | BUILTIN_SIZE_OF : nameIR → typeIR → builtinSizeMethodCallee
deriving _root_.DecidableEq


inductive builtinMethodCallee : Type where
  | BUILTIN_IS_VALID : storageReference → builtinMethodCallee
  | BUILTIN_SET_VALID : storageReference → builtinMethodCallee
  | BUILTIN_SET_INVALID : storageReference → builtinMethodCallee
  | BUILTIN_PUSH_FRONT : storageReference → builtinMethodCallee
  | BUILTIN_POP_FRONT : storageReference → builtinMethodCallee
  | BUILTIN_SIZE_OF : nameIR → typeIR → builtinMethodCallee
deriving _root_.DecidableEq


inductive externObjectConstructorDef : Type where
  | «EXTERN % `< % `> `( % `) `{ % `}» : nameIR → typeParameterListIR → constructorParameterListIR → externMethodPrototypeListIR → externObjectConstructorDef
deriving _root_.DecidableEq


inductive parserObjectConstructorDef : Type where
  | «PARSER `< % `> `( % `) `( % `) `{ % % `}» : typeParameterListIR → parameterListIR → constructorParameterListIR → parserLocalDeclarationListIR → parserStateListIR → parserObjectConstructorDef
deriving _root_.DecidableEq


inductive controlObjectConstructorDef : Type where
  | «CONTROL `< % `> `( % `) `( % `) `{ % APPLY % `}» : typeParameterListIR → parameterListIR → constructorParameterListIR → controlLocalDeclarationListIR → controlBodyIR → controlObjectConstructorDef
deriving _root_.DecidableEq


inductive packageObjectConstructorDef : Type where
  | «PACKAGE `< % `> `( % `)» : typeParameterListIR → constructorParameterListIR → packageObjectConstructorDef
deriving _root_.DecidableEq


inductive constructorDef : Type where
  | «EXTERN % `< % `> `( % `) `{ % `}» : nameIR → typeParameterListIR → constructorParameterListIR → externMethodPrototypeListIR → constructorDef
  | «PARSER `< % `> `( % `) `( % `) `{ % % `}» : typeParameterListIR → parameterListIR → constructorParameterListIR → parserLocalDeclarationListIR → parserStateListIR → constructorDef
  | «CONTROL `< % `> `( % `) `( % `) `{ % APPLY % `}» : typeParameterListIR → parameterListIR → constructorParameterListIR → controlLocalDeclarationListIR → controlBodyIR → constructorDef
  | «PACKAGE `< % `> `( % `)» : typeParameterListIR → constructorParameterListIR → constructorDef
deriving _root_.DecidableEq

end SpecTec
