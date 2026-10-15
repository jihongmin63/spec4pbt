import SpecTecDecl0072

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$parameterListIR_of_constructorDef:case_1:downcast:0» (arg0 : constructorDef) : (_root_.Option externObjectConstructorDef) := match arg0 with | .«EXTERN % `< % `> `( % `) `{ % `}» field0 field1 field2 field3 => some (externObjectConstructorDef.«EXTERN % `< % `> `( % `) `{ % `}» field0 field1 field2 field3) | _ => none


def «$parameterListIR_of_constructorDef:case_2:downcast:0» (arg0 : constructorDef) : (_root_.Option parserObjectConstructorDef) := match arg0 with | .«PARSER `< % `> `( % `) `( % `) `{ % % `}» field0 field1 field2 field3 field4 => some (parserObjectConstructorDef.«PARSER `< % `> `( % `) `( % `) `{ % % `}» field0 field1 field2 field3 field4) | _ => none


def «$parameterListIR_of_constructorDef:case_3:downcast:0» (arg0 : constructorDef) : (_root_.Option controlObjectConstructorDef) := match arg0 with | .«CONTROL `< % `> `( % `) `( % `) `{ % APPLY % `}» field0 field1 field2 field3 field4 => some (controlObjectConstructorDef.«CONTROL `< % `> `( % `) `( % `) `{ % APPLY % `}» field0 field1 field2 field3 field4) | _ => none


def «$parameterListIR_of_constructorDef:case_4:downcast:0» (arg0 : constructorDef) : (_root_.Option packageObjectConstructorDef) := match arg0 with | .«PACKAGE `< % `> `( % `)» field0 field1 => some (packageObjectConstructorDef.«PACKAGE `< % `> `( % `)» field0 field1) | _ => none


abbrev objectState : Type := _root_.SpecTecExternTypes.objectState


abbrev externMethodDefEnv : Type := (map callableId externMethodDef)


abbrev actionDefEnv : Type := (map callableId actionDef)


inductive controlApplyMethodDef : Type where
  | «CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» : parameterListIR → controlLocalDeclarationListIR → actionDefEnv → controlBodyIR → controlApplyMethodDef
deriving _root_.DecidableEq


structure tableObjectProperty : Type where
  («KEYS» : tableKeysPropertyIR)
  («ACTIONS» : tableActionsPropertyIR)
  («DEFAULT_ACTION» : tableDefaultActionPropertyIR)
  («ENTRIES» : tableEntriesPropertyIR)
  («CUSTOMS» : (_root_.List tableCustomPropertyIR))
deriving _root_.DecidableEq


inductive valueSetObject : Type where
  | «VALUE_SET `{ % `( % `) `}» : (_root_.List value) → _root_.Nat → valueSetObject
deriving _root_.DecidableEq


abbrev frame : Type := (map id value)


inductive externMethodCallee : Type where
  | «EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» : objectId → nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → (_root_.List id) → theta → frame → (_root_.Option blockStatementIR) → externMethodCallee
deriving _root_.DecidableEq


inductive controlApplyMethodCallee : Type where
  | «CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» : objectId → parameterListIR → (_root_.List id) → theta → frame → controlLocalDeclarationListIR → actionDefEnv → controlBodyIR → controlApplyMethodCallee
deriving _root_.DecidableEq


inductive tableApplyMethodCallee : Type where
  | «TABLE % '.' APPLY `{ % ';' % `}» : objectId → frame → tableObjectProperty → tableApplyMethodCallee
deriving _root_.DecidableEq


inductive externObject : Type where
  | «EXTERN % `< % `> `{ % % % `}» : typeId → theta → objectState → frame → externMethodDefEnv → externObject
deriving _root_.DecidableEq


inductive controlObject : Type where
  | «CONTROL `< % `> `( % `) `{ % % % % `}» : theta → parameterListIR → frame → controlLocalDeclarationListIR → actionDefEnv → controlBodyIR → controlObject
deriving _root_.DecidableEq


inductive packageObject : Type where
  | «PACKAGE `< % `> `{ % `}» : theta → frame → packageObject
deriving _root_.DecidableEq


inductive tableObject : Type where
  | «TABLE % `{ % % `}» : typeId → frame → tableObjectProperty → tableObject
deriving _root_.DecidableEq


abbrev stateEnv : Type := (map id parserStateIR)


inductive parserApplyMethodDef : Type where
  | «PARSER_APPLY `( % `) `{ % ';' % `}» : parameterListIR → parserLocalDeclarationListIR → stateEnv → parserApplyMethodDef
deriving _root_.DecidableEq


inductive methodDef : Type where
  | «EXTERN_METHOD % `< % `> `( % `) %» : nameIR → typeParameterListIR → parameterListIR → (_root_.Option blockStatementIR) → methodDef
  | «EXTERN_METHOD ABSTRACT % `< % `> `( % `)» : nameIR → typeParameterListIR → parameterListIR → methodDef
  | «PARSER_APPLY `( % `) `{ % ';' % `}» : parameterListIR → parserLocalDeclarationListIR → stateEnv → methodDef
  | «CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» : parameterListIR → controlLocalDeclarationListIR → actionDefEnv → controlBodyIR → methodDef
  | «TABLE_APPLY `{ % `}» : tablePropertyListIR → methodDef
deriving _root_.DecidableEq


inductive callableDef : Type where
  | «% ACTION % `( % `) %» : annotationList → nameIR → parameterListIR → blockStatementIR → callableDef
  | «FUNCTION % `< % `> `( % `) %» : nameIR → typeParameterListIR → parameterListIR → blockStatementIR → callableDef
  | «EXTERN_FUNCTION % `< % `> `( % `)» : nameIR → typeParameterListIR → parameterListIR → callableDef
  | «EXTERN_METHOD % `< % `> `( % `) %» : nameIR → typeParameterListIR → parameterListIR → (_root_.Option blockStatementIR) → callableDef
  | «EXTERN_METHOD ABSTRACT % `< % `> `( % `)» : nameIR → typeParameterListIR → parameterListIR → callableDef
  | «PARSER_APPLY `( % `) `{ % ';' % `}» : parameterListIR → parserLocalDeclarationListIR → stateEnv → callableDef
  | «CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» : parameterListIR → controlLocalDeclarationListIR → actionDefEnv → controlBodyIR → callableDef
  | «TABLE_APPLY `{ % `}» : tablePropertyListIR → callableDef
deriving _root_.DecidableEq


def «$parameterListIR_of_callableDef:case_1:downcast:0» (arg0 : callableDef) : (_root_.Option actionDef) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDef.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «$parameterListIR_of_callableDef:case_2:downcast:0» (arg0 : callableDef) : (_root_.Option functionDef) := match arg0 with | .«FUNCTION % `< % `> `( % `) %» field0 field1 field2 field3 => some (functionDef.«FUNCTION % `< % `> `( % `) %» field0 field1 field2 field3) | .«EXTERN_FUNCTION % `< % `> `( % `)» field0 field1 field2 => some (functionDef.«EXTERN_FUNCTION % `< % `> `( % `)» field0 field1 field2) | _ => none


def «$parameterListIR_of_callableDef:case_3:downcast:0» (arg0 : callableDef) : (_root_.Option methodDef) := match arg0 with | .«EXTERN_METHOD % `< % `> `( % `) %» field0 field1 field2 field3 => some (methodDef.«EXTERN_METHOD % `< % `> `( % `) %» field0 field1 field2 field3) | .«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» field0 field1 field2 => some (methodDef.«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» field0 field1 field2) | .«PARSER_APPLY `( % `) `{ % ';' % `}» field0 field1 field2 => some (methodDef.«PARSER_APPLY `( % `) `{ % ';' % `}» field0 field1 field2) | .«CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 => some (methodDef.«CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» field0 field1 field2 field3) | .«TABLE_APPLY `{ % `}» field0 => some (methodDef.«TABLE_APPLY `{ % `}» field0) | _ => none


def «$parameterListIR_of_methodDef:case_1:downcast:0» (arg0 : methodDef) : (_root_.Option externMethodDef) := match arg0 with | .«EXTERN_METHOD % `< % `> `( % `) %» field0 field1 field2 field3 => some (externMethodDef.«EXTERN_METHOD % `< % `> `( % `) %» field0 field1 field2 field3) | .«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» field0 field1 field2 => some (externMethodDef.«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» field0 field1 field2) | _ => none


def «$parameterListIR_of_methodDef:case_2:downcast:0» (arg0 : methodDef) : (_root_.Option parserApplyMethodDef) := match arg0 with | .«PARSER_APPLY `( % `) `{ % ';' % `}» field0 field1 field2 => some (parserApplyMethodDef.«PARSER_APPLY `( % `) `{ % ';' % `}» field0 field1 field2) | _ => none


def «$parameterListIR_of_methodDef:case_3:downcast:0» (arg0 : methodDef) : (_root_.Option controlApplyMethodDef) := match arg0 with | .«CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» field0 field1 field2 field3 => some (controlApplyMethodDef.«CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» field0 field1 field2 field3) | _ => none


def «$parameterListIR_of_methodDef:case_4:downcast:0» (arg0 : methodDef) : (_root_.Option tableApplyMethodDef) := match arg0 with | .«TABLE_APPLY `{ % `}» field0 => some (tableApplyMethodDef.«TABLE_APPLY `{ % `}» field0) | _ => none


inductive parserApplyMethodCallee : Type where
  | «PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» : objectId → parameterListIR → (_root_.List id) → theta → frame → parserLocalDeclarationListIR → stateEnv → parserApplyMethodCallee
deriving _root_.DecidableEq


inductive methodCallee : Type where
  | BUILTIN_IS_VALID : storageReference → methodCallee
  | BUILTIN_SET_VALID : storageReference → methodCallee
  | BUILTIN_SET_INVALID : storageReference → methodCallee
  | BUILTIN_PUSH_FRONT : storageReference → methodCallee
  | BUILTIN_POP_FRONT : storageReference → methodCallee
  | BUILTIN_SIZE_OF : nameIR → typeIR → methodCallee
  | «EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» : objectId → nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → (_root_.List id) → theta → frame → (_root_.Option blockStatementIR) → methodCallee
  | «PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» : objectId → parameterListIR → (_root_.List id) → theta → frame → parserLocalDeclarationListIR → stateEnv → methodCallee
  | «CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» : objectId → parameterListIR → (_root_.List id) → theta → frame → controlLocalDeclarationListIR → actionDefEnv → controlBodyIR → methodCallee
  | «TABLE % '.' APPLY `{ % ';' % `}» : objectId → frame → tableObjectProperty → methodCallee
deriving _root_.DecidableEq


inductive callee : Type where
  | «ACTION % '.' % `( % '#' % `) %» : cursor → nameIR → parameterListIR → (_root_.List id) → blockStatementIR → callee
  | «FUNCTION % `< % `> `( % '#' % `) %» : nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → blockStatementIR → callee
  | «EXTERN_FUNCTION % `< % `> `( % '#' % '#' % `)» : nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → (_root_.List id) → callee
  | BUILTIN_IS_VALID : storageReference → callee
  | BUILTIN_SET_VALID : storageReference → callee
  | BUILTIN_SET_INVALID : storageReference → callee
  | BUILTIN_PUSH_FRONT : storageReference → callee
  | BUILTIN_POP_FRONT : storageReference → callee
  | BUILTIN_SIZE_OF : nameIR → typeIR → callee
  | «EXTERN_METHOD % '.' % `< % `> `( % '#' % '#' % `) `{ % ';' % ';' % `}» : objectId → nameIR → typeParameterListIR → parameterListIR → (_root_.List id) → (_root_.List id) → theta → frame → (_root_.Option blockStatementIR) → callee
  | «PARSER % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % `}» : objectId → parameterListIR → (_root_.List id) → theta → frame → parserLocalDeclarationListIR → stateEnv → callee
  | «CONTROL % '.' APPLY `( % '#' % `) `{ % ';' % ';' % ';' % ';' % `}» : objectId → parameterListIR → (_root_.List id) → theta → frame → controlLocalDeclarationListIR → actionDefEnv → controlBodyIR → callee
  | «TABLE % '.' APPLY `{ % ';' % `}» : objectId → frame → tableObjectProperty → callee
deriving _root_.DecidableEq

end SpecTec
