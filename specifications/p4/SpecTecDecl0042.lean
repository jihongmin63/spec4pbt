import SpecTecDecl0041

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$lift_declarationIR:case_4:downcast:0» (arg0 : declarationIR) : (_root_.Option actionDeclarationIR) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDeclarationIR.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «$lift_declarationIR:case_5:downcast:0» (arg0 : declarationIR) : (_root_.Option errorDeclarationIR) := match arg0 with | .«ERROR `{ % `}» field0 => some (errorDeclarationIR.«ERROR `{ % `}» field0) | _ => none


def «$lift_declarationIR:case_6:downcast:0» (arg0 : declarationIR) : (_root_.Option matchKindDeclarationIR) := match arg0 with | .«MATCH_KIND `{ % `}» field0 => some (matchKindDeclarationIR.«MATCH_KIND `{ % `}» field0) | _ => none


def «$lift_declarationIR:case_7:downcast:0» (arg0 : declarationIR) : (_root_.Option externDeclarationIR) := match arg0 with | .«% EXTERN % ';'» field0 field1 => some (externDeclarationIR.«% EXTERN % ';'» field0 field1) | .«% EXTERN % `< % ',' `> `{ % % `}» field0 field1 field2 field3 field4 => some (externDeclarationIR.«% EXTERN % `< % ',' `> `{ % % `}» field0 field1 field2 field3 field4) | _ => none


def «$lift_declarationIR:case_8:downcast:0» (arg0 : declarationIR) : (_root_.Option parserDeclarationIR) := match arg0 with | .«% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» field0 field1 field2 field3 field4 field5 field6 field7 => some (parserDeclarationIR.«% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» field0 field1 field2 field3 field4 field5 field6 field7) | _ => none


def «$lift_declarationIR:case_9:downcast:0» (arg0 : declarationIR) : (_root_.Option controlDeclarationIR) := match arg0 with | .«% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» field0 field1 field2 field3 field4 field5 field6 field7 => some (controlDeclarationIR.«% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» field0 field1 field2 field3 field4 field5 field6 field7) | _ => none


def «$lift_declarationIR:case_10:downcast:0» (arg0 : declarationIR) : (_root_.Option typeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (typeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (typeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (typeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (typeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (typeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typeDeclarationIR.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typeDeclarationIR.«% TYPE % % ';'» field0 field1 field2) | .«% PARSER % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (typeDeclarationIR.«% PARSER % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | .«% CONTROL % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (typeDeclarationIR.«% CONTROL % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | .«% PACKAGE % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (typeDeclarationIR.«% PACKAGE % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | _ => none


inductive flow : Type where
  | CONT : flow
  | RET : flow
deriving _root_.DecidableEq


inductive loop : Type where
  | IN : loop
  | OUT : loop
deriving _root_.DecidableEq


inductive varTypeIR : Type where
  | «% % % %» : direction → typeIR → ctk → (_root_.Option value) → varTypeIR
deriving _root_.DecidableEq


abbrev typeFrame : Type := (map id varTypeIR)


abbrev typeDefEnv : Type := (map typeId typeDefIR)


abbrev callableTypeDefEnv : Type := (map callableId callableTypeDefIR)


abbrev constructorTypeDefEnv : Type := (map constructorId constructorTypeDefIR)


structure globalTypingLayer : Type where
  («CONSTRUCTOR» : constructorTypeDefEnv)
  («TYPE» : typeDefEnv)
  («CALLABLE» : callableTypeDefEnv)
  («FRAME» : typeFrame)
deriving _root_.DecidableEq


inductive blockKind : Type where
  | _EMPTY : blockKind
  | EXTERN : blockKind
  | PARSER : blockKind
  | CONTROL : blockKind
  | PACKAGE : blockKind
deriving _root_.DecidableEq


structure blockTypingLayer : Type where
  («KIND» : blockKind)
  («TYPE» : typeDefEnv)
  («CALLABLE» : callableTypeDefEnv)
  («FRAME» : typeFrame)
deriving _root_.DecidableEq


inductive actionLocalKind : Type where
  | ACTION : actionLocalKind
deriving _root_.DecidableEq


inductive definedFunctionLocalKind : Type where
  | «FUNCTION ':' %» : typeIR → definedFunctionLocalKind
deriving _root_.DecidableEq


inductive externFunctionLocalKind : Type where
  | «EXTERN_FUNCTION ':' %» : typeIR → externFunctionLocalKind
deriving _root_.DecidableEq


inductive functionLocalKind : Type where
  | «FUNCTION ':' %» : typeIR → functionLocalKind
  | «EXTERN_FUNCTION ':' %» : typeIR → functionLocalKind
deriving _root_.DecidableEq


inductive externMethodLocalKind : Type where
  | «EXTERN_METHOD ':' %» : typeIR → externMethodLocalKind
  | «EXTERN_METHOD ABSTRACT ':' %» : typeIR → externMethodLocalKind
deriving _root_.DecidableEq


inductive methodLocalKind : Type where
  | «EXTERN_METHOD ':' %» : typeIR → methodLocalKind
  | «EXTERN_METHOD ABSTRACT ':' %» : typeIR → methodLocalKind
  | PARSER_STATE : methodLocalKind
  | CONTROL_APPLY_METHOD : methodLocalKind
  | TABLE_APPLY_METHOD : methodLocalKind
deriving _root_.DecidableEq


inductive localKind : Type where
  | _EMPTY : localKind
  | ACTION : localKind
  | «FUNCTION ':' %» : typeIR → localKind
  | «EXTERN_FUNCTION ':' %» : typeIR → localKind
  | «EXTERN_METHOD ':' %» : typeIR → localKind
  | «EXTERN_METHOD ABSTRACT ':' %» : typeIR → localKind
  | PARSER_STATE : localKind
  | CONTROL_APPLY_METHOD : localKind
  | TABLE_APPLY_METHOD : localKind
deriving _root_.DecidableEq


structure localTypingLayer : Type where
  («KIND» : localKind)
  («TYPE» : typeDefEnv)
  («FRAMES» : (_root_.List typeFrame))
deriving _root_.DecidableEq


structure typingContext : Type where
  («CONTROL» : flow)
  («LOOP» : loop)
  («GLOBAL» : globalTypingLayer)
  («BLOCK» : blockTypingLayer)
  («LOCAL» : localTypingLayer)
deriving _root_.DecidableEq


def «$find_local_return_type_t:case_1:downcast:0» (arg0 : localKind) : (_root_.Option definedFunctionLocalKind) := match arg0 with | .«FUNCTION ':' %» field0 => some (definedFunctionLocalKind.«FUNCTION ':' %» field0) | _ => none


def «$find_local_return_type_t:case_2:downcast:0» (arg0 : localKind) : (_root_.Option externFunctionLocalKind) := match arg0 with | .«EXTERN_FUNCTION ':' %» field0 => some (externFunctionLocalKind.«EXTERN_FUNCTION ':' %» field0) | _ => none


def «$find_local_return_type_t:case_4:downcast:0» (arg0 : localKind) : (_root_.Option externMethodLocalKind) := match arg0 with | .«EXTERN_METHOD ':' %» field0 => some (externMethodLocalKind.«EXTERN_METHOD ':' %» field0) | .«EXTERN_METHOD ABSTRACT ':' %» field0 => some (externMethodLocalKind.«EXTERN_METHOD ABSTRACT ':' %» field0) | _ => none


def «$find_local_return_type_t:case_5:downcast:0» (arg0 : localKind) : (_root_.Option externMethodLocalKind) := match arg0 with | .«EXTERN_METHOD ':' %» field0 => some (externMethodLocalKind.«EXTERN_METHOD ':' %» field0) | .«EXTERN_METHOD ABSTRACT ':' %» field0 => some (externMethodLocalKind.«EXTERN_METHOD ABSTRACT ':' %» field0) | _ => none


inductive matchKey : Type where
  | «% ':' %» : typeIR → nameIR → matchKey
deriving _root_.DecidableEq


inductive matchAction : Type where
  | «% `( % '@' % `)» : prefixedNameIR → (_root_.List parameterIR) → argumentListIR → matchAction
deriving _root_.DecidableEq

end SpecTec
