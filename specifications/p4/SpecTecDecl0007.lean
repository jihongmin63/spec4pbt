import SpecTecDecl0006

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive externObjectDeclaration : Type where
  | «% EXTERN % % `{ % `}» : annotationList → nonTypeName → typeParameterListOpt → externConstructorOrMethodPrototypeList → externObjectDeclaration
deriving _root_.DecidableEq


inductive externDeclaration : Type where
  | «% EXTERN % ';'» : annotationList → functionPrototype → externDeclaration
  | «% EXTERN % % `{ % `}» : annotationList → nonTypeName → typeParameterListOpt → externConstructorOrMethodPrototypeList → externDeclaration
deriving _root_.DecidableEq


inductive valueSetDeclaration : Type where
  | «% VALUE_SET `< % `> `( % `) % ';'» : annotationList → valueSetType → expression → name → valueSetDeclaration
deriving _root_.DecidableEq


inductive parserTypeDeclaration : Type where
  | «% PARSER % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → parserTypeDeclaration
deriving _root_.DecidableEq


mutual

inductive parserBlockElementStatementList : Type where
  | _EMPTY : parserBlockElementStatementList
  | «% %» : parserBlockElementStatementList → parserBlockElementStatement → parserBlockElementStatementList
deriving _root_.DecidableEq

inductive parserStatement : Type where
  | «';'» : parserStatement
  | «% % % ';'» : lvalue → assignop → expression → parserStatement
  | «% `( % `) ';'» : lvalue → argumentList → parserStatement
  | «% `< % `> `( % `) ';'» : lvalue → typeArgumentList → argumentList → parserStatement
  | «% '.' APPLY `( % `) ';'» : namedType → argumentList → parserStatement
  | «% `{ % `}» : annotationList → parserBlockElementStatementList → parserStatement
  | «IF `( % `) %» : expression → parserStatement → parserStatement
  | «IF `( % `) % ELSE %» : expression → parserStatement → parserStatement → parserStatement
deriving _root_.DecidableEq

inductive parserBlockElementStatement : Type where
  | «% CONST % % % ';'» : annotationList → type → name → initializer → parserBlockElementStatement
  | «% % % % ';'» : annotationList → type → name → initializerOpt → parserBlockElementStatement
  | «';'» : parserBlockElementStatement
  | «% % % ';'» : lvalue → assignop → expression → parserBlockElementStatement
  | «% `( % `) ';'» : lvalue → argumentList → parserBlockElementStatement
  | «% `< % `> `( % `) ';'» : lvalue → typeArgumentList → argumentList → parserBlockElementStatement
  | «% '.' APPLY `( % `) ';'» : namedType → argumentList → parserBlockElementStatement
  | «% `{ % `}» : annotationList → parserBlockElementStatementList → parserBlockElementStatement
  | «IF `( % `) %» : expression → parserStatement → parserBlockElementStatement
  | «IF `( % `) % ELSE %» : expression → parserStatement → parserStatement → parserBlockElementStatement
deriving _root_.DecidableEq

end


inductive parserBlockStatement : Type where
  | «% `{ % `}» : annotationList → parserBlockElementStatementList → parserBlockStatement
deriving _root_.DecidableEq


inductive parserConditionalStatement : Type where
  | «IF `( % `) %» : expression → parserStatement → parserConditionalStatement
  | «IF `( % `) % ELSE %» : expression → parserStatement → parserStatement → parserConditionalStatement
deriving _root_.DecidableEq


inductive parserState : Type where
  | «% STATE % `{ % % `}» : annotationList → name → parserBlockElementStatementList → transitionStatement → parserState
deriving _root_.DecidableEq


inductive parserStateList : Type where
  | «% STATE % `{ % % `}» : annotationList → name → parserBlockElementStatementList → transitionStatement → parserStateList
  | «% %» : parserStateList → parserState → parserStateList
deriving _root_.DecidableEq


def «$flatten_parserStateList:case_1:downcast:0» (arg0 : parserStateList) : (_root_.Option parserState) := match arg0 with | .«% STATE % `{ % % `}» field0 field1 field2 field3 => some (parserState.«% STATE % `{ % % `}» field0 field1 field2 field3) | _ => none


inductive parserLocalDeclaration : Type where
  | «% CONST % % % ';'» : annotationList → type → name → initializer → parserLocalDeclaration
  | «% % `( % `) % ';'» : annotationList → type → argumentList → name → parserLocalDeclaration
  | «% % `( % `) % % ';'» : annotationList → type → argumentList → name → objectInitializer → parserLocalDeclaration
  | «% % % % ';'» : annotationList → type → name → initializerOpt → parserLocalDeclaration
  | «% VALUE_SET `< % `> `( % `) % ';'» : annotationList → valueSetType → expression → name → parserLocalDeclaration
deriving _root_.DecidableEq


inductive parserLocalDeclarationList : Type where
  | _EMPTY : parserLocalDeclarationList
  | «% %» : parserLocalDeclarationList → parserLocalDeclaration → parserLocalDeclarationList
deriving _root_.DecidableEq


inductive parserDeclaration : Type where
  | «% PARSER % % `( % `) % `{ % % `}» : annotationList → name → typeParameterListOpt → parameterList → constructorParameterListOpt → parserLocalDeclarationList → parserStateList → parserDeclaration
deriving _root_.DecidableEq


inductive tableKey : Type where
  | «% ':' % % ';'» : expression → name → annotationList → tableKey
deriving _root_.DecidableEq


inductive tableKeyList : Type where
  | _EMPTY : tableKeyList
  | «% %» : tableKeyList → tableKey → tableKeyList
deriving _root_.DecidableEq


inductive tableAction : Type where
  | «% % ';'» : annotationList → tableActionReference → tableAction
deriving _root_.DecidableEq


inductive tableActionList : Type where
  | _EMPTY : tableActionList
  | «% %» : tableActionList → tableAction → tableActionList
deriving _root_.DecidableEq


inductive tableEntry : Type where
  | «% % % ':' % % ';'» : constOpt → tableEntryPriority → keysetExpression → tableActionReference → annotationList → tableEntry
  | «% % ':' % % ';'» : constOpt → keysetExpression → tableActionReference → annotationList → tableEntry
deriving _root_.DecidableEq


inductive tableEntryList : Type where
  | _EMPTY : tableEntryList
  | «% %» : tableEntryList → tableEntry → tableEntryList
deriving _root_.DecidableEq


inductive tableProperty : Type where
  | «KEY '=' `{ % `}» : tableKeyList → tableProperty
  | «ACTIONS '=' `{ % `}» : tableActionList → tableProperty
  | «% % ENTRIES '=' `{ % `}» : annotationList → constOpt → tableEntryList → tableProperty
  | «% % % % ';'» : annotationList → constOpt → tableCustomName → initializer → tableProperty
deriving _root_.DecidableEq


inductive tablePropertyList : Type where
  | _EMPTY : tablePropertyList
  | «% %» : tablePropertyList → tableProperty → tablePropertyList
deriving _root_.DecidableEq


inductive tableDeclaration : Type where
  | «% TABLE % `{ % `}» : annotationList → name → tablePropertyList → tableDeclaration
deriving _root_.DecidableEq


inductive controlTypeDeclaration : Type where
  | «% CONTROL % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → controlTypeDeclaration
deriving _root_.DecidableEq


abbrev controlBody : Type := blockStatement


inductive controlLocalDeclaration : Type where
  | «% CONST % % % ';'» : annotationList → type → name → initializer → controlLocalDeclaration
  | «% % `( % `) % ';'» : annotationList → type → argumentList → name → controlLocalDeclaration
  | «% % `( % `) % % ';'» : annotationList → type → argumentList → name → objectInitializer → controlLocalDeclaration
  | «% % % % ';'» : annotationList → type → name → initializerOpt → controlLocalDeclaration
  | «% ACTION % `( % `) %» : annotationList → name → parameterList → blockStatement → controlLocalDeclaration
  | «% TABLE % `{ % `}» : annotationList → name → tablePropertyList → controlLocalDeclaration
deriving _root_.DecidableEq


inductive controlLocalDeclarationList : Type where
  | _EMPTY : controlLocalDeclarationList
  | «% %» : controlLocalDeclarationList → controlLocalDeclaration → controlLocalDeclarationList
deriving _root_.DecidableEq


inductive controlDeclaration : Type where
  | «% CONTROL % % `( % `) % `{ % APPLY % `}» : annotationList → name → typeParameterListOpt → parameterList → constructorParameterListOpt → controlLocalDeclarationList → controlBody → controlDeclaration
deriving _root_.DecidableEq


inductive packageTypeDeclaration : Type where
  | «% PACKAGE % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → packageTypeDeclaration
deriving _root_.DecidableEq


inductive typeDeclaration : Type where
  | «% ENUM % `{ % % `}» : annotationList → name → nameList → trailingCommaOpt → typeDeclaration
  | «% ENUM % % `{ % % `}» : annotationList → type → name → namedExpressionList → trailingCommaOpt → typeDeclaration
  | «% STRUCT % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → typeDeclaration
  | «% HEADER % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → typeDeclaration
  | «% HEADER_UNION % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → typeDeclaration
  | «% TYPEDEF % % ';'» : annotationList → typedef → name → typeDeclaration
  | «% TYPE % % ';'» : annotationList → type → name → typeDeclaration
  | «% PARSER % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → typeDeclaration
  | «% CONTROL % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → typeDeclaration
  | «% PACKAGE % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → typeDeclaration
deriving _root_.DecidableEq


inductive declaration : Type where
  | «% CONST % % % ';'» : annotationList → type → name → initializer → declaration
  | «% % `( % `) % ';'» : annotationList → type → argumentList → name → declaration
  | «% % `( % `) % % ';'» : annotationList → type → argumentList → name → objectInitializer → declaration
  | «% % %» : annotationList → functionPrototype → blockStatement → declaration
  | «% ACTION % `( % `) %» : annotationList → name → parameterList → blockStatement → declaration
  | «ERROR `{ % `}» : nameList → declaration
  | «MATCH_KIND `{ % % `}» : nameList → trailingCommaOpt → declaration
  | «% EXTERN % ';'» : annotationList → functionPrototype → declaration
  | «% EXTERN % % `{ % `}» : annotationList → nonTypeName → typeParameterListOpt → externConstructorOrMethodPrototypeList → declaration
  | «% PARSER % % `( % `) % `{ % % `}» : annotationList → name → typeParameterListOpt → parameterList → constructorParameterListOpt → parserLocalDeclarationList → parserStateList → declaration
  | «% CONTROL % % `( % `) % `{ % APPLY % `}» : annotationList → name → typeParameterListOpt → parameterList → constructorParameterListOpt → controlLocalDeclarationList → controlBody → declaration
  | «% ENUM % `{ % % `}» : annotationList → name → nameList → trailingCommaOpt → declaration
  | «% ENUM % % `{ % % `}» : annotationList → type → name → namedExpressionList → trailingCommaOpt → declaration
  | «% STRUCT % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → declaration
  | «% HEADER % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → declaration
  | «% HEADER_UNION % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → declaration
  | «% TYPEDEF % % ';'» : annotationList → typedef → name → declaration
  | «% TYPE % % ';'» : annotationList → type → name → declaration
  | «% PARSER % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → declaration
  | «% CONTROL % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → declaration
  | «% PACKAGE % % `( % `) ';'» : annotationList → name → typeParameterListOpt → parameterList → declaration
deriving _root_.DecidableEq


def «$flatten_annotationList:case_2:downcast:0» (arg0 : annotationList) : (_root_.Option annotation) := match arg0 with | .«'@' %» field0 => some (annotation.«'@' %» field0) | .«'@' % `( % `)» field0 field1 => some (annotation.«'@' % `( % `)» field0 field1) | .«'@' % `[ % `]» field0 field1 => some (annotation.«'@' % `[ % `]» field0 field1) | .«'@' PRAGMA % %» field0 field1 => some (annotation.«'@' PRAGMA % %» field0 field1) | _ => none


def «$flatten_annotationList:case_3:downcast:0» (arg0 : annotationList) : (_root_.Option annotationListNonEmpty) := match arg0 with | .«'@' %» field0 => some (annotationListNonEmpty.«'@' %» field0) | .«'@' % `( % `)» field0 field1 => some (annotationListNonEmpty.«'@' % `( % `)» field0 field1) | .«'@' % `[ % `]» field0 field1 => some (annotationListNonEmpty.«'@' % `[ % `]» field0 field1) | .«'@' PRAGMA % %» field0 field1 => some (annotationListNonEmpty.«'@' PRAGMA % %» field0 field1) | .«% %» field0 field1 => some (annotationListNonEmpty.«% %» field0 field1) | _ => none

end SpecTec
