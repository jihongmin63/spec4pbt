import SpecTecDecl0005

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive constructorParameterListOpt : Type where
  | _EMPTY : constructorParameterListOpt
  | «`( % `)» : parameterList → constructorParameterListOpt
deriving _root_.DecidableEq


inductive forInitStatement : Type where
  | «% % % %» : annotationList → type → name → initializerOpt → forInitStatement
  | «% `( % `)» : lvalue → argumentList → forInitStatement
  | «% `< % `> `( % `)» : lvalue → typeArgumentList → argumentList → forInitStatement
  | «% % %» : lvalue → assignop → expression → forInitStatement
deriving _root_.DecidableEq


inductive forInitStatementListNonEmpty : Type where
  | «% % % %» : annotationList → type → name → initializerOpt → forInitStatementListNonEmpty
  | «% `( % `)» : lvalue → argumentList → forInitStatementListNonEmpty
  | «% `< % `> `( % `)» : lvalue → typeArgumentList → argumentList → forInitStatementListNonEmpty
  | «% % %» : lvalue → assignop → expression → forInitStatementListNonEmpty
  | «% ',' %» : forInitStatementListNonEmpty → forInitStatement → forInitStatementListNonEmpty
deriving _root_.DecidableEq


inductive forInitStatementList : Type where
  | _EMPTY : forInitStatementList
  | «% % % %» : annotationList → type → name → initializerOpt → forInitStatementList
  | «% `( % `)» : lvalue → argumentList → forInitStatementList
  | «% `< % `> `( % `)» : lvalue → typeArgumentList → argumentList → forInitStatementList
  | «% % %» : lvalue → assignop → expression → forInitStatementList
  | «% ',' %» : forInitStatementListNonEmpty → forInitStatement → forInitStatementList
deriving _root_.DecidableEq


mutual

inductive blockStatement : Type where
  | «% `{ % `}» : annotationList → blockElementStatementList → blockStatement
deriving _root_.DecidableEq

inductive switchCase : Type where
  | «% ':' %» : switchLabel → blockStatement → switchCase
  | «% ':'» : switchLabel → switchCase
deriving _root_.DecidableEq

inductive switchCaseList : Type where
  | _EMPTY : switchCaseList
  | «% %» : switchCaseList → switchCase → switchCaseList
deriving _root_.DecidableEq

inductive statement : Type where
  | «';'» : statement
  | «% % % ';'» : lvalue → assignop → expression → statement
  | «% `( % `) ';'» : lvalue → argumentList → statement
  | «% `< % `> `( % `) ';'» : lvalue → typeArgumentList → argumentList → statement
  | «% '.' APPLY `( % `) ';'» : namedType → argumentList → statement
  | «RETURN ';'» : statement
  | «RETURN % ';'» : expression → statement
  | «EXIT ';'» : statement
  | «% `{ % `}» : annotationList → blockElementStatementList → statement
  | «IF `( % `) %» : expression → statement → statement
  | «IF `( % `) % ELSE %» : expression → statement → statement → statement
  | «% FOR `( % ';' % ';' % `) %» : annotationList → forInitStatementList → expression → forUpdateStatementList → statement → statement
  | «% FOR `( % % IN % `) %» : annotationList → type → name → forCollectionExpression → statement → statement
  | «% FOR `( % % % IN % `) %» : annotationList → annotationListNonEmpty → type → name → forCollectionExpression → statement → statement
  | «BREAK ';'» : statement
  | «CONTINUE ';'» : statement
  | «SWITCH `( % `) `{ % `}» : expression → switchCaseList → statement
deriving _root_.DecidableEq

inductive blockElementStatement : Type where
  | «% CONST % % % ';'» : annotationList → type → name → initializer → blockElementStatement
  | «% % % % ';'» : annotationList → type → name → initializerOpt → blockElementStatement
  | «';'» : blockElementStatement
  | «% % % ';'» : lvalue → assignop → expression → blockElementStatement
  | «% `( % `) ';'» : lvalue → argumentList → blockElementStatement
  | «% `< % `> `( % `) ';'» : lvalue → typeArgumentList → argumentList → blockElementStatement
  | «% '.' APPLY `( % `) ';'» : namedType → argumentList → blockElementStatement
  | «RETURN ';'» : blockElementStatement
  | «RETURN % ';'» : expression → blockElementStatement
  | «EXIT ';'» : blockElementStatement
  | «% `{ % `}» : annotationList → blockElementStatementList → blockElementStatement
  | «IF `( % `) %» : expression → statement → blockElementStatement
  | «IF `( % `) % ELSE %» : expression → statement → statement → blockElementStatement
  | «% FOR `( % ';' % ';' % `) %» : annotationList → forInitStatementList → expression → forUpdateStatementList → statement → blockElementStatement
  | «% FOR `( % % IN % `) %» : annotationList → type → name → forCollectionExpression → statement → blockElementStatement
  | «% FOR `( % % % IN % `) %» : annotationList → annotationListNonEmpty → type → name → forCollectionExpression → statement → blockElementStatement
  | «BREAK ';'» : blockElementStatement
  | «CONTINUE ';'» : blockElementStatement
  | «SWITCH `( % `) `{ % `}» : expression → switchCaseList → blockElementStatement
deriving _root_.DecidableEq

inductive blockElementStatementList : Type where
  | _EMPTY : blockElementStatementList
  | «% %» : blockElementStatementList → blockElementStatement → blockElementStatementList
deriving _root_.DecidableEq

end


inductive conditionalStatement : Type where
  | «IF `( % `) %» : expression → statement → conditionalStatement
  | «IF `( % `) % ELSE %» : expression → statement → statement → conditionalStatement
deriving _root_.DecidableEq


def «$flatten_forInitStatementList:case_2:downcast:0» (arg0 : forInitStatementList) : (_root_.Option forInitStatement) := match arg0 with | .«% % % %» field0 field1 field2 field3 => some (forInitStatement.«% % % %» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (forInitStatement.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (forInitStatement.«% `< % `> `( % `)» field0 field1 field2) | .«% % %» field0 field1 field2 => some (forInitStatement.«% % %» field0 field1 field2) | _ => none


def «$flatten_forInitStatementList:case_3:downcast:0» (arg0 : forInitStatementList) : (_root_.Option forInitStatementListNonEmpty) := match arg0 with | .«% % % %» field0 field1 field2 field3 => some (forInitStatementListNonEmpty.«% % % %» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (forInitStatementListNonEmpty.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (forInitStatementListNonEmpty.«% `< % `> `( % `)» field0 field1 field2) | .«% % %» field0 field1 field2 => some (forInitStatementListNonEmpty.«% % %» field0 field1 field2) | .«% ',' %» field0 field1 => some (forInitStatementListNonEmpty.«% ',' %» field0 field1) | _ => none


inductive forStatement : Type where
  | «% FOR `( % ';' % ';' % `) %» : annotationList → forInitStatementList → expression → forUpdateStatementList → statement → forStatement
  | «% FOR `( % % IN % `) %» : annotationList → type → name → forCollectionExpression → statement → forStatement
  | «% FOR `( % % % IN % `) %» : annotationList → annotationListNonEmpty → type → name → forCollectionExpression → statement → forStatement
deriving _root_.DecidableEq


inductive switchStatement : Type where
  | «SWITCH `( % `) `{ % `}» : expression → switchCaseList → switchStatement
deriving _root_.DecidableEq


inductive constantDeclaration : Type where
  | «% CONST % % % ';'» : annotationList → type → name → initializer → constantDeclaration
deriving _root_.DecidableEq


inductive variableDeclaration : Type where
  | «% % % % ';'» : annotationList → type → name → initializerOpt → variableDeclaration
deriving _root_.DecidableEq


inductive functionPrototype : Type where
  | «% % % `( % `)» : typeOrVoid → name → typeParameterListOpt → parameterList → functionPrototype
deriving _root_.DecidableEq


inductive functionDeclaration : Type where
  | «% % %» : annotationList → functionPrototype → blockStatement → functionDeclaration
deriving _root_.DecidableEq


inductive actionDeclaration : Type where
  | «% ACTION % `( % `) %» : annotationList → name → parameterList → blockStatement → actionDeclaration
deriving _root_.DecidableEq


mutual

inductive objectInitializer : Type where
  | «'=' `{ % `}» : objectDeclarationList → objectInitializer
deriving _root_.DecidableEq

inductive objectDeclaration : Type where
  | «% % %» : annotationList → functionPrototype → blockStatement → objectDeclaration
  | «% % `( % `) % ';'» : annotationList → type → argumentList → name → objectDeclaration
  | «% % `( % `) % % ';'» : annotationList → type → argumentList → name → objectInitializer → objectDeclaration
deriving _root_.DecidableEq

inductive objectDeclarationList : Type where
  | _EMPTY : objectDeclarationList
  | «% %» : objectDeclarationList → objectDeclaration → objectDeclarationList
deriving _root_.DecidableEq

end


inductive instantiation : Type where
  | «% % `( % `) % ';'» : annotationList → type → argumentList → name → instantiation
  | «% % `( % `) % % ';'» : annotationList → type → argumentList → name → objectInitializer → instantiation
deriving _root_.DecidableEq


inductive enumTypeDeclaration : Type where
  | «% ENUM % `{ % % `}» : annotationList → name → nameList → trailingCommaOpt → enumTypeDeclaration
  | «% ENUM % % `{ % % `}» : annotationList → type → name → namedExpressionList → trailingCommaOpt → enumTypeDeclaration
deriving _root_.DecidableEq


inductive typeField : Type where
  | «% % % ';'» : annotationList → type → name → typeField
deriving _root_.DecidableEq


inductive typeFieldList : Type where
  | _EMPTY : typeFieldList
  | «% %» : typeFieldList → typeField → typeFieldList
deriving _root_.DecidableEq


inductive structTypeDeclaration : Type where
  | «% STRUCT % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → structTypeDeclaration
deriving _root_.DecidableEq


inductive headerTypeDeclaration : Type where
  | «% HEADER % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → headerTypeDeclaration
deriving _root_.DecidableEq


inductive headerUnionTypeDeclaration : Type where
  | «% HEADER_UNION % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → headerUnionTypeDeclaration
deriving _root_.DecidableEq


inductive derivedTypeDeclaration : Type where
  | «% ENUM % `{ % % `}» : annotationList → name → nameList → trailingCommaOpt → derivedTypeDeclaration
  | «% ENUM % % `{ % % `}» : annotationList → type → name → namedExpressionList → trailingCommaOpt → derivedTypeDeclaration
  | «% STRUCT % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → derivedTypeDeclaration
  | «% HEADER % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → derivedTypeDeclaration
  | «% HEADER_UNION % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → derivedTypeDeclaration
deriving _root_.DecidableEq


inductive typedef : Type where
  | BOOL : typedef
  | ERROR : typedef
  | MATCH_KIND : typedef
  | STRING : typedef
  | INT : typedef
  | «INT `< % `>» : _root_.Int → typedef
  | «INT `< `( % `) `>» : expression → typedef
  | BIT : typedef
  | «BIT `< % `>» : _root_.Int → typedef
  | «BIT `< `( % `) `>» : expression → typedef
  | «VARBIT `< % `>» : _root_.Int → typedef
  | «VARBIT `< `( % `) `>» : expression → typedef
  | _TID : _root_.String → typedef
  | «_TID '.' %» : typeName → typedef
  | «% `< % `>» : prefixedTypeName → typeArgumentList → typedef
  | «% `[ % `]» : type → expression → typedef
  | «LIST `< % `>» : typeArgument → typedef
  | «TUPLE `< % `>» : typeArgumentList → typedef
  | «% ENUM % `{ % % `}» : annotationList → name → nameList → trailingCommaOpt → typedef
  | «% ENUM % % `{ % % `}» : annotationList → type → name → namedExpressionList → trailingCommaOpt → typedef
  | «% STRUCT % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → typedef
  | «% HEADER % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → typedef
  | «% HEADER_UNION % % `{ % `}» : annotationList → name → typeParameterListOpt → typeFieldList → typedef
deriving _root_.DecidableEq


inductive typedefDeclaration : Type where
  | «% TYPEDEF % % ';'» : annotationList → typedef → name → typedefDeclaration
  | «% TYPE % % ';'» : annotationList → type → name → typedefDeclaration
deriving _root_.DecidableEq


inductive externFunctionDeclaration : Type where
  | «% EXTERN % ';'» : annotationList → functionPrototype → externFunctionDeclaration
deriving _root_.DecidableEq


inductive externConstructorPrototype : Type where
  | «% % `( % `) ';'» : annotationList → typeIdentifier → parameterList → externConstructorPrototype
deriving _root_.DecidableEq


inductive externMethodPrototype : Type where
  | «% % ';'» : annotationList → functionPrototype → externMethodPrototype
  | «% ABSTRACT % ';'» : annotationList → functionPrototype → externMethodPrototype
deriving _root_.DecidableEq


inductive externConstructorOrMethodPrototype : Type where
  | «% % `( % `) ';'» : annotationList → typeIdentifier → parameterList → externConstructorOrMethodPrototype
  | «% % ';'» : annotationList → functionPrototype → externConstructorOrMethodPrototype
  | «% ABSTRACT % ';'» : annotationList → functionPrototype → externConstructorOrMethodPrototype
deriving _root_.DecidableEq


def «$is_externConstructorPrototype:case_1:downcast:0» (arg0 : externConstructorOrMethodPrototype) : (_root_.Option externConstructorPrototype) := match arg0 with | .«% % `( % `) ';'» field0 field1 field2 => some (externConstructorPrototype.«% % `( % `) ';'» field0 field1 field2) | _ => none


inductive externConstructorOrMethodPrototypeList : Type where
  | _EMPTY : externConstructorOrMethodPrototypeList
  | «% %» : externConstructorOrMethodPrototypeList → externConstructorOrMethodPrototype → externConstructorOrMethodPrototypeList
deriving _root_.DecidableEq

end SpecTec
