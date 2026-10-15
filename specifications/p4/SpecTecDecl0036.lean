import SpecTecDecl0035

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

abbrev parserStateListIR : Type := (_root_.List parserStateIR)


inductive parserLocalDeclarationIR : Type where
  | «% CONST % % % ';'» : annotationList → typeIR → nameIR → constantInitializerIR → parserLocalDeclarationIR
  | «% % % `( % `) % % ';'» : annotationList → typeIR → constructorTargetIR → argumentListIR → nameIR → objectInitializerOptIR → parserLocalDeclarationIR
  | «% % % % ';'» : annotationList → typeIR → nameIR → initializerOptIR → parserLocalDeclarationIR
  | «% VALUE_SET `< % `> `( % `) % ';'» : annotationList → typeIR → typedExpressionIR → nameIR → parserLocalDeclarationIR
deriving _root_.DecidableEq


abbrev parserLocalDeclarationListIR : Type := (_root_.List parserLocalDeclarationIR)


inductive parserDeclarationIR : Type where
  | «% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → constructorParameterListIR → parserLocalDeclarationListIR → parserStateListIR → parserDeclarationIR
deriving _root_.DecidableEq


abbrev constIR : Type := const


abbrev constOptIR : Type := (_root_.Option constIR)


inductive tableKeyIR : Type where
  | «% '#' % ':' % % ';'» : typedExpressionIR → nameIR → nameIR → annotationList → tableKeyIR
deriving _root_.DecidableEq


abbrev tableKeyListIR : Type := (_root_.List tableKeyIR)


abbrev controlPlaneNameIR : Type := (_root_.Option nameIR)


inductive tableActionReferenceIR : Type where
  | «% % `( % `)» : prefixedNameIR → controlPlaneNameIR → argumentListIR → tableActionReferenceIR
deriving _root_.DecidableEq


inductive tableActionIR : Type where
  | «% % '#' `( % ',' % `) ';'» : annotationList → tableActionReferenceIR → parameterListIR → parameterListIR → tableActionIR
deriving _root_.DecidableEq


abbrev tableActionListIR : Type := (_root_.List tableActionIR)


inductive tableEntryPriorityIR : Type where
  | «PRIORITY '=' % ':'» : integerLiteral → tableEntryPriorityIR
deriving _root_.DecidableEq


abbrev tableEntryPriorityOptIR : Type := (_root_.Option tableEntryPriorityIR)


inductive tableEntryIR : Type where
  | «% % % ':' % % ';'» : constOptIR → tableEntryPriorityOptIR → keysetExpressionIR → tableActionReferenceIR → annotationList → tableEntryIR
deriving _root_.DecidableEq


abbrev tableEntryListIR : Type := (_root_.List tableEntryIR)


inductive tableKeysPropertyIR : Type where
  | «KEY '=' `{ % `}» : tableKeyListIR → tableKeysPropertyIR
deriving _root_.DecidableEq


inductive tableActionsPropertyIR : Type where
  | «ACTIONS '=' `{ % `}» : tableActionListIR → tableActionsPropertyIR
deriving _root_.DecidableEq


inductive tableDefaultActionPropertyIR : Type where
  | «% % DEFAULT_ACTION '=' % ';'» : annotationList → constOptIR → tableActionReferenceIR → tableDefaultActionPropertyIR
deriving _root_.DecidableEq


inductive tableEntriesPropertyIR : Type where
  | «% % ENTRIES '=' `{ % `}» : annotationList → constOptIR → tableEntryListIR → tableEntriesPropertyIR
deriving _root_.DecidableEq


inductive tableCustomPropertyIR : Type where
  | «% % CUSTOM % % ';'» : annotationList → constOptIR → nameIR → initializerIR → tableCustomPropertyIR
  | «% % CUSTOM_CONST % % ';'» : annotationList → constOptIR → nameIR → constantInitializerIR → tableCustomPropertyIR
deriving _root_.DecidableEq


inductive tablePropertyIR : Type where
  | «KEY '=' `{ % `}» : tableKeyListIR → tablePropertyIR
  | «ACTIONS '=' `{ % `}» : tableActionListIR → tablePropertyIR
  | «% % DEFAULT_ACTION '=' % ';'» : annotationList → constOptIR → tableActionReferenceIR → tablePropertyIR
  | «% % ENTRIES '=' `{ % `}» : annotationList → constOptIR → tableEntryListIR → tablePropertyIR
  | «% % CUSTOM % % ';'» : annotationList → constOptIR → nameIR → initializerIR → tablePropertyIR
  | «% % CUSTOM_CONST % % ';'» : annotationList → constOptIR → nameIR → constantInitializerIR → tablePropertyIR
deriving _root_.DecidableEq


abbrev tablePropertyListIR : Type := (_root_.List tablePropertyIR)


inductive tableDeclarationIR : Type where
  | «% TABLE % % `{ % `}» : annotationList → typeIR → nameIR → tablePropertyListIR → tableDeclarationIR
deriving _root_.DecidableEq


inductive controlTypeDeclarationIR : Type where
  | «% CONTROL % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → controlTypeDeclarationIR
deriving _root_.DecidableEq


abbrev controlBodyIR : Type := blockStatementIR


inductive controlLocalDeclarationIR : Type where
  | «% CONST % % % ';'» : annotationList → typeIR → nameIR → constantInitializerIR → controlLocalDeclarationIR
  | «% % % `( % `) % % ';'» : annotationList → typeIR → constructorTargetIR → argumentListIR → nameIR → objectInitializerOptIR → controlLocalDeclarationIR
  | «% % % % ';'» : annotationList → typeIR → nameIR → initializerOptIR → controlLocalDeclarationIR
  | «% ACTION % `( % `) %» : annotationList → nameIR → parameterListIR → blockStatementIR → controlLocalDeclarationIR
  | «% TABLE % % `{ % `}» : annotationList → typeIR → nameIR → tablePropertyListIR → controlLocalDeclarationIR
deriving _root_.DecidableEq


abbrev controlLocalDeclarationListIR : Type := (_root_.List controlLocalDeclarationIR)


inductive controlDeclarationIR : Type where
  | «% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → constructorParameterListIR → controlLocalDeclarationListIR → controlBodyIR → controlDeclarationIR
deriving _root_.DecidableEq


inductive packageTypeDeclarationIR : Type where
  | «% PACKAGE % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → packageTypeDeclarationIR
deriving _root_.DecidableEq


inductive typeDeclarationIR : Type where
  | «% ENUM % `{ % `}» : annotationList → nameIR → nameListIR → typeDeclarationIR
  | «% ENUM % % `{ % `}» : annotationList → typeIR → nameIR → namedValueListIR → typeDeclarationIR
  | «% STRUCT % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → typeDeclarationIR
  | «% HEADER % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → typeDeclarationIR
  | «% HEADER_UNION % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → typeDeclarationIR
  | «% TYPEDEF % % ';'» : annotationList → typedefIR → nameIR → typeDeclarationIR
  | «% TYPE % % ';'» : annotationList → typeIR → nameIR → typeDeclarationIR
  | «% PARSER % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → typeDeclarationIR
  | «% CONTROL % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → typeDeclarationIR
  | «% PACKAGE % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → typeDeclarationIR
deriving _root_.DecidableEq


inductive declarationIR : Type where
  | «% CONST % % % ';'» : annotationList → typeIR → nameIR → constantInitializerIR → declarationIR
  | «% % % `( % `) % % ';'» : annotationList → typeIR → constructorTargetIR → argumentListIR → nameIR → objectInitializerOptIR → declarationIR
  | «% % %» : annotationList → functionPrototypeIR → blockStatementIR → declarationIR
  | «% ACTION % `( % `) %» : annotationList → nameIR → parameterListIR → blockStatementIR → declarationIR
  | «ERROR `{ % `}» : nameListIR → declarationIR
  | «MATCH_KIND `{ % `}» : nameListIR → declarationIR
  | «% EXTERN % ';'» : annotationList → functionPrototypeIR → declarationIR
  | «% EXTERN % `< % ',' `> `{ % % `}» : annotationList → nameIR → typeParameterListIR → externConstructorPrototypeListIR → externMethodPrototypeListIR → declarationIR
  | «% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → constructorParameterListIR → parserLocalDeclarationListIR → parserStateListIR → declarationIR
  | «% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → constructorParameterListIR → controlLocalDeclarationListIR → controlBodyIR → declarationIR
  | «% ENUM % `{ % `}» : annotationList → nameIR → nameListIR → declarationIR
  | «% ENUM % % `{ % `}» : annotationList → typeIR → nameIR → namedValueListIR → declarationIR
  | «% STRUCT % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → declarationIR
  | «% HEADER % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → declarationIR
  | «% HEADER_UNION % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → declarationIR
  | «% TYPEDEF % % ';'» : annotationList → typedefIR → nameIR → declarationIR
  | «% TYPE % % ';'» : annotationList → typeIR → nameIR → declarationIR
  | «% PARSER % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → declarationIR
  | «% CONTROL % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → declarationIR
  | «% PACKAGE % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → declarationIR
deriving _root_.DecidableEq

end SpecTec
