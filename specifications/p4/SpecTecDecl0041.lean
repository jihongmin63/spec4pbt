import SpecTecDecl0040

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$lift_typeIR_as_valueSetType:case_3:downcast:1» (arg0 : type) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «$lift_parserStatementIR:case_1:downcast:0» (arg0 : parserStatementIR) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «$lift_parserStatementIR:case_2:downcast:0» (arg0 : parserStatementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «$lift_parserStatementIR:case_3:downcast:0» (arg0 : parserStatementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «$lift_parserStatementIR:case_4:downcast:0» (arg0 : parserStatementIR) : (_root_.Option directApplicationStatementIR) := match arg0 with | .«% '.' APPLY `( % `) ';'» field0 field1 => some (directApplicationStatementIR.«% '.' APPLY `( % `) ';'» field0 field1) | _ => none


def «$lift_parserStatementIR:case_5:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserBlockStatementIR) := match arg0 with | .«% `{ % `}» field0 field1 => some (parserBlockStatementIR.«% `{ % `}» field0 field1) | _ => none


def «$lift_parserStatementIR:case_6:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «$lift_parserBlockElementStatementIR:case_1:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_parserBlockElementStatementIR:case_2:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_parserBlockElementStatementIR:case_3:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option parserStatementIR) := match arg0 with | .«';'» => some (parserStatementIR.«';'») | .«% % % ';'» field0 field1 field2 => some (parserStatementIR.«% % % ';'» field0 field1 field2) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (parserStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | .«% '.' APPLY `( % `) ';'» field0 field1 => some (parserStatementIR.«% '.' APPLY `( % `) ';'» field0 field1) | .«% `{ % `}» field0 field1 => some (parserStatementIR.«% `{ % `}» field0 field1) | .«IF `( % `) %» field0 field1 => some (parserStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «$lift_parserLocalDeclarationIR:case_1:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_parserLocalDeclarationIR:case_2:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option instantiationIR) := match arg0 with | .«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5 => some (instantiationIR.«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5) | _ => none


def «$lift_parserLocalDeclarationIR:case_3:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_parserLocalDeclarationIR:case_4:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option valueSetDeclarationIR) := match arg0 with | .«% VALUE_SET `< % `> `( % `) % ';'» field0 field1 field2 field3 => some (valueSetDeclarationIR.«% VALUE_SET `< % `> `( % `) % ';'» field0 field1 field2 field3) | _ => none


def «$lift_tablePropertyIR:case_1:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableKeysPropertyIR) := match arg0 with | .«KEY '=' `{ % `}» field0 => some (tableKeysPropertyIR.«KEY '=' `{ % `}» field0) | _ => none


def «$lift_tablePropertyIR:case_2:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableActionsPropertyIR) := match arg0 with | .«ACTIONS '=' `{ % `}» field0 => some (tableActionsPropertyIR.«ACTIONS '=' `{ % `}» field0) | _ => none


def «$lift_tablePropertyIR:case_3:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableDefaultActionPropertyIR) := match arg0 with | .«% % DEFAULT_ACTION '=' % ';'» field0 field1 field2 => some (tableDefaultActionPropertyIR.«% % DEFAULT_ACTION '=' % ';'» field0 field1 field2) | _ => none


def «$lift_tablePropertyIR:case_4:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableEntriesPropertyIR) := match arg0 with | .«% % ENTRIES '=' `{ % `}» field0 field1 field2 => some (tableEntriesPropertyIR.«% % ENTRIES '=' `{ % `}» field0 field1 field2) | _ => none


def «$lift_tablePropertyIR:case_5:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableCustomPropertyIR) := match arg0 with | .«% % CUSTOM % % ';'» field0 field1 field2 field3 => some (tableCustomPropertyIR.«% % CUSTOM % % ';'» field0 field1 field2 field3) | .«% % CUSTOM_CONST % % ';'» field0 field1 field2 field3 => some (tableCustomPropertyIR.«% % CUSTOM_CONST % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_controlLocalDeclarationIR:case_1:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_controlLocalDeclarationIR:case_2:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option instantiationIR) := match arg0 with | .«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5 => some (instantiationIR.«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5) | _ => none


def «$lift_controlLocalDeclarationIR:case_3:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_controlLocalDeclarationIR:case_4:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option actionDeclarationIR) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDeclarationIR.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «$lift_controlLocalDeclarationIR:case_5:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option tableDeclarationIR) := match arg0 with | .«% TABLE % % `{ % `}» field0 field1 field2 field3 => some (tableDeclarationIR.«% TABLE % % `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_typeDeclarationIR:case_1:downcast:0» (arg0 : typeDeclarationIR) : (_root_.Option derivedTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (derivedTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_typeDeclarationIR:case_2:downcast:0» (arg0 : typeDeclarationIR) : (_root_.Option typedefDeclarationIR) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «$lift_typeDeclarationIR:case_3:downcast:0» (arg0 : typeDeclarationIR) : (_root_.Option parserTypeDeclarationIR) := match arg0 with | .«% PARSER % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (parserTypeDeclarationIR.«% PARSER % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | _ => none


def «$lift_typeDeclarationIR:case_4:downcast:0» (arg0 : typeDeclarationIR) : (_root_.Option controlTypeDeclarationIR) := match arg0 with | .«% CONTROL % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (controlTypeDeclarationIR.«% CONTROL % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | _ => none


def «$lift_typeDeclarationIR:case_5:downcast:0» (arg0 : typeDeclarationIR) : (_root_.Option packageTypeDeclarationIR) := match arg0 with | .«% PACKAGE % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (packageTypeDeclarationIR.«% PACKAGE % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | _ => none


def «$lift_declarationIR:case_1:downcast:0» (arg0 : declarationIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_declarationIR:case_2:downcast:0» (arg0 : declarationIR) : (_root_.Option instantiationIR) := match arg0 with | .«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5 => some (instantiationIR.«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5) | _ => none


def «$lift_declarationIR:case_3:downcast:0» (arg0 : declarationIR) : (_root_.Option functionDeclarationIR) := match arg0 with | .«% % %» field0 field1 field2 => some (functionDeclarationIR.«% % %» field0 field1 field2) | _ => none

end SpecTec
