import SpecTecDecl0039

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$lift_statementIR:case_1:downcast:0» (arg0 : statementIR) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «$lift_statementIR:case_2:downcast:0» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «$lift_statementIR:case_3:downcast:0» (arg0 : statementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «$lift_statementIR:case_4:downcast:0» (arg0 : statementIR) : (_root_.Option directApplicationStatementIR) := match arg0 with | .«% '.' APPLY `( % `) ';'» field0 field1 => some (directApplicationStatementIR.«% '.' APPLY `( % `) ';'» field0 field1) | _ => none


def «$lift_statementIR:case_5:downcast:0» (arg0 : statementIR) : (_root_.Option returnStatementIR) := match arg0 with | .«RETURN ';'» => some (returnStatementIR.«RETURN ';'») | .«RETURN % ';'» field0 => some (returnStatementIR.«RETURN % ';'» field0) | _ => none


def «$lift_statementIR:case_6:downcast:0» (arg0 : statementIR) : (_root_.Option exitStatement) := match arg0 with | .«EXIT ';'» => some (exitStatement.«EXIT ';'») | _ => none


def «$lift_statementIR:case_7:downcast:0» (arg0 : statementIR) : (_root_.Option blockStatementIR) := match arg0 with | .«% `{ % `}» field0 field1 => some (blockStatementIR.«% `{ % `}» field0 field1) | _ => none


def «$lift_statementIR:case_8:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «$lift_statementIR:case_9:downcast:0» (arg0 : statementIR) : (_root_.Option switchStatementIR) := match arg0 with | .«SWITCH `( % `) `{ % `}» field0 field1 => some (switchStatementIR.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «$lift_typedLvalueIR:case_2:downcast:0» (arg0 : lvalueIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$lift_typedLvalueIR:case_3:downcast:0» (arg0 : lvalueIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$lift_callableTargetIR_as_lvalue:case_2:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$lift_callableTargetIR_as_lvalue:case_3:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «$lift_blockElementStatementIR:case_1:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_blockElementStatementIR:case_2:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «$lift_blockElementStatementIR:case_3:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option statementIR) := match arg0 with | .«';'» => some (statementIR.«';'») | .«% % % ';'» field0 field1 field2 => some (statementIR.«% % % ';'» field0 field1 field2) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (statementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | .«% '.' APPLY `( % `) ';'» field0 field1 => some (statementIR.«% '.' APPLY `( % `) ';'» field0 field1) | .«RETURN ';'» => some (statementIR.«RETURN ';'») | .«RETURN % ';'» field0 => some (statementIR.«RETURN % ';'» field0) | .«EXIT ';'» => some (statementIR.«EXIT ';'») | .«% `{ % `}» field0 field1 => some (statementIR.«% `{ % `}» field0 field1) | .«IF `( % `) %» field0 field1 => some (statementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (statementIR.«IF `( % `) % ELSE %» field0 field1 field2) | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (statementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (statementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (statementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | .«BREAK ';'» => some (statementIR.«BREAK ';'») | .«CONTINUE ';'» => some (statementIR.«CONTINUE ';'») | .«SWITCH `( % `) `{ % `}» field0 field1 => some (statementIR.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «$lift_switchLabelIR:case_2:downcast:0» (arg0 : switchLabelIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$lift_objectDeclarationIR:case_1:downcast:0» (arg0 : objectDeclarationIR) : (_root_.Option functionDeclarationIR) := match arg0 with | .«% % %» field0 field1 field2 => some (functionDeclarationIR.«% % %» field0 field1 field2) | _ => none


def «$lift_objectDeclarationIR:case_2:downcast:0» (arg0 : objectDeclarationIR) : (_root_.Option instantiationIR) := match arg0 with | .«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5 => some (instantiationIR.«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5) | _ => none


def «$lift_derivedTypeDeclarationIR:case_1:downcast:0» (arg0 : derivedTypeDeclarationIR) : (_root_.Option enumTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (enumTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (enumTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_derivedTypeDeclarationIR:case_2:downcast:0» (arg0 : derivedTypeDeclarationIR) : (_root_.Option structTypeDeclarationIR) := match arg0 with | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (structTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_derivedTypeDeclarationIR:case_3:downcast:0» (arg0 : derivedTypeDeclarationIR) : (_root_.Option headerTypeDeclarationIR) := match arg0 with | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (headerTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_derivedTypeDeclarationIR:case_4:downcast:0» (arg0 : derivedTypeDeclarationIR) : (_root_.Option headerUnionTypeDeclarationIR) := match arg0 with | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (headerUnionTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_typedefIR:case_1:downcast:0» (arg0 : typedefIR) : (_root_.Option typeIR) := match arg0 with | .VOID => some (typeIR.VOID) | .BOOL => some (typeIR.BOOL) | .ERROR => some (typeIR.ERROR) | .MATCH_KIND => some (typeIR.MATCH_KIND) | .STRING => some (typeIR.STRING) | .INT => some (typeIR.INT) | .«INT `< % `>» field0 => some (typeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (typeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (typeIR.«VARBIT `< % `>» field0) | ._NAME field0 => some (typeIR._NAME field0) | .TYPEDEF field0 field1 => some (typeIR.TYPEDEF field0 field1) | .TYPE field0 field1 => some (typeIR.TYPE field0 field1) | .«LIST `< % `>» field0 => some (typeIR.«LIST `< % `>» field0) | .«TUPLE `< % `>» field0 => some (typeIR.«TUPLE `< % `>» field0) | .«ARRAY % `[ % `]» field0 field1 => some (typeIR.«ARRAY % `[ % `]» field0 field1) | .«HEADER_STACK % `[ % `]» field0 field1 => some (typeIR.«HEADER_STACK % `[ % `]» field0 field1) | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | .«ENUM % `{ % `}» field0 field1 => some (typeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | .«EXTERN % `< % `> %» field0 field1 field2 => some (typeIR.«EXTERN % `< % `> %» field0 field1 field2) | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (typeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (typeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | .«TABLE % `{ % `}» field0 field1 => some (typeIR.«TABLE % `{ % `}» field0 field1) | .DEFAULT => some (typeIR.DEFAULT) | .HEADER_INVALID => some (typeIR.HEADER_INVALID) | .«SEQ `< % `>» field0 => some (typeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (typeIR.«SEQ `< % ',' '...' `>» field0) | .«RECORD `{ % `}» field0 => some (typeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (typeIR.«RECORD `{ % ',' '...' `}» field0) | .«SET `< % `>» field0 => some (typeIR.«SET `< % `>» field0) | .«TABLE_ENUM % `{ % `}» field0 field1 => some (typeIR.«TABLE_ENUM % `{ % `}» field0 field1) | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (typeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none


def «$lift_typedefIR:case_2:downcast:0» (arg0 : typedefIR) : (_root_.Option derivedTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (derivedTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_typedefDeclarationIR:case_1:downcast:0» (arg0 : typedefIR) : (_root_.Option typeIR) := match arg0 with | .VOID => some (typeIR.VOID) | .BOOL => some (typeIR.BOOL) | .ERROR => some (typeIR.ERROR) | .MATCH_KIND => some (typeIR.MATCH_KIND) | .STRING => some (typeIR.STRING) | .INT => some (typeIR.INT) | .«INT `< % `>» field0 => some (typeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (typeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (typeIR.«VARBIT `< % `>» field0) | ._NAME field0 => some (typeIR._NAME field0) | .TYPEDEF field0 field1 => some (typeIR.TYPEDEF field0 field1) | .TYPE field0 field1 => some (typeIR.TYPE field0 field1) | .«LIST `< % `>» field0 => some (typeIR.«LIST `< % `>» field0) | .«TUPLE `< % `>» field0 => some (typeIR.«TUPLE `< % `>» field0) | .«ARRAY % `[ % `]» field0 field1 => some (typeIR.«ARRAY % `[ % `]» field0 field1) | .«HEADER_STACK % `[ % `]» field0 field1 => some (typeIR.«HEADER_STACK % `[ % `]» field0 field1) | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | .«ENUM % `{ % `}» field0 field1 => some (typeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | .«EXTERN % `< % `> %» field0 field1 field2 => some (typeIR.«EXTERN % `< % `> %» field0 field1 field2) | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (typeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (typeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | .«TABLE % `{ % `}» field0 field1 => some (typeIR.«TABLE % `{ % `}» field0 field1) | .DEFAULT => some (typeIR.DEFAULT) | .HEADER_INVALID => some (typeIR.HEADER_INVALID) | .«SEQ `< % `>» field0 => some (typeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (typeIR.«SEQ `< % ',' '...' `>» field0) | .«RECORD `{ % `}» field0 => some (typeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (typeIR.«RECORD `{ % ',' '...' `}» field0) | .«SET `< % `>» field0 => some (typeIR.«SET `< % `>» field0) | .«TABLE_ENUM % `{ % `}» field0 field1 => some (typeIR.«TABLE_ENUM % `{ % `}» field0 field1) | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (typeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none


def «$lift_typedefDeclarationIR:case_2:downcast:0» (arg0 : typedefIR) : (_root_.Option derivedTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (derivedTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$lift_externDeclarationIR:case_1:downcast:0» (arg0 : externDeclarationIR) : (_root_.Option externFunctionDeclarationIR) := match arg0 with | .«% EXTERN % ';'» field0 field1 => some (externFunctionDeclarationIR.«% EXTERN % ';'» field0 field1) | _ => none


def «$lift_externDeclarationIR:case_2:downcast:0» (arg0 : externDeclarationIR) : (_root_.Option externObjectDeclarationIR) := match arg0 with | .«% EXTERN % `< % ',' `> `{ % % `}» field0 field1 field2 field3 field4 => some (externObjectDeclarationIR.«% EXTERN % `< % ',' `> `{ % % `}» field0 field1 field2 field3 field4) | _ => none


def «$lift_stateExpressionIR:case_2:downcast:0» (arg0 : stateExpressionIR) : (_root_.Option selectExpressionIR) := match arg0 with | .«SELECT `( % `) `{ % `}» field0 field1 => some (selectExpressionIR.«SELECT `( % `) `{ % `}» field0 field1) | _ => none


def «$lift_typeIR_as_valueSetType:case_1:downcast:1» (arg0 : type) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «$lift_typeIR_as_valueSetType:case_2:downcast:1» (arg0 : type) : (_root_.Option tupleType) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleType.«TUPLE `< % `>» field0) | _ => none

end SpecTec
