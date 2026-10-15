import SpecTecDecl0060

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Stmt_ok:callStatement-typeArgumentList:downcast:0» (arg0 : statement) : (_root_.Option callStatement) := match arg0 with | .«% `( % `) ';'» field0 field1 => some (callStatement.«% `( % `) ';'» field0 field1) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatement.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «Stmt_ok:directApplicationStatement:downcast:0» (arg0 : statement) : (_root_.Option directApplicationStatement) := match arg0 with | .«% '.' APPLY `( % `) ';'» field0 field1 => some (directApplicationStatement.«% '.' APPLY `( % `) ';'» field0 field1) | _ => none


def «Stmt_ok:directApplicationStatement:downcast:1» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Stmt_ok:directApplicationStatement:downcast:4» (arg0 : statementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «Stmt_ok:non-expression:downcast:0» (arg0 : statement) : (_root_.Option returnStatement) := match arg0 with | .«RETURN ';'» => some (returnStatement.«RETURN ';'») | .«RETURN % ';'» field0 => some (returnStatement.«RETURN % ';'» field0) | _ => none


def «Stmt_ok:expression:downcast:0» (arg0 : statement) : (_root_.Option returnStatement) := match arg0 with | .«RETURN ';'» => some (returnStatement.«RETURN ';'») | .«RETURN % ';'» field0 => some (returnStatement.«RETURN % ';'» field0) | _ => none


def «Stmt_ok:exitStatement:downcast:0» (arg0 : statement) : (_root_.Option exitStatement) := match arg0 with | .«EXIT ';'» => some (exitStatement.«EXIT ';'») | _ => none


def «Stmt_ok:blockStatement:downcast:0» (arg0 : statement) : (_root_.Option blockStatement) := match arg0 with | .«% `{ % `}» field0 field1 => some (blockStatement.«% `{ % `}» field0 field1) | _ => none


def «Stmt_ok:non-else:downcast:0» (arg0 : statement) : (_root_.Option conditionalStatement) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatement.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatement.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_ok:else:downcast:0» (arg0 : statement) : (_root_.Option conditionalStatement) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatement.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatement.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_ok:forStatement-three-clause:downcast:0» (arg0 : statement) : (_root_.Option forStatement) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatement.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatement.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatement.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_ok:no-annotations:downcast:0» (arg0 : statement) : (_root_.Option forStatement) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatement.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatement.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatement.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_ok:annotations:downcast:0» (arg0 : statement) : (_root_.Option forStatement) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatement.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatement.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatement.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_ok:annotations:downcast:1» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_ok:breakStatement:downcast:0» (arg0 : statement) : (_root_.Option breakStatement) := match arg0 with | .«BREAK ';'» => some (breakStatement.«BREAK ';'») | _ => none


def «Stmt_ok:continueStatement:downcast:0» (arg0 : statement) : (_root_.Option continueStatement) := match arg0 with | .«CONTINUE ';'» => some (continueStatement.«CONTINUE ';'») | _ => none


def «Stmt_ok:table:downcast:0» (arg0 : statement) : (_root_.Option switchStatement) := match arg0 with | .«SWITCH `( % `) `{ % `}» field0 field1 => some (switchStatement.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «Stmt_ok:table:downcast:3» (arg0 : typeIR) : (_root_.Option tableMetadataEnumTypeIR) := match arg0 with | .«TABLE_ENUM % `{ % `}» field0 field1 => some (tableMetadataEnumTypeIR.«TABLE_ENUM % `{ % `}» field0 field1) | _ => none


def «Stmt_ok:general:downcast:0» (arg0 : statement) : (_root_.Option switchStatement) := match arg0 with | .«SWITCH `( % `) `{ % `}» field0 field1 => some (switchStatement.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «BlockElementStmt_ok:constantDeclaration:downcast:0» (arg0 : blockElementStatement) : (_root_.Option constantDeclaration) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclaration.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «BlockElementStmt_ok:variableDeclaration:downcast:0» (arg0 : blockElementStatement) : (_root_.Option variableDeclaration) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclaration.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «BlockElementStmt_ok:statement:downcast:0» (arg0 : blockElementStatement) : (_root_.Option statement) := match arg0 with | .«';'» => some (statement.«';'») | .«% % % ';'» field0 field1 field2 => some (statement.«% % % ';'» field0 field1 field2) | .«% `( % `) ';'» field0 field1 => some (statement.«% `( % `) ';'» field0 field1) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (statement.«% `< % `> `( % `) ';'» field0 field1 field2) | .«% '.' APPLY `( % `) ';'» field0 field1 => some (statement.«% '.' APPLY `( % `) ';'» field0 field1) | .«RETURN ';'» => some (statement.«RETURN ';'») | .«RETURN % ';'» field0 => some (statement.«RETURN % ';'» field0) | .«EXIT ';'» => some (statement.«EXIT ';'») | .«% `{ % `}» field0 field1 => some (statement.«% `{ % `}» field0 field1) | .«IF `( % `) %» field0 field1 => some (statement.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (statement.«IF `( % `) % ELSE %» field0 field1 field2) | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (statement.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (statement.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (statement.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | .«BREAK ';'» => some (statement.«BREAK ';'») | .«CONTINUE ';'» => some (statement.«CONTINUE ';'») | .«SWITCH `( % `) `{ % `}» field0 field1 => some (statement.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «Parameter_ok:initializer-ctk:downcast:0» (arg0 : initializerOpt) : (_root_.Option initializer) := match arg0 with | .«'=' %» field0 => some (initializer.«'=' %» field0) | _ => none


def «Parameter_ok:initializer-lctk:downcast:0» (arg0 : initializerOpt) : (_root_.Option initializer) := match arg0 with | .«'=' %» field0 => some (initializer.«'=' %» field0) | _ => none


def «ExternConstructor_ok:rule:downcast:2» (arg0 : typeDefIR) : (_root_.Option externObjectTypeDefIR) := match arg0 with | .«EXTERN % `< % ',' % `> %» field0 field1 field2 field3 => some (externObjectTypeDefIR.«EXTERN % `< % ',' % `> %» field0 field1 field2 field3) | _ => none


def «ParserTransition_ok:select:downcast:0» (arg0 : stateExpression) : (_root_.Option selectExpression) := match arg0 with | .«SELECT `( % `) `{ % `}» field0 field1 => some (selectExpression.«SELECT `( % `) `{ % `}» field0 field1) | _ => none


def «ParserStmt_ok:emptyStatement:downcast:0» (arg0 : parserStatement) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «ParserStmt_ok:emptyStatement:downcast:1» (arg0 : statementIR) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «ParserStmt_ok:assignmentStatement:downcast:0» (arg0 : parserStatement) : (_root_.Option assignmentStatement) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatement.«% % % ';'» field0 field1 field2) | _ => none


def «ParserStmt_ok:assignmentStatement:downcast:1» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «ParserStmt_ok:callStatement:downcast:0» (arg0 : parserStatement) : (_root_.Option callStatement) := match arg0 with | .«% `( % `) ';'» field0 field1 => some (callStatement.«% `( % `) ';'» field0 field1) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatement.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «ParserStmt_ok:callStatement:downcast:1» (arg0 : statementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none

end SpecTec
