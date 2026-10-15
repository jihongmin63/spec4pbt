import SpecTecDecl0075

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Stmt_inst:assignmentStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «Stmt_inst:callStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «Stmt_inst:directApplicationStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option directApplicationStatementIR) := match arg0 with | .«% '.' APPLY `( % `) ';'» field0 field1 => some (directApplicationStatementIR.«% '.' APPLY `( % `) ';'» field0 field1) | _ => none


def «Stmt_inst:returnStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option returnStatementIR) := match arg0 with | .«RETURN ';'» => some (returnStatementIR.«RETURN ';'») | .«RETURN % ';'» field0 => some (returnStatementIR.«RETURN % ';'» field0) | _ => none


def «Stmt_inst:exitStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option exitStatement) := match arg0 with | .«EXIT ';'» => some (exitStatement.«EXIT ';'») | _ => none


def «Stmt_inst:blockStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option blockStatementIR) := match arg0 with | .«% `{ % `}» field0 field1 => some (blockStatementIR.«% `{ % `}» field0 field1) | _ => none


def «Stmt_inst:non-else:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_inst:else:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_inst:forStatementIR-three-clause:downcast:0» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_inst:no-annotations:downcast:0» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_inst:annotations:downcast:0» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_inst:breakStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option breakStatement) := match arg0 with | .«BREAK ';'» => some (breakStatement.«BREAK ';'») | _ => none


def «Stmt_inst:continueStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option continueStatement) := match arg0 with | .«CONTINUE ';'» => some (continueStatement.«CONTINUE ';'») | _ => none


def «Stmt_inst:switchStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option switchStatementIR) := match arg0 with | .«SWITCH `( % `) `{ % `}» field0 field1 => some (switchStatementIR.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «BlockElementStmt_inst:constantDeclarationIR:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «BlockElementStmt_inst:variableDeclarationIR:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «BlockElementStmt_inst:statementIR:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option statementIR) := match arg0 with | .«';'» => some (statementIR.«';'») | .«% % % ';'» field0 field1 field2 => some (statementIR.«% % % ';'» field0 field1 field2) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (statementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | .«% '.' APPLY `( % `) ';'» field0 field1 => some (statementIR.«% '.' APPLY `( % `) ';'» field0 field1) | .«RETURN ';'» => some (statementIR.«RETURN ';'») | .«RETURN % ';'» field0 => some (statementIR.«RETURN % ';'» field0) | .«EXIT ';'» => some (statementIR.«EXIT ';'») | .«% `{ % `}» field0 field1 => some (statementIR.«% `{ % `}» field0 field1) | .«IF `( % `) %» field0 field1 => some (statementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (statementIR.«IF `( % `) % ELSE %» field0 field1 field2) | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (statementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (statementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (statementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | .«BREAK ';'» => some (statementIR.«BREAK ';'») | .«CONTINUE ';'» => some (statementIR.«CONTINUE ';'») | .«SWITCH `( % `) `{ % `}» field0 field1 => some (statementIR.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «ParserStmt_inst:emptyStatementIR:downcast:0» (arg0 : parserStatementIR) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «ParserStmt_inst:emptyStatementIR:downcast:1» (arg0 : statementIR) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «ParserStmt_inst:assignmentStatementIR:downcast:0» (arg0 : parserStatementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «ParserStmt_inst:assignmentStatementIR:downcast:1» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «ParserStmt_inst:callStatementIR:downcast:0» (arg0 : parserStatementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «ParserStmt_inst:callStatementIR:downcast:1» (arg0 : statementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «ParserStmt_inst:directApplicationStatementIR:downcast:0» (arg0 : parserStatementIR) : (_root_.Option directApplicationStatementIR) := match arg0 with | .«% '.' APPLY `( % `) ';'» field0 field1 => some (directApplicationStatementIR.«% '.' APPLY `( % `) ';'» field0 field1) | _ => none


def «ParserStmt_inst:parserBlockStatementIR:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserBlockStatementIR) := match arg0 with | .«% `{ % `}» field0 field1 => some (parserBlockStatementIR.«% `{ % `}» field0 field1) | _ => none


def «ParserStmt_inst:non-else:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserStmt_inst:else:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserBlockElementStmt_inst:constantDeclarationIR:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserBlockElementStmt_inst:variableDeclarationIR:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserBlockElementStmt_inst:parserStatementIR:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option parserStatementIR) := match arg0 with | .«';'» => some (parserStatementIR.«';'») | .«% % % ';'» field0 field1 field2 => some (parserStatementIR.«% % % ';'» field0 field1 field2) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (parserStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | .«% '.' APPLY `( % `) ';'» field0 field1 => some (parserStatementIR.«% '.' APPLY `( % `) ';'» field0 field1) | .«% `{ % `}» field0 field1 => some (parserStatementIR.«% `{ % `}» field0 field1) | .«IF `( % `) %» field0 field1 => some (parserStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserLocalDecl_inst:constantDeclarationIR:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserLocalDecl_inst:instantiationIR:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option instantiationIR) := match arg0 with | .«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5 => some (instantiationIR.«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5) | _ => none

end SpecTec
