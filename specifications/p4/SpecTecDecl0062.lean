import SpecTecDecl0061

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «ParserStmt_ok:directApplicationStatement:downcast:0» (arg0 : parserStatement) : (_root_.Option directApplicationStatement) := match arg0 with | .«% '.' APPLY `( % `) ';'» field0 field1 => some (directApplicationStatement.«% '.' APPLY `( % `) ';'» field0 field1) | _ => none


def «ParserStmt_ok:directApplicationStatement:downcast:1» (arg0 : statementIR) : (_root_.Option directApplicationStatementIR) := match arg0 with | .«% '.' APPLY `( % `) ';'» field0 field1 => some (directApplicationStatementIR.«% '.' APPLY `( % `) ';'» field0 field1) | _ => none


def «ParserStmt_ok:parserBlockStatement:downcast:0» (arg0 : parserStatement) : (_root_.Option parserBlockStatement) := match arg0 with | .«% `{ % `}» field0 field1 => some (parserBlockStatement.«% `{ % `}» field0 field1) | _ => none


def «ParserStmt_ok:non-else:downcast:0» (arg0 : parserStatement) : (_root_.Option parserConditionalStatement) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatement.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatement.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserStmt_ok:else:downcast:0» (arg0 : parserStatement) : (_root_.Option parserConditionalStatement) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatement.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatement.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserBlockElementStmt_ok:constantDeclaration:downcast:0» (arg0 : parserBlockElementStatement) : (_root_.Option constantDeclaration) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclaration.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserBlockElementStmt_ok:variableDeclaration:downcast:0» (arg0 : parserBlockElementStatement) : (_root_.Option variableDeclaration) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclaration.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserBlockElementStmt_ok:parserStatement:downcast:0» (arg0 : parserBlockElementStatement) : (_root_.Option parserStatement) := match arg0 with | .«';'» => some (parserStatement.«';'») | .«% % % ';'» field0 field1 field2 => some (parserStatement.«% % % ';'» field0 field1 field2) | .«% `( % `) ';'» field0 field1 => some (parserStatement.«% `( % `) ';'» field0 field1) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (parserStatement.«% `< % `> `( % `) ';'» field0 field1 field2) | .«% '.' APPLY `( % `) ';'» field0 field1 => some (parserStatement.«% '.' APPLY `( % `) ';'» field0 field1) | .«% `{ % `}» field0 field1 => some (parserStatement.«% `{ % `}» field0 field1) | .«IF `( % `) %» field0 field1 => some (parserStatement.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserStatement.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserLocalDecl_ok:constantDeclaration:downcast:0» (arg0 : parserLocalDeclaration) : (_root_.Option constantDeclaration) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclaration.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserLocalDecl_ok:instantiation:downcast:0» (arg0 : parserLocalDeclaration) : (_root_.Option instantiation) := match arg0 with | .«% % `( % `) % ';'» field0 field1 field2 field3 => some (instantiation.«% % `( % `) % ';'» field0 field1 field2 field3) | .«% % `( % `) % % ';'» field0 field1 field2 field3 field4 => some (instantiation.«% % `( % `) % % ';'» field0 field1 field2 field3 field4) | _ => none


def «ParserLocalDecl_ok:variableDeclaration:downcast:0» (arg0 : parserLocalDeclaration) : (_root_.Option variableDeclaration) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclaration.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserLocalDecl_ok:valueSetDeclaration:downcast:0» (arg0 : parserLocalDeclaration) : (_root_.Option valueSetDeclaration) := match arg0 with | .«% VALUE_SET `< % `> `( % `) % ';'» field0 field1 field2 field3 => some (valueSetDeclaration.«% VALUE_SET `< % `> `( % `) % ';'» field0 field1 field2 field3) | _ => none


def «TableAction_ok:prefixedNonTypeName:downcast:0» (arg0 : tableActionReference) : (_root_.Option prefixedNonTypeName) := match arg0 with | ._ID field0 => some (prefixedNonTypeName._ID field0) | .APPLY => some (prefixedNonTypeName.APPLY) | .KEY => some (prefixedNonTypeName.KEY) | .ACTIONS => some (prefixedNonTypeName.ACTIONS) | .STATE => some (prefixedNonTypeName.STATE) | .ENTRIES => some (prefixedNonTypeName.ENTRIES) | .TYPE => some (prefixedNonTypeName.TYPE) | .PRIORITY => some (prefixedNonTypeName.PRIORITY) | .«_ID '.' %» field0 => some (prefixedNonTypeName.«_ID '.' %» field0) | _ => none


def «TableAction_ok:prefixedNonTypeName:downcast:3» (arg0 : callableTypeDefIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «TableAction_ok:prefixedNonTypeName-argumentList:downcast:2» (arg0 : callableTypeDefIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «TableDefaultAction_ok:prefixedNonTypeName:downcast:0» (arg0 : expression) : (_root_.Option prefixedNonTypeName) := match arg0 with | ._ID field0 => some (prefixedNonTypeName._ID field0) | .APPLY => some (prefixedNonTypeName.APPLY) | .KEY => some (prefixedNonTypeName.KEY) | .ACTIONS => some (prefixedNonTypeName.ACTIONS) | .STATE => some (prefixedNonTypeName.STATE) | .ENTRIES => some (prefixedNonTypeName.ENTRIES) | .TYPE => some (prefixedNonTypeName.TYPE) | .PRIORITY => some (prefixedNonTypeName.PRIORITY) | .«_ID '.' %» field0 => some (prefixedNonTypeName.«_ID '.' %» field0) | _ => none


def «TableDefaultAction_ok:prefixedNonTypeName-argumentList:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «TableDefaultAction_ok:prefixedNonTypeName-argumentList:downcast:1» (arg0 : callTarget) : (_root_.Option prefixedNonTypeName) := match arg0 with | ._ID field0 => some (prefixedNonTypeName._ID field0) | .APPLY => some (prefixedNonTypeName.APPLY) | .KEY => some (prefixedNonTypeName.KEY) | .ACTIONS => some (prefixedNonTypeName.ACTIONS) | .STATE => some (prefixedNonTypeName.STATE) | .ENTRIES => some (prefixedNonTypeName.ENTRIES) | .TYPE => some (prefixedNonTypeName.TYPE) | .PRIORITY => some (prefixedNonTypeName.PRIORITY) | .«_ID '.' %» field0 => some (prefixedNonTypeName.«_ID '.' %» field0) | _ => none


def «TableEntry_keyset_ok:expression:downcast:0» (arg0 : keysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «TableEntry_keyset_ok:simple:downcast:0» (arg0 : keysetExpression) : (_root_.Option simpleKeysetExpression) := match arg0 with | .TRUE => some (simpleKeysetExpression.TRUE) | .FALSE => some (simpleKeysetExpression.FALSE) | .D field0 => some (simpleKeysetExpression.D field0) | .«% W %» field0 field1 => some (simpleKeysetExpression.«% W %» field0 field1) | .«% S %» field0 field1 => some (simpleKeysetExpression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (simpleKeysetExpression.«'"' % '"'» field0) | ._ID field0 => some (simpleKeysetExpression._ID field0) | .APPLY => some (simpleKeysetExpression.APPLY) | .KEY => some (simpleKeysetExpression.KEY) | .ACTIONS => some (simpleKeysetExpression.ACTIONS) | .STATE => some (simpleKeysetExpression.STATE) | .ENTRIES => some (simpleKeysetExpression.ENTRIES) | .TYPE => some (simpleKeysetExpression.TYPE) | .PRIORITY => some (simpleKeysetExpression.PRIORITY) | .«_ID '.' %» field0 => some (simpleKeysetExpression.«_ID '.' %» field0) | .THIS => some (simpleKeysetExpression.THIS) | .«'...'» => some (simpleKeysetExpression.«'...'») | .«% %» field0 field1 => some (simpleKeysetExpression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (simpleKeysetExpression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (simpleKeysetExpression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (simpleKeysetExpression.«`( % `) %» field0 field1) | .«'{#}'» => some (simpleKeysetExpression.«'{#}'») | .«`{ % % `}» field0 field1 => some (simpleKeysetExpression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (simpleKeysetExpression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (simpleKeysetExpression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (simpleKeysetExpression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (simpleKeysetExpression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (simpleKeysetExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (simpleKeysetExpression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (simpleKeysetExpression.«`( % `)» field0) | .«% '&&&' %» field0 field1 => some (simpleKeysetExpression.«% '&&&' %» field0 field1) | .«% '..' %» field0 field1 => some (simpleKeysetExpression.«% '..' %» field0 field1) | .DEFAULT => some (simpleKeysetExpression.DEFAULT) | .«'_'» => some (simpleKeysetExpression.«'_'») | _ => none


def «TableEntry_keyset_ok:tuple:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «TableEntry_keyset_ok:simple_2:downcast:0» (arg0 : keysetExpression) : (_root_.Option simpleKeysetExpression) := match arg0 with | .TRUE => some (simpleKeysetExpression.TRUE) | .FALSE => some (simpleKeysetExpression.FALSE) | .D field0 => some (simpleKeysetExpression.D field0) | .«% W %» field0 field1 => some (simpleKeysetExpression.«% W %» field0 field1) | .«% S %» field0 field1 => some (simpleKeysetExpression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (simpleKeysetExpression.«'"' % '"'» field0) | ._ID field0 => some (simpleKeysetExpression._ID field0) | .APPLY => some (simpleKeysetExpression.APPLY) | .KEY => some (simpleKeysetExpression.KEY) | .ACTIONS => some (simpleKeysetExpression.ACTIONS) | .STATE => some (simpleKeysetExpression.STATE) | .ENTRIES => some (simpleKeysetExpression.ENTRIES) | .TYPE => some (simpleKeysetExpression.TYPE) | .PRIORITY => some (simpleKeysetExpression.PRIORITY) | .«_ID '.' %» field0 => some (simpleKeysetExpression.«_ID '.' %» field0) | .THIS => some (simpleKeysetExpression.THIS) | .«'...'» => some (simpleKeysetExpression.«'...'») | .«% %» field0 field1 => some (simpleKeysetExpression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (simpleKeysetExpression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (simpleKeysetExpression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (simpleKeysetExpression.«`( % `) %» field0 field1) | .«'{#}'» => some (simpleKeysetExpression.«'{#}'») | .«`{ % % `}» field0 field1 => some (simpleKeysetExpression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (simpleKeysetExpression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (simpleKeysetExpression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (simpleKeysetExpression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (simpleKeysetExpression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (simpleKeysetExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (simpleKeysetExpression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (simpleKeysetExpression.«`( % `)» field0) | .«% '&&&' %» field0 field1 => some (simpleKeysetExpression.«% '&&&' %» field0 field1) | .«% '..' %» field0 field1 => some (simpleKeysetExpression.«% '..' %» field0 field1) | .DEFAULT => some (simpleKeysetExpression.DEFAULT) | .«'_'» => some (simpleKeysetExpression.«'_'») | _ => none


def «TableEntry_keyset_ok:tuple_2:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «TableEntry_keyset_ok:tuple_3:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «TableEntry_action_ok:prefixedNonTypeName:downcast:0» (arg0 : tableActionReference) : (_root_.Option prefixedNonTypeName) := match arg0 with | ._ID field0 => some (prefixedNonTypeName._ID field0) | .APPLY => some (prefixedNonTypeName.APPLY) | .KEY => some (prefixedNonTypeName.KEY) | .ACTIONS => some (prefixedNonTypeName.ACTIONS) | .STATE => some (prefixedNonTypeName.STATE) | .ENTRIES => some (prefixedNonTypeName.ENTRIES) | .TYPE => some (prefixedNonTypeName.TYPE) | .PRIORITY => some (prefixedNonTypeName.PRIORITY) | .«_ID '.' %» field0 => some (prefixedNonTypeName.«_ID '.' %» field0) | _ => none


def «TableEntry_priority_ok:expression:downcast:1» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «TableProperty_ok:largest-priority-wins:downcast:4» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


def «TableProperty_ok:priority-delta:downcast:4» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «ControlLocalDecl_ok:constantDeclaration:downcast:0» (arg0 : controlLocalDeclaration) : (_root_.Option constantDeclaration) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclaration.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_ok:instantiation:downcast:0» (arg0 : controlLocalDeclaration) : (_root_.Option instantiation) := match arg0 with | .«% % `( % `) % ';'» field0 field1 field2 field3 => some (instantiation.«% % `( % `) % ';'» field0 field1 field2 field3) | .«% % `( % `) % % ';'» field0 field1 field2 field3 field4 => some (instantiation.«% % `( % `) % % ';'» field0 field1 field2 field3 field4) | _ => none


def «ControlLocalDecl_ok:variableDeclaration:downcast:0» (arg0 : controlLocalDeclaration) : (_root_.Option variableDeclaration) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclaration.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_ok:actionDeclaration:downcast:0» (arg0 : controlLocalDeclaration) : (_root_.Option actionDeclaration) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDeclaration.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none

end SpecTec
