import SpecTecDecl0068

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$compat_range:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_range:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_range:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_range:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_range:matches:5:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «SwitchLabel_table_ok:expressionNonBrace-prefixedNonTypeName:downcast:0» (arg0 : switchLabel) : (_root_.Option prefixedNonTypeName) := match arg0 with | ._ID field0 => some (prefixedNonTypeName._ID field0) | .APPLY => some (prefixedNonTypeName.APPLY) | .KEY => some (prefixedNonTypeName.KEY) | .ACTIONS => some (prefixedNonTypeName.ACTIONS) | .STATE => some (prefixedNonTypeName.STATE) | .ENTRIES => some (prefixedNonTypeName.ENTRIES) | .TYPE => some (prefixedNonTypeName.TYPE) | .PRIORITY => some (prefixedNonTypeName.PRIORITY) | .«_ID '.' %» field0 => some (prefixedNonTypeName.«_ID '.' %» field0) | _ => none


def «SwitchLabel_general_ok:expressionNonBrace:downcast:0» (arg0 : switchLabel) : (_root_.Option expressionNonBrace) := match arg0 with | .TRUE => some (expressionNonBrace.TRUE) | .FALSE => some (expressionNonBrace.FALSE) | .D field0 => some (expressionNonBrace.D field0) | .«% W %» field0 field1 => some (expressionNonBrace.«% W %» field0 field1) | .«% S %» field0 field1 => some (expressionNonBrace.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expressionNonBrace.«'"' % '"'» field0) | ._ID field0 => some (expressionNonBrace._ID field0) | .APPLY => some (expressionNonBrace.APPLY) | .KEY => some (expressionNonBrace.KEY) | .ACTIONS => some (expressionNonBrace.ACTIONS) | .STATE => some (expressionNonBrace.STATE) | .ENTRIES => some (expressionNonBrace.ENTRIES) | .TYPE => some (expressionNonBrace.TYPE) | .PRIORITY => some (expressionNonBrace.PRIORITY) | .«_ID '.' %» field0 => some (expressionNonBrace.«_ID '.' %» field0) | .THIS => some (expressionNonBrace.THIS) | .«% %» field0 field1 => some (expressionNonBrace.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expressionNonBrace.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expressionNonBrace.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expressionNonBrace.«`( % `) %» field0 field1) | .«ERROR '.' %» field0 => some (expressionNonBrace.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expressionNonBrace.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expressionNonBrace.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expressionNonBrace.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expressionNonBrace.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expressionNonBrace.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expressionNonBrace.«`( % `)» field0) | _ => none


def «$compat_switch:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.ERROR => 0
  | _ => 1


def «$compat_switch:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$compat_switch:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$compat_switch:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$compat_switch:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$compat_switch:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «ObjectDecl_ok:instantiation:downcast:0» (arg0 : objectDeclaration) : (_root_.Option instantiation) := match arg0 with | .«% % `( % `) % ';'» field0 field1 field2 field3 => some (instantiation.«% % `( % `) % ';'» field0 field1 field2 field3) | .«% % `( % `) % % ';'» field0 field1 field2 field3 field4 => some (instantiation.«% % `( % `) % % ';'» field0 field1 field2 field3 field4) | _ => none


def «ObjectDecl_ok:functionDeclaration:downcast:0» (arg0 : objectDeclaration) : (_root_.Option functionDeclaration) := match arg0 with | .«% % %» field0 field1 field2 => some (functionDeclaration.«% % %» field0 field1 field2) | _ => none


def «InstDecl_objectInitializer_ok:rule:downcast:4» (arg0 : typeIR) : (_root_.Option externObjectTypeIR) := match arg0 with | .«EXTERN % `< % `> %» field0 field1 field2 => some (externObjectTypeIR.«EXTERN % `< % `> %» field0 field1 field2) | _ => none


def «$split_externConstructorOrMethodPrototypeList:case_1:downcast:5:0» (arg0 : externConstructorOrMethodPrototype) : (_root_.Option externConstructorPrototype) := match arg0 with | .«% % `( % `) ';'» field0 field1 field2 => some (externConstructorPrototype.«% % `( % `) ';'» field0 field1 field2) | _ => none


def «$split_externConstructorOrMethodPrototypeList:case_1:downcast:10:0» (arg0 : externConstructorOrMethodPrototype) : (_root_.Option externMethodPrototype) := match arg0 with | .«% % ';'» field0 field1 => some (externMethodPrototype.«% % ';'» field0 field1) | .«% ABSTRACT % ';'» field0 field1 => some (externMethodPrototype.«% ABSTRACT % ';'» field0 field1) | _ => none


def «SelectCase_keyset_simple_ok:set-alpha:downcast:0» (arg0 : simpleKeysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «SelectCase_keyset_simple_ok:set-alpha:downcast:3» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «SelectCase_keyset_simple_ok:set-subtype:downcast:0» (arg0 : simpleKeysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «SelectCase_keyset_simple_ok:set-subtype:downcast:3» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «SelectCase_keyset_simple_ok:non-set:downcast:0» (arg0 : simpleKeysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «$compat_mask:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.INT, typeIR.INT => 0
  | _, _ => 1


def «$compat_mask:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_mask:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_mask:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_mask:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_mask:matches:5:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «SelectCase_keyset_ok:expression:downcast:0» (arg0 : keysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «SelectCase_keyset_ok:expression-list:downcast:0» (arg0 : keysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «SelectCase_keyset_ok:mask:downcast:0» (arg0 : keysetExpression) : (_root_.Option simpleKeysetExpression) := match arg0 with | .TRUE => some (simpleKeysetExpression.TRUE) | .FALSE => some (simpleKeysetExpression.FALSE) | .D field0 => some (simpleKeysetExpression.D field0) | .«% W %» field0 field1 => some (simpleKeysetExpression.«% W %» field0 field1) | .«% S %» field0 field1 => some (simpleKeysetExpression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (simpleKeysetExpression.«'"' % '"'» field0) | ._ID field0 => some (simpleKeysetExpression._ID field0) | .APPLY => some (simpleKeysetExpression.APPLY) | .KEY => some (simpleKeysetExpression.KEY) | .ACTIONS => some (simpleKeysetExpression.ACTIONS) | .STATE => some (simpleKeysetExpression.STATE) | .ENTRIES => some (simpleKeysetExpression.ENTRIES) | .TYPE => some (simpleKeysetExpression.TYPE) | .PRIORITY => some (simpleKeysetExpression.PRIORITY) | .«_ID '.' %» field0 => some (simpleKeysetExpression.«_ID '.' %» field0) | .THIS => some (simpleKeysetExpression.THIS) | .«'...'» => some (simpleKeysetExpression.«'...'») | .«% %» field0 field1 => some (simpleKeysetExpression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (simpleKeysetExpression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (simpleKeysetExpression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (simpleKeysetExpression.«`( % `) %» field0 field1) | .«'{#}'» => some (simpleKeysetExpression.«'{#}'») | .«`{ % % `}» field0 field1 => some (simpleKeysetExpression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (simpleKeysetExpression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (simpleKeysetExpression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (simpleKeysetExpression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (simpleKeysetExpression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (simpleKeysetExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (simpleKeysetExpression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (simpleKeysetExpression.«`( % `)» field0) | .«% '&&&' %» field0 field1 => some (simpleKeysetExpression.«% '&&&' %» field0 field1) | .«% '..' %» field0 field1 => some (simpleKeysetExpression.«% '..' %» field0 field1) | .DEFAULT => some (simpleKeysetExpression.DEFAULT) | .«'_'» => some (simpleKeysetExpression.«'_'») | _ => none

end SpecTec
