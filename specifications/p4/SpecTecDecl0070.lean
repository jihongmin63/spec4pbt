import SpecTecDecl0069

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «SelectCase_keyset_ok:range:downcast:0» (arg0 : keysetExpression) : (_root_.Option simpleKeysetExpression) := match arg0 with | .TRUE => some (simpleKeysetExpression.TRUE) | .FALSE => some (simpleKeysetExpression.FALSE) | .D field0 => some (simpleKeysetExpression.D field0) | .«% W %» field0 field1 => some (simpleKeysetExpression.«% W %» field0 field1) | .«% S %» field0 field1 => some (simpleKeysetExpression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (simpleKeysetExpression.«'"' % '"'» field0) | ._ID field0 => some (simpleKeysetExpression._ID field0) | .APPLY => some (simpleKeysetExpression.APPLY) | .KEY => some (simpleKeysetExpression.KEY) | .ACTIONS => some (simpleKeysetExpression.ACTIONS) | .STATE => some (simpleKeysetExpression.STATE) | .ENTRIES => some (simpleKeysetExpression.ENTRIES) | .TYPE => some (simpleKeysetExpression.TYPE) | .PRIORITY => some (simpleKeysetExpression.PRIORITY) | .«_ID '.' %» field0 => some (simpleKeysetExpression.«_ID '.' %» field0) | .THIS => some (simpleKeysetExpression.THIS) | .«'...'» => some (simpleKeysetExpression.«'...'») | .«% %» field0 field1 => some (simpleKeysetExpression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (simpleKeysetExpression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (simpleKeysetExpression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (simpleKeysetExpression.«`( % `) %» field0 field1) | .«'{#}'» => some (simpleKeysetExpression.«'{#}'») | .«`{ % % `}» field0 field1 => some (simpleKeysetExpression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (simpleKeysetExpression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (simpleKeysetExpression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (simpleKeysetExpression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (simpleKeysetExpression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (simpleKeysetExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (simpleKeysetExpression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (simpleKeysetExpression.«`( % `)» field0) | .«% '&&&' %» field0 field1 => some (simpleKeysetExpression.«% '&&&' %» field0 field1) | .«% '..' %» field0 field1 => some (simpleKeysetExpression.«% '..' %» field0 field1) | .DEFAULT => some (simpleKeysetExpression.DEFAULT) | .«'_'» => some (simpleKeysetExpression.«'_'») | _ => none


def «SelectCase_keyset_ok:mask_2:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «SelectCase_keyset_ok:range_2:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «SelectCase_keyset_ok:default-one-to-one_2:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «SelectCase_keyset_ok:default-many-to-one_2:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «SelectCase_keyset_ok:dontcare-one-to-one_2:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «SelectCase_keyset_ok:dontcare-many-to-one_2:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «SelectCase_keyset_ok:list:downcast:0» (arg0 : keysetExpression) : (_root_.Option tupleKeysetExpression) := match arg0 with | .«`( % '&&&' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '&&&' % `)» field0 field1) | .«`( % '..' % `)» field0 field1 => some (tupleKeysetExpression.«`( % '..' % `)» field0 field1) | .«`( DEFAULT `)» => some (tupleKeysetExpression.«`( DEFAULT `)») | .«`( '_' `)» => some (tupleKeysetExpression.«`( '_' `)») | .«`( % ',' % `)» field0 field1 => some (tupleKeysetExpression.«`( % ',' % `)» field0 field1) | _ => none


def «$compat_table_exact_optional_key:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$compat_table_exact_optional_key:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.ERROR => 0
  | _ => 1


def «$compat_table_exact_optional_key:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | typeIR.«INT `< % `>» _ => 0
  | typeIR.«BIT `< % `>» _ => 0
  | typeIR.«VARBIT `< % `>» _ => 0
  | _ => 1


def «$compat_table_exact_optional_key:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$compat_table_exact_optional_key:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$compat_table_exact_optional_key:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | _ => 1


def «$compat_table_exact_optional_key:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$compat_table_exact_optional_key:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$compat_table_lpm_ternary_range_key:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$compat_table_lpm_ternary_range_key:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | _ => 1


def «$compat_table_lpm_ternary_range_key:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$compat_table_lpm_ternary_range_key:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$compat_table_lpm_ternary_range_key:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$compat_table_lpm_ternary_range_key:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$compat_table_lpm_ternary_range_key:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$compat_table_lpm_ternary_range_key:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «TableEntry_keyset_simple_ok:lpm:downcast:0» (arg0 : simpleKeysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «TableEntry_keyset_simple_ok:non-lpm-singleton-seq:downcast:0» (arg0 : simpleKeysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «TableEntry_keyset_simple_ok:non-lpm-singleton-seq:downcast:2» (arg0 : expression) : (_root_.Option sequenceOrRecordExpression) := match arg0 with | .«`{ % % `}» field0 field1 => some (sequenceOrRecordExpression.«`{ % % `}» field0 field1) | _ => none


def «TableEntry_keyset_simple_ok:non-lpm-singleton-seq:downcast:3» (arg0 : sequenceOrRecordElementExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «TableEntry_keyset_simple_ok:non-lpm-non-singleton-seq:downcast:0» (arg0 : simpleKeysetExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «TableEntry_keyset_simple_ok:lpm_2:downcast:4» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$is_singleton_list_expression:case_1:downcast:0» (arg0 : expression) : (_root_.Option sequenceOrRecordExpression) := match arg0 with | .«`{ % % `}» field0 field1 => some (sequenceOrRecordExpression.«`{ % % `}» field0 field1) | _ => none


def «$is_singleton_list_expression:case_1:downcast:1» (arg0 : sequenceOrRecordElementExpression) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none

end SpecTec
