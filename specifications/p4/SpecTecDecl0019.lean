import SpecTecDecl0018

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$bitacc_offset_replace_op:case_1:downcast:1» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bitacc_offset_replace_op:case_1:downcast:2» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bitacc_offset_replace_op:case_1:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bitacc_offset_replace_op:case_1:downcast:4» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bitacc_offset_replace_op:case_1:downcast:7» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bitacc_offset_replace_op:case_2:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bitacc_offset_replace_op:case_2:downcast:1» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bitacc_offset_replace_op:case_2:downcast:2» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bitacc_offset_replace_op:case_2:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bitacc_offset_replace_op:case_2:downcast:4» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bitacc_offset_replace_op:case_2:downcast:7» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


inductive prefixedNameIR : Type where
  | _BARE : nameIR → prefixedNameIR
  | «'.' %» : nameIR → prefixedNameIR
deriving _root_.DecidableEq


mutual

inductive fieldTypeIR : Type where
  | «% % % ';'» : annotationList → typeIR → nameIR → fieldTypeIR

inductive typeIR : Type where
  | VOID : typeIR
  | BOOL : typeIR
  | ERROR : typeIR
  | MATCH_KIND : typeIR
  | STRING : typeIR
  | INT : typeIR
  | «INT `< % `>» : _root_.Nat → typeIR
  | «BIT `< % `>» : _root_.Nat → typeIR
  | «VARBIT `< % `>» : _root_.Nat → typeIR
  | _NAME : typeId → typeIR
  | TYPEDEF : typeId → typeIR → typeIR
  | TYPE : typeId → typeIR → typeIR
  | «LIST `< % `>» : typeIR → typeIR
  | «TUPLE `< % `>» : (_root_.List typeIR) → typeIR
  | «ARRAY % `[ % `]» : typeIR → _root_.Nat → typeIR
  | «HEADER_STACK % `[ % `]» : typeIR → _root_.Nat → typeIR
  | «STRUCT % `< % `> `{ % `}» : typeId → (_root_.List typeIR) → (_root_.List fieldTypeIR) → typeIR
  | «HEADER % `< % `> `{ % `}» : typeId → (_root_.List typeIR) → (_root_.List fieldTypeIR) → typeIR
  | «HEADER_UNION % `< % `> `{ % `}» : typeId → (_root_.List typeIR) → (_root_.List fieldTypeIR) → typeIR
  | «ENUM % `{ % `}» : typeId → (_root_.List nameIR) → typeIR
  | «ENUM % `< % `> `{ % `}» : typeId → typeIR → (_root_.List valueFieldIR) → typeIR
  | «EXTERN % `< % `> %» : typeId → (_root_.List typeIR) → (set (pair callableId externMethodTypeDefIR)) → typeIR
  | «PARSER % `< % `> `( % `)» : typeId → (_root_.List typeIR) → (_root_.List parameterIR) → typeIR
  | «CONTROL % `< % `> `( % `)» : typeId → (_root_.List typeIR) → (_root_.List parameterIR) → typeIR
  | «PACKAGE % `< % `> `{ % `}» : typeId → (_root_.List typeIR) → (_root_.List typeIR) → typeIR
  | «TABLE % `{ % `}» : typeId → tableMetadataStructTypeIR → typeIR
  | DEFAULT : typeIR
  | HEADER_INVALID : typeIR
  | «SEQ `< % `>» : (_root_.List typeIR) → typeIR
  | «SEQ `< % ',' '...' `>» : (_root_.List typeIR) → typeIR
  | «RECORD `{ % `}» : (_root_.List fieldTypeIR) → typeIR
  | «RECORD `{ % ',' '...' `}» : (_root_.List fieldTypeIR) → typeIR
  | «SET `< % `>» : typeIR → typeIR
  | «TABLE_ENUM % `{ % `}» : typeId → (_root_.List nameIR) → typeIR
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolTypeIR → boolTypeIR → tableMetadataEnumTypeIR → typeIR

inductive parameterInitializerIR : Type where
  | «'=' %» : typedExpressionIR → parameterInitializerIR
  | «'=' _VALUE %» : value → parameterInitializerIR

inductive parameterIR : Type where
  | «% % % % %» : annotationList → direction → typeIR → id → (_root_.Option parameterInitializerIR) → parameterIR

inductive externMethodTypeDefIR : Type where
  | «EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → externMethodTypeDefIR
  | «EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» : nameIR → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeIR → externMethodTypeDefIR

inductive namedExpressionIR : Type where
  | «% '=' %» : nameIR → typedExpressionIR → namedExpressionIR

inductive callableTargetIR : Type where
  | _BARE : nameIR → callableTargetIR
  | «'.' %» : nameIR → callableTargetIR
  | «% '.' %» : typedExpressionIR → nameIR → callableTargetIR
  | «TYPE % '.' %» : prefixedNameIR → nameIR → callableTargetIR
  | «`( % `)» : callableTargetIR → callableTargetIR

inductive constructorTargetIR : Type where
  | «% `< % `>» : prefixedNameIR → (_root_.List typeIR) → constructorTargetIR

inductive expressionIR : Type where
  | TRUE : expressionIR
  | FALSE : expressionIR
  | D : _root_.Int → expressionIR
  | «% W %» : _root_.Nat → _root_.Int → expressionIR
  | «% S %» : _root_.Nat → _root_.Int → expressionIR
  | «'"' % '"'» : _root_.String → expressionIR
  | _BARE : nameIR → expressionIR
  | «'.' %» : nameIR → expressionIR
  | «'...'» : expressionIR
  | «% %» : unop → typedExpressionIR → expressionIR
  | «% % %» : typedExpressionIR → binop → typedExpressionIR → expressionIR
  | «% '?' % ':' %» : typedExpressionIR → typedExpressionIR → typedExpressionIR → expressionIR
  | «`( % `) %» : typeIR → typedExpressionIR → expressionIR
  | «'{#}'» : expressionIR
  | «SEQ `{ % `}» : (_root_.List typedExpressionIR) → expressionIR
  | «SEQ `{ % ',' '...' `}» : (_root_.List typedExpressionIR) → expressionIR
  | «RECORD `{ % `}» : (_root_.List namedExpressionIR) → expressionIR
  | «RECORD `{ % ',' '...' `}» : (_root_.List namedExpressionIR) → expressionIR
  | «ERROR '.' %» : nameIR → expressionIR
  | «% '.' %» : memberAccessBaseIR → nameIR → expressionIR
  | «% `[ % `]» : typedExpressionIR → typedExpressionIR → expressionIR
  | «% `[ % % % `]» : typedExpressionIR → typedExpressionIR → sliceop → typedExpressionIR → expressionIR
  | «% `( % `)» : constructorTargetIR → (_root_.List argumentIR) → expressionIR
  | «% `< % `> `( % `)» : callableTargetIR → (_root_.List typeIR) → (_root_.List argumentIR) → expressionIR
  | «`( % `)» : typedExpressionIR → expressionIR

inductive expressionNoteIR : Type where
  | «`( % % `)» : typeIR → ctk → expressionNoteIR

inductive typedExpressionIR : Type where
  | «% '#' %» : expressionIR → expressionNoteIR → typedExpressionIR

inductive memberAccessBaseIR : Type where
  | TYPE : prefixedNameIR → memberAccessBaseIR
  | «% '#' %» : expressionIR → expressionNoteIR → memberAccessBaseIR

inductive argumentIR : Type where
  | «% '#' %» : expressionIR → expressionNoteIR → argumentIR
  | «% '=' %» : nameIR → typedExpressionIR → argumentIR
  | «% '=' '_'» : nameIR → argumentIR
  | «'_'» : argumentIR

end


mutual

def decEq_fieldTypeIR (a b : fieldTypeIR) : _root_.Decidable (a = b) :=
  match a, b with
    | .«% % % ';'» x0 x1 x2, .«% % % ';'» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typeIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_typeIR (a b : typeIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .VOID, .VOID =>
      _root_.Decidable.isTrue rfl
    | .BOOL, .BOOL =>
      _root_.Decidable.isTrue rfl
    | .ERROR, .ERROR =>
      _root_.Decidable.isTrue rfl
    | .MATCH_KIND, .MATCH_KIND =>
      _root_.Decidable.isTrue rfl
    | .STRING, .STRING =>
      _root_.Decidable.isTrue rfl
    | .INT, .INT =>
      _root_.Decidable.isTrue rfl
    | .«INT `< % `>» x0, .«INT `< % `>» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«BIT `< % `>» x0, .«BIT `< % `>» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«VARBIT `< % `>» x0, .«VARBIT `< % `>» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | ._NAME x0, ._NAME y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .TYPEDEF x0 x1, .TYPEDEF y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typeIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .TYPE x0 x1, .TYPE y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typeIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«LIST `< % `>» x0, .«LIST `< % `>» y0 =>
      match decEq_typeIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«TUPLE `< % `>» x0, .«TUPLE `< % `>» y0 =>
      match decEq_shape_002eb71903a3 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«ARRAY % `[ % `]» x0 x1, .«ARRAY % `[ % `]» y0 y1 =>
      match decEq_typeIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«HEADER_STACK % `[ % `]» x0 x1, .«HEADER_STACK % `[ % `]» y0 y1 =>
      match decEq_typeIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«STRUCT % `< % `> `{ % `}» x0 x1 x2, .«STRUCT % `< % `> `{ % `}» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_d6cdccd864e2 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«HEADER % `< % `> `{ % `}» x0 x1 x2, .«HEADER % `< % `> `{ % `}» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_d6cdccd864e2 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«HEADER_UNION % `< % `> `{ % `}» x0 x1 x2, .«HEADER_UNION % `< % `> `{ % `}» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_d6cdccd864e2 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«ENUM % `{ % `}» x0 x1, .«ENUM % `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«ENUM % `< % `> `{ % `}» x0 x1 x2, .«ENUM % `< % `> `{ % `}» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typeIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«EXTERN % `< % `> %» x0 x1 x2, .«EXTERN % `< % `> %» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_7d3133f0b6e2 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«PARSER % `< % `> `( % `)» x0 x1 x2, .«PARSER % `< % `> `( % `)» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_ec5214aa5618 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«CONTROL % `< % `> `( % `)» x0 x1 x2, .«CONTROL % `< % `> `( % `)» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_ec5214aa5618 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«PACKAGE % `< % `> `{ % `}» x0 x1 x2, .«PACKAGE % `< % `> `{ % `}» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_002eb71903a3 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«TABLE % `{ % `}» x0 x1, .«TABLE % `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .DEFAULT, .DEFAULT =>
      _root_.Decidable.isTrue rfl
    | .HEADER_INVALID, .HEADER_INVALID =>
      _root_.Decidable.isTrue rfl
    | .«SEQ `< % `>» x0, .«SEQ `< % `>» y0 =>
      match decEq_shape_002eb71903a3 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SEQ `< % ',' '...' `>» x0, .«SEQ `< % ',' '...' `>» y0 =>
      match decEq_shape_002eb71903a3 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«RECORD `{ % `}» x0, .«RECORD `{ % `}» y0 =>
      match decEq_shape_d6cdccd864e2 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«RECORD `{ % ',' '...' `}» x0, .«RECORD `{ % ',' '...' `}» y0 =>
      match decEq_shape_d6cdccd864e2 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SET `< % `>» x0, .«SET `< % `>» y0 =>
      match decEq_typeIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«TABLE_ENUM % `{ % `}» x0 x1, .«TABLE_ENUM % `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» x0 x1 x2 x3, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» y0 y1 y2 y3 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; rfl)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .VOID, .BOOL => nomatch hc
    | .VOID, .ERROR => nomatch hc
    | .VOID, .MATCH_KIND => nomatch hc
    | .VOID, .STRING => nomatch hc
    | .VOID, .INT => nomatch hc
    | .VOID, .«INT `< % `>» _ => nomatch hc
    | .VOID, .«BIT `< % `>» _ => nomatch hc
    | .VOID, .«VARBIT `< % `>» _ => nomatch hc
    | .VOID, ._NAME _ => nomatch hc
    | .VOID, .TYPEDEF _ _ => nomatch hc
    | .VOID, .TYPE _ _ => nomatch hc
    | .VOID, .«LIST `< % `>» _ => nomatch hc
    | .VOID, .«TUPLE `< % `>» _ => nomatch hc
    | .VOID, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .VOID, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .VOID, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .VOID, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .VOID, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .VOID, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .VOID, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .VOID, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .VOID, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .VOID, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .VOID, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .VOID, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .VOID, .DEFAULT => nomatch hc
    | .VOID, .HEADER_INVALID => nomatch hc
    | .VOID, .«SEQ `< % `>» _ => nomatch hc
    | .VOID, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .VOID, .«RECORD `{ % `}» _ => nomatch hc
    | .VOID, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .VOID, .«SET `< % `>» _ => nomatch hc
    | .VOID, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .VOID, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .BOOL, .VOID => nomatch hc
    | .BOOL, .ERROR => nomatch hc
    | .BOOL, .MATCH_KIND => nomatch hc
    | .BOOL, .STRING => nomatch hc
    | .BOOL, .INT => nomatch hc
    | .BOOL, .«INT `< % `>» _ => nomatch hc
    | .BOOL, .«BIT `< % `>» _ => nomatch hc
    | .BOOL, .«VARBIT `< % `>» _ => nomatch hc
    | .BOOL, ._NAME _ => nomatch hc
    | .BOOL, .TYPEDEF _ _ => nomatch hc
    | .BOOL, .TYPE _ _ => nomatch hc
    | .BOOL, .«LIST `< % `>» _ => nomatch hc
    | .BOOL, .«TUPLE `< % `>» _ => nomatch hc
    | .BOOL, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .BOOL, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .BOOL, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .BOOL, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .BOOL, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .BOOL, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .BOOL, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .BOOL, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .BOOL, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .BOOL, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .BOOL, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .BOOL, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .BOOL, .DEFAULT => nomatch hc
    | .BOOL, .HEADER_INVALID => nomatch hc
    | .BOOL, .«SEQ `< % `>» _ => nomatch hc
    | .BOOL, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .BOOL, .«RECORD `{ % `}» _ => nomatch hc
    | .BOOL, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .BOOL, .«SET `< % `>» _ => nomatch hc
    | .BOOL, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .BOOL, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .ERROR, .VOID => nomatch hc
    | .ERROR, .BOOL => nomatch hc
    | .ERROR, .MATCH_KIND => nomatch hc
    | .ERROR, .STRING => nomatch hc
    | .ERROR, .INT => nomatch hc
    | .ERROR, .«INT `< % `>» _ => nomatch hc
    | .ERROR, .«BIT `< % `>» _ => nomatch hc
    | .ERROR, .«VARBIT `< % `>» _ => nomatch hc
    | .ERROR, ._NAME _ => nomatch hc
    | .ERROR, .TYPEDEF _ _ => nomatch hc
    | .ERROR, .TYPE _ _ => nomatch hc
    | .ERROR, .«LIST `< % `>» _ => nomatch hc
    | .ERROR, .«TUPLE `< % `>» _ => nomatch hc
    | .ERROR, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .ERROR, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .ERROR, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .ERROR, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .ERROR, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .ERROR, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .ERROR, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .ERROR, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .ERROR, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .ERROR, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .ERROR, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .ERROR, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .ERROR, .DEFAULT => nomatch hc
    | .ERROR, .HEADER_INVALID => nomatch hc
    | .ERROR, .«SEQ `< % `>» _ => nomatch hc
    | .ERROR, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .ERROR, .«RECORD `{ % `}» _ => nomatch hc
    | .ERROR, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .ERROR, .«SET `< % `>» _ => nomatch hc
    | .ERROR, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .ERROR, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .MATCH_KIND, .VOID => nomatch hc
    | .MATCH_KIND, .BOOL => nomatch hc
    | .MATCH_KIND, .ERROR => nomatch hc
    | .MATCH_KIND, .STRING => nomatch hc
    | .MATCH_KIND, .INT => nomatch hc
    | .MATCH_KIND, .«INT `< % `>» _ => nomatch hc
    | .MATCH_KIND, .«BIT `< % `>» _ => nomatch hc
    | .MATCH_KIND, .«VARBIT `< % `>» _ => nomatch hc
    | .MATCH_KIND, ._NAME _ => nomatch hc
    | .MATCH_KIND, .TYPEDEF _ _ => nomatch hc
    | .MATCH_KIND, .TYPE _ _ => nomatch hc
    | .MATCH_KIND, .«LIST `< % `>» _ => nomatch hc
    | .MATCH_KIND, .«TUPLE `< % `>» _ => nomatch hc
    | .MATCH_KIND, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .MATCH_KIND, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .MATCH_KIND, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .MATCH_KIND, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .MATCH_KIND, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .MATCH_KIND, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .MATCH_KIND, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .MATCH_KIND, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .MATCH_KIND, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .MATCH_KIND, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .MATCH_KIND, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .MATCH_KIND, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .MATCH_KIND, .DEFAULT => nomatch hc
    | .MATCH_KIND, .HEADER_INVALID => nomatch hc
    | .MATCH_KIND, .«SEQ `< % `>» _ => nomatch hc
    | .MATCH_KIND, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .MATCH_KIND, .«RECORD `{ % `}» _ => nomatch hc
    | .MATCH_KIND, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .MATCH_KIND, .«SET `< % `>» _ => nomatch hc
    | .MATCH_KIND, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .MATCH_KIND, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .STRING, .VOID => nomatch hc
    | .STRING, .BOOL => nomatch hc
    | .STRING, .ERROR => nomatch hc
    | .STRING, .MATCH_KIND => nomatch hc
    | .STRING, .INT => nomatch hc
    | .STRING, .«INT `< % `>» _ => nomatch hc
    | .STRING, .«BIT `< % `>» _ => nomatch hc
    | .STRING, .«VARBIT `< % `>» _ => nomatch hc
    | .STRING, ._NAME _ => nomatch hc
    | .STRING, .TYPEDEF _ _ => nomatch hc
    | .STRING, .TYPE _ _ => nomatch hc
    | .STRING, .«LIST `< % `>» _ => nomatch hc
    | .STRING, .«TUPLE `< % `>» _ => nomatch hc
    | .STRING, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .STRING, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .STRING, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .STRING, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .STRING, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .STRING, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .STRING, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .STRING, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .STRING, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .STRING, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .STRING, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .STRING, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .STRING, .DEFAULT => nomatch hc
    | .STRING, .HEADER_INVALID => nomatch hc
    | .STRING, .«SEQ `< % `>» _ => nomatch hc
    | .STRING, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .STRING, .«RECORD `{ % `}» _ => nomatch hc
    | .STRING, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .STRING, .«SET `< % `>» _ => nomatch hc
    | .STRING, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .STRING, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .INT, .VOID => nomatch hc
    | .INT, .BOOL => nomatch hc
    | .INT, .ERROR => nomatch hc
    | .INT, .MATCH_KIND => nomatch hc
    | .INT, .STRING => nomatch hc
    | .INT, .«INT `< % `>» _ => nomatch hc
    | .INT, .«BIT `< % `>» _ => nomatch hc
    | .INT, .«VARBIT `< % `>» _ => nomatch hc
    | .INT, ._NAME _ => nomatch hc
    | .INT, .TYPEDEF _ _ => nomatch hc
    | .INT, .TYPE _ _ => nomatch hc
    | .INT, .«LIST `< % `>» _ => nomatch hc
    | .INT, .«TUPLE `< % `>» _ => nomatch hc
    | .INT, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .INT, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .INT, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .INT, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .INT, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .INT, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .INT, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .INT, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .INT, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .INT, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .INT, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .INT, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .INT, .DEFAULT => nomatch hc
    | .INT, .HEADER_INVALID => nomatch hc
    | .INT, .«SEQ `< % `>» _ => nomatch hc
    | .INT, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .INT, .«RECORD `{ % `}» _ => nomatch hc
    | .INT, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .INT, .«SET `< % `>» _ => nomatch hc
    | .INT, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .INT, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«INT `< % `>» _, .VOID => nomatch hc
    | .«INT `< % `>» _, .BOOL => nomatch hc
    | .«INT `< % `>» _, .ERROR => nomatch hc
    | .«INT `< % `>» _, .MATCH_KIND => nomatch hc
    | .«INT `< % `>» _, .STRING => nomatch hc
    | .«INT `< % `>» _, .INT => nomatch hc
    | .«INT `< % `>» _, .«BIT `< % `>» _ => nomatch hc
    | .«INT `< % `>» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«INT `< % `>» _, ._NAME _ => nomatch hc
    | .«INT `< % `>» _, .TYPEDEF _ _ => nomatch hc
    | .«INT `< % `>» _, .TYPE _ _ => nomatch hc
    | .«INT `< % `>» _, .«LIST `< % `>» _ => nomatch hc
    | .«INT `< % `>» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«INT `< % `>» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«INT `< % `>» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«INT `< % `>» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«INT `< % `>» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«INT `< % `>» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«INT `< % `>» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«INT `< % `>» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«INT `< % `>» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«INT `< % `>» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«INT `< % `>» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«INT `< % `>» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«INT `< % `>» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«INT `< % `>» _, .DEFAULT => nomatch hc
    | .«INT `< % `>» _, .HEADER_INVALID => nomatch hc
    | .«INT `< % `>» _, .«SEQ `< % `>» _ => nomatch hc
    | .«INT `< % `>» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«INT `< % `>» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«INT `< % `>» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«INT `< % `>» _, .«SET `< % `>» _ => nomatch hc
    | .«INT `< % `>» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«INT `< % `>» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .VOID => nomatch hc
    | .«BIT `< % `>» _, .BOOL => nomatch hc
    | .«BIT `< % `>» _, .ERROR => nomatch hc
    | .«BIT `< % `>» _, .MATCH_KIND => nomatch hc
    | .«BIT `< % `>» _, .STRING => nomatch hc
    | .«BIT `< % `>» _, .INT => nomatch hc
    | .«BIT `< % `>» _, .«INT `< % `>» _ => nomatch hc
    | .«BIT `< % `>» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«BIT `< % `>» _, ._NAME _ => nomatch hc
    | .«BIT `< % `>» _, .TYPEDEF _ _ => nomatch hc
    | .«BIT `< % `>» _, .TYPE _ _ => nomatch hc
    | .«BIT `< % `>» _, .«LIST `< % `>» _ => nomatch hc
    | .«BIT `< % `>» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«BIT `< % `>» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«BIT `< % `>» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«BIT `< % `>» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«BIT `< % `>» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«BIT `< % `>» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«BIT `< % `>» _, .DEFAULT => nomatch hc
    | .«BIT `< % `>» _, .HEADER_INVALID => nomatch hc
    | .«BIT `< % `>» _, .«SEQ `< % `>» _ => nomatch hc
    | .«BIT `< % `>» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«BIT `< % `>» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«BIT `< % `>» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«BIT `< % `>» _, .«SET `< % `>» _ => nomatch hc
    | .«BIT `< % `>» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«BIT `< % `>» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .VOID => nomatch hc
    | .«VARBIT `< % `>» _, .BOOL => nomatch hc
    | .«VARBIT `< % `>» _, .ERROR => nomatch hc
    | .«VARBIT `< % `>» _, .MATCH_KIND => nomatch hc
    | .«VARBIT `< % `>» _, .STRING => nomatch hc
    | .«VARBIT `< % `>» _, .INT => nomatch hc
    | .«VARBIT `< % `>» _, .«INT `< % `>» _ => nomatch hc
    | .«VARBIT `< % `>» _, .«BIT `< % `>» _ => nomatch hc
    | .«VARBIT `< % `>» _, ._NAME _ => nomatch hc
    | .«VARBIT `< % `>» _, .TYPEDEF _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .TYPE _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«LIST `< % `>» _ => nomatch hc
    | .«VARBIT `< % `>» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«VARBIT `< % `>» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .DEFAULT => nomatch hc
    | .«VARBIT `< % `>» _, .HEADER_INVALID => nomatch hc
    | .«VARBIT `< % `>» _, .«SEQ `< % `>» _ => nomatch hc
    | .«VARBIT `< % `>» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«VARBIT `< % `>» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«VARBIT `< % `>» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«VARBIT `< % `>» _, .«SET `< % `>» _ => nomatch hc
    | .«VARBIT `< % `>» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«VARBIT `< % `>» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | ._NAME _, .VOID => nomatch hc
    | ._NAME _, .BOOL => nomatch hc
    | ._NAME _, .ERROR => nomatch hc
    | ._NAME _, .MATCH_KIND => nomatch hc
    | ._NAME _, .STRING => nomatch hc
    | ._NAME _, .INT => nomatch hc
    | ._NAME _, .«INT `< % `>» _ => nomatch hc
    | ._NAME _, .«BIT `< % `>» _ => nomatch hc
    | ._NAME _, .«VARBIT `< % `>» _ => nomatch hc
    | ._NAME _, .TYPEDEF _ _ => nomatch hc
    | ._NAME _, .TYPE _ _ => nomatch hc
    | ._NAME _, .«LIST `< % `>» _ => nomatch hc
    | ._NAME _, .«TUPLE `< % `>» _ => nomatch hc
    | ._NAME _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | ._NAME _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | ._NAME _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | ._NAME _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | ._NAME _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | ._NAME _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | ._NAME _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | ._NAME _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | ._NAME _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | ._NAME _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | ._NAME _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | ._NAME _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | ._NAME _, .DEFAULT => nomatch hc
    | ._NAME _, .HEADER_INVALID => nomatch hc
    | ._NAME _, .«SEQ `< % `>» _ => nomatch hc
    | ._NAME _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | ._NAME _, .«RECORD `{ % `}» _ => nomatch hc
    | ._NAME _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | ._NAME _, .«SET `< % `>» _ => nomatch hc
    | ._NAME _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | ._NAME _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .TYPEDEF _ _, .VOID => nomatch hc
    | .TYPEDEF _ _, .BOOL => nomatch hc
    | .TYPEDEF _ _, .ERROR => nomatch hc
    | .TYPEDEF _ _, .MATCH_KIND => nomatch hc
    | .TYPEDEF _ _, .STRING => nomatch hc
    | .TYPEDEF _ _, .INT => nomatch hc
    | .TYPEDEF _ _, .«INT `< % `>» _ => nomatch hc
    | .TYPEDEF _ _, .«BIT `< % `>» _ => nomatch hc
    | .TYPEDEF _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .TYPEDEF _ _, ._NAME _ => nomatch hc
    | .TYPEDEF _ _, .TYPE _ _ => nomatch hc
    | .TYPEDEF _ _, .«LIST `< % `>» _ => nomatch hc
    | .TYPEDEF _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .TYPEDEF _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .TYPEDEF _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .TYPEDEF _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPEDEF _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPEDEF _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPEDEF _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .TYPEDEF _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPEDEF _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .TYPEDEF _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .TYPEDEF _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .TYPEDEF _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPEDEF _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .TYPEDEF _ _, .DEFAULT => nomatch hc
    | .TYPEDEF _ _, .HEADER_INVALID => nomatch hc
    | .TYPEDEF _ _, .«SEQ `< % `>» _ => nomatch hc
    | .TYPEDEF _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .TYPEDEF _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .TYPEDEF _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .TYPEDEF _ _, .«SET `< % `>» _ => nomatch hc
    | .TYPEDEF _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .TYPEDEF _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .TYPE _ _, .VOID => nomatch hc
    | .TYPE _ _, .BOOL => nomatch hc
    | .TYPE _ _, .ERROR => nomatch hc
    | .TYPE _ _, .MATCH_KIND => nomatch hc
    | .TYPE _ _, .STRING => nomatch hc
    | .TYPE _ _, .INT => nomatch hc
    | .TYPE _ _, .«INT `< % `>» _ => nomatch hc
    | .TYPE _ _, .«BIT `< % `>» _ => nomatch hc
    | .TYPE _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .TYPE _ _, ._NAME _ => nomatch hc
    | .TYPE _ _, .TYPEDEF _ _ => nomatch hc
    | .TYPE _ _, .«LIST `< % `>» _ => nomatch hc
    | .TYPE _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .TYPE _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .TYPE _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .TYPE _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPE _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPE _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPE _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .TYPE _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPE _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .TYPE _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .TYPE _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .TYPE _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .TYPE _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .TYPE _ _, .DEFAULT => nomatch hc
    | .TYPE _ _, .HEADER_INVALID => nomatch hc
    | .TYPE _ _, .«SEQ `< % `>» _ => nomatch hc
    | .TYPE _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .TYPE _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .TYPE _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .TYPE _ _, .«SET `< % `>» _ => nomatch hc
    | .TYPE _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .TYPE _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .VOID => nomatch hc
    | .«LIST `< % `>» _, .BOOL => nomatch hc
    | .«LIST `< % `>» _, .ERROR => nomatch hc
    | .«LIST `< % `>» _, .MATCH_KIND => nomatch hc
    | .«LIST `< % `>» _, .STRING => nomatch hc
    | .«LIST `< % `>» _, .INT => nomatch hc
    | .«LIST `< % `>» _, .«INT `< % `>» _ => nomatch hc
    | .«LIST `< % `>» _, .«BIT `< % `>» _ => nomatch hc
    | .«LIST `< % `>» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«LIST `< % `>» _, ._NAME _ => nomatch hc
    | .«LIST `< % `>» _, .TYPEDEF _ _ => nomatch hc
    | .«LIST `< % `>» _, .TYPE _ _ => nomatch hc
    | .«LIST `< % `>» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«LIST `< % `>» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«LIST `< % `>» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«LIST `< % `>» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«LIST `< % `>» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«LIST `< % `>» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«LIST `< % `>» _, .DEFAULT => nomatch hc
    | .«LIST `< % `>» _, .HEADER_INVALID => nomatch hc
    | .«LIST `< % `>» _, .«SEQ `< % `>» _ => nomatch hc
    | .«LIST `< % `>» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«LIST `< % `>» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«LIST `< % `>» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«LIST `< % `>» _, .«SET `< % `>» _ => nomatch hc
    | .«LIST `< % `>» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«LIST `< % `>» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .VOID => nomatch hc
    | .«TUPLE `< % `>» _, .BOOL => nomatch hc
    | .«TUPLE `< % `>» _, .ERROR => nomatch hc
    | .«TUPLE `< % `>» _, .MATCH_KIND => nomatch hc
    | .«TUPLE `< % `>» _, .STRING => nomatch hc
    | .«TUPLE `< % `>» _, .INT => nomatch hc
    | .«TUPLE `< % `>» _, .«INT `< % `>» _ => nomatch hc
    | .«TUPLE `< % `>» _, .«BIT `< % `>» _ => nomatch hc
    | .«TUPLE `< % `>» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«TUPLE `< % `>» _, ._NAME _ => nomatch hc
    | .«TUPLE `< % `>» _, .TYPEDEF _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .TYPE _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«LIST `< % `>» _ => nomatch hc
    | .«TUPLE `< % `>» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .DEFAULT => nomatch hc
    | .«TUPLE `< % `>» _, .HEADER_INVALID => nomatch hc
    | .«TUPLE `< % `>» _, .«SEQ `< % `>» _ => nomatch hc
    | .«TUPLE `< % `>» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«TUPLE `< % `>» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«TUPLE `< % `>» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«TUPLE `< % `>» _, .«SET `< % `>» _ => nomatch hc
    | .«TUPLE `< % `>» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«TUPLE `< % `>» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .VOID => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .BOOL => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .ERROR => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .MATCH_KIND => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .STRING => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .INT => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«INT `< % `>» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«BIT `< % `>» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, ._NAME _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .TYPEDEF _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .TYPE _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«LIST `< % `>» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .DEFAULT => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .HEADER_INVALID => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«SET `< % `>» _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«ARRAY % `[ % `]» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .VOID => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .BOOL => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .ERROR => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .MATCH_KIND => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .STRING => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .INT => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«INT `< % `>» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«BIT `< % `>» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, ._NAME _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .TYPEDEF _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .TYPE _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«LIST `< % `>» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .DEFAULT => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .HEADER_INVALID => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«SET `< % `>» _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«HEADER_STACK % `[ % `]» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .VOID => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .BOOL => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .ERROR => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .MATCH_KIND => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .STRING => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .INT => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, ._NAME _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .TYPE _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .DEFAULT => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .HEADER_INVALID => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«STRUCT % `< % `> `{ % `}» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .VOID => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .BOOL => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .ERROR => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .MATCH_KIND => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .STRING => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .INT => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, ._NAME _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .TYPE _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .DEFAULT => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .HEADER_INVALID => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«HEADER % `< % `> `{ % `}» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .VOID => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .BOOL => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .ERROR => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .MATCH_KIND => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .STRING => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .INT => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, ._NAME _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .TYPE _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .DEFAULT => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .HEADER_INVALID => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«HEADER_UNION % `< % `> `{ % `}» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .VOID => nomatch hc
    | .«ENUM % `{ % `}» _ _, .BOOL => nomatch hc
    | .«ENUM % `{ % `}» _ _, .ERROR => nomatch hc
    | .«ENUM % `{ % `}» _ _, .MATCH_KIND => nomatch hc
    | .«ENUM % `{ % `}» _ _, .STRING => nomatch hc
    | .«ENUM % `{ % `}» _ _, .INT => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«INT `< % `>» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«BIT `< % `>» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, ._NAME _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .TYPEDEF _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .TYPE _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«LIST `< % `>» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .DEFAULT => nomatch hc
    | .«ENUM % `{ % `}» _ _, .HEADER_INVALID => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«SET `< % `>» _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«ENUM % `{ % `}» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .VOID => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .BOOL => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .ERROR => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .MATCH_KIND => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .STRING => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .INT => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, ._NAME _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .TYPE _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .DEFAULT => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .HEADER_INVALID => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«ENUM % `< % `> `{ % `}» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .VOID => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .BOOL => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .ERROR => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .MATCH_KIND => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .STRING => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .INT => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, ._NAME _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .TYPE _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .DEFAULT => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .HEADER_INVALID => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«EXTERN % `< % `> %» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .VOID => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .BOOL => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .ERROR => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .MATCH_KIND => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .STRING => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .INT => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, ._NAME _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .TYPE _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .DEFAULT => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .HEADER_INVALID => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«PARSER % `< % `> `( % `)» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .VOID => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .BOOL => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .ERROR => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .MATCH_KIND => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .STRING => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .INT => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, ._NAME _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .TYPE _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .DEFAULT => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .HEADER_INVALID => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«CONTROL % `< % `> `( % `)» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .VOID => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .BOOL => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .ERROR => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .MATCH_KIND => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .STRING => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .INT => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, ._NAME _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .TYPE _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .DEFAULT => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .HEADER_INVALID => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«PACKAGE % `< % `> `{ % `}» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .VOID => nomatch hc
    | .«TABLE % `{ % `}» _ _, .BOOL => nomatch hc
    | .«TABLE % `{ % `}» _ _, .ERROR => nomatch hc
    | .«TABLE % `{ % `}» _ _, .MATCH_KIND => nomatch hc
    | .«TABLE % `{ % `}» _ _, .STRING => nomatch hc
    | .«TABLE % `{ % `}» _ _, .INT => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«INT `< % `>» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«BIT `< % `>» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, ._NAME _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .TYPEDEF _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .TYPE _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«LIST `< % `>» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .DEFAULT => nomatch hc
    | .«TABLE % `{ % `}» _ _, .HEADER_INVALID => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«SET `< % `>» _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«TABLE % `{ % `}» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .DEFAULT, .VOID => nomatch hc
    | .DEFAULT, .BOOL => nomatch hc
    | .DEFAULT, .ERROR => nomatch hc
    | .DEFAULT, .MATCH_KIND => nomatch hc
    | .DEFAULT, .STRING => nomatch hc
    | .DEFAULT, .INT => nomatch hc
    | .DEFAULT, .«INT `< % `>» _ => nomatch hc
    | .DEFAULT, .«BIT `< % `>» _ => nomatch hc
    | .DEFAULT, .«VARBIT `< % `>» _ => nomatch hc
    | .DEFAULT, ._NAME _ => nomatch hc
    | .DEFAULT, .TYPEDEF _ _ => nomatch hc
    | .DEFAULT, .TYPE _ _ => nomatch hc
    | .DEFAULT, .«LIST `< % `>» _ => nomatch hc
    | .DEFAULT, .«TUPLE `< % `>» _ => nomatch hc
    | .DEFAULT, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .DEFAULT, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .DEFAULT, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .DEFAULT, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .DEFAULT, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .DEFAULT, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .DEFAULT, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .DEFAULT, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .DEFAULT, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .DEFAULT, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .DEFAULT, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .DEFAULT, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .DEFAULT, .HEADER_INVALID => nomatch hc
    | .DEFAULT, .«SEQ `< % `>» _ => nomatch hc
    | .DEFAULT, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .DEFAULT, .«RECORD `{ % `}» _ => nomatch hc
    | .DEFAULT, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .DEFAULT, .«SET `< % `>» _ => nomatch hc
    | .DEFAULT, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .DEFAULT, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .HEADER_INVALID, .VOID => nomatch hc
    | .HEADER_INVALID, .BOOL => nomatch hc
    | .HEADER_INVALID, .ERROR => nomatch hc
    | .HEADER_INVALID, .MATCH_KIND => nomatch hc
    | .HEADER_INVALID, .STRING => nomatch hc
    | .HEADER_INVALID, .INT => nomatch hc
    | .HEADER_INVALID, .«INT `< % `>» _ => nomatch hc
    | .HEADER_INVALID, .«BIT `< % `>» _ => nomatch hc
    | .HEADER_INVALID, .«VARBIT `< % `>» _ => nomatch hc
    | .HEADER_INVALID, ._NAME _ => nomatch hc
    | .HEADER_INVALID, .TYPEDEF _ _ => nomatch hc
    | .HEADER_INVALID, .TYPE _ _ => nomatch hc
    | .HEADER_INVALID, .«LIST `< % `>» _ => nomatch hc
    | .HEADER_INVALID, .«TUPLE `< % `>» _ => nomatch hc
    | .HEADER_INVALID, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .HEADER_INVALID, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .HEADER_INVALID, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .HEADER_INVALID, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .HEADER_INVALID, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .HEADER_INVALID, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .HEADER_INVALID, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .HEADER_INVALID, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .HEADER_INVALID, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .HEADER_INVALID, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .HEADER_INVALID, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .HEADER_INVALID, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .HEADER_INVALID, .DEFAULT => nomatch hc
    | .HEADER_INVALID, .«SEQ `< % `>» _ => nomatch hc
    | .HEADER_INVALID, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .HEADER_INVALID, .«RECORD `{ % `}» _ => nomatch hc
    | .HEADER_INVALID, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .HEADER_INVALID, .«SET `< % `>» _ => nomatch hc
    | .HEADER_INVALID, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .HEADER_INVALID, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .VOID => nomatch hc
    | .«SEQ `< % `>» _, .BOOL => nomatch hc
    | .«SEQ `< % `>» _, .ERROR => nomatch hc
    | .«SEQ `< % `>» _, .MATCH_KIND => nomatch hc
    | .«SEQ `< % `>» _, .STRING => nomatch hc
    | .«SEQ `< % `>» _, .INT => nomatch hc
    | .«SEQ `< % `>» _, .«INT `< % `>» _ => nomatch hc
    | .«SEQ `< % `>» _, .«BIT `< % `>» _ => nomatch hc
    | .«SEQ `< % `>» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«SEQ `< % `>» _, ._NAME _ => nomatch hc
    | .«SEQ `< % `>» _, .TYPEDEF _ _ => nomatch hc
    | .«SEQ `< % `>» _, .TYPE _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«LIST `< % `>» _ => nomatch hc
    | .«SEQ `< % `>» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«SEQ `< % `>» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«SEQ `< % `>» _, .DEFAULT => nomatch hc
    | .«SEQ `< % `>» _, .HEADER_INVALID => nomatch hc
    | .«SEQ `< % `>» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«SEQ `< % `>» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SEQ `< % `>» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SEQ `< % `>» _, .«SET `< % `>» _ => nomatch hc
    | .«SEQ `< % `>» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«SEQ `< % `>» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .VOID => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .BOOL => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .ERROR => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .MATCH_KIND => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .STRING => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .INT => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«INT `< % `>» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«BIT `< % `>» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, ._NAME _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .TYPEDEF _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .TYPE _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«LIST `< % `>» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .DEFAULT => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .HEADER_INVALID => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«SEQ `< % `>» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«SET `< % `>» _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«SEQ `< % ',' '...' `>» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .VOID => nomatch hc
    | .«RECORD `{ % `}» _, .BOOL => nomatch hc
    | .«RECORD `{ % `}» _, .ERROR => nomatch hc
    | .«RECORD `{ % `}» _, .MATCH_KIND => nomatch hc
    | .«RECORD `{ % `}» _, .STRING => nomatch hc
    | .«RECORD `{ % `}» _, .INT => nomatch hc
    | .«RECORD `{ % `}» _, .«INT `< % `>» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«BIT `< % `>» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«RECORD `{ % `}» _, ._NAME _ => nomatch hc
    | .«RECORD `{ % `}» _, .TYPEDEF _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .TYPE _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«LIST `< % `>» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .DEFAULT => nomatch hc
    | .«RECORD `{ % `}» _, .HEADER_INVALID => nomatch hc
    | .«RECORD `{ % `}» _, .«SEQ `< % `>» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SET `< % `>» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .VOID => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .BOOL => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .ERROR => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .MATCH_KIND => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .STRING => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .INT => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«INT `< % `>» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«BIT `< % `>» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, ._NAME _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .TYPEDEF _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .TYPE _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«LIST `< % `>» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .DEFAULT => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .HEADER_INVALID => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SEQ `< % `>» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SET `< % `>» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SET `< % `>» _, .VOID => nomatch hc
    | .«SET `< % `>» _, .BOOL => nomatch hc
    | .«SET `< % `>» _, .ERROR => nomatch hc
    | .«SET `< % `>» _, .MATCH_KIND => nomatch hc
    | .«SET `< % `>» _, .STRING => nomatch hc
    | .«SET `< % `>» _, .INT => nomatch hc
    | .«SET `< % `>» _, .«INT `< % `>» _ => nomatch hc
    | .«SET `< % `>» _, .«BIT `< % `>» _ => nomatch hc
    | .«SET `< % `>» _, .«VARBIT `< % `>» _ => nomatch hc
    | .«SET `< % `>» _, ._NAME _ => nomatch hc
    | .«SET `< % `>» _, .TYPEDEF _ _ => nomatch hc
    | .«SET `< % `>» _, .TYPE _ _ => nomatch hc
    | .«SET `< % `>» _, .«LIST `< % `>» _ => nomatch hc
    | .«SET `< % `>» _, .«TUPLE `< % `>» _ => nomatch hc
    | .«SET `< % `>» _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«SET `< % `>» _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«SET `< % `>» _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SET `< % `>» _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SET `< % `>» _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SET `< % `>» _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«SET `< % `>» _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SET `< % `>» _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«SET `< % `>» _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«SET `< % `>» _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«SET `< % `>» _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«SET `< % `>» _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«SET `< % `>» _, .DEFAULT => nomatch hc
    | .«SET `< % `>» _, .HEADER_INVALID => nomatch hc
    | .«SET `< % `>» _, .«SEQ `< % `>» _ => nomatch hc
    | .«SET `< % `>» _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«SET `< % `>» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SET `< % `>» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SET `< % `>» _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
    | .«SET `< % `>» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .VOID => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .BOOL => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .ERROR => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .MATCH_KIND => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .STRING => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .INT => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«INT `< % `>» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«BIT `< % `>» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, ._NAME _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .TYPEDEF _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .TYPE _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«LIST `< % `>» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .DEFAULT => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .HEADER_INVALID => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«SET `< % `>» _ => nomatch hc
    | .«TABLE_ENUM % `{ % `}» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .VOID => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .BOOL => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .ERROR => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .MATCH_KIND => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .STRING => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .INT => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«INT `< % `>» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«BIT `< % `>» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«VARBIT `< % `>» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, ._NAME _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .TYPEDEF _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .TYPE _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«LIST `< % `>» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«TUPLE `< % `>» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«ARRAY % `[ % `]» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«HEADER_STACK % `[ % `]» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«STRUCT % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«HEADER % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«HEADER_UNION % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«ENUM % `{ % `}» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«ENUM % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«EXTERN % `< % `> %» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«PARSER % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«CONTROL % `< % `> `( % `)» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«PACKAGE % `< % `> `{ % `}» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«TABLE % `{ % `}» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .DEFAULT => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .HEADER_INVALID => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SEQ `< % `>» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SEQ `< % ',' '...' `>» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SET `< % `>» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«TABLE_ENUM % `{ % `}» _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_shape_002eb71903a3 (a b : (_root_.List typeIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_typeIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_002eb71903a3 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_shape_d6cdccd864e2 (a b : (_root_.List fieldTypeIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_fieldTypeIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_d6cdccd864e2 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_shape_7d3133f0b6e2 (a b : (set (pair callableId externMethodTypeDefIR))) : _root_.Decidable (a = b) :=
  match a, b with
    | .«`{ % `}» x0, .«`{ % `}» y0 =>
      match decEq_shape_1808a22e0c27 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_shape_1808a22e0c27 (a b : (_root_.List (pair callableId externMethodTypeDefIR))) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_shape_93170a729c29 x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_1808a22e0c27 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_shape_93170a729c29 (a b : (pair callableId externMethodTypeDefIR)) : _root_.Decidable (a = b) :=
  match a, b with
    | .«% ':' %» x0 x1, .«% ':' %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_externMethodTypeDefIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_externMethodTypeDefIR (a b : externMethodTypeDefIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» x0 x1 x2 x3 x4, .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» y0 y1 y2 y3 y4 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match decEq_shape_ec5214aa5618 x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match decEq_typeIR x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; rfl)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» x0 x1 x2 x3 x4, .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» y0 y1 y2 y3 y4 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match decEq_shape_ec5214aa5618 x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match decEq_typeIR x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; rfl)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» _ _ _ _ _, .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => nomatch hc
    | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» _ _ _ _ _, .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_shape_ec5214aa5618 (a b : (_root_.List parameterIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_parameterIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_ec5214aa5618 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_parameterIR (a b : parameterIR) : _root_.Decidable (a = b) :=
  match a, b with
    | .«% % % % %» x0 x1 x2 x3 x4, .«% % % % %» y0 y1 y2 y3 y4 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_typeIR x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match decEq_shape_923cac0108d2 x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; rfl)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_shape_923cac0108d2 (a b : (_root_.Option parameterInitializerIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | _root_.Option.none, _root_.Option.none => _root_.Decidable.isTrue rfl
  | _root_.Option.some x0, _root_.Option.some y0 =>
    match decEq_parameterInitializerIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      _root_.Decidable.isTrue (by cases h0; rfl)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | _root_.Option.none, _root_.Option.some _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _root_.Option.some _, _root_.Option.none => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_parameterInitializerIR (a b : parameterInitializerIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .«'=' %» x0, .«'=' %» y0 =>
      match decEq_typedExpressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'=' _VALUE %» x0, .«'=' _VALUE %» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'=' %» _, .«'=' _VALUE %» _ => nomatch hc
    | .«'=' _VALUE %» _, .«'=' %» _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_typedExpressionIR (a b : typedExpressionIR) : _root_.Decidable (a = b) :=
  match a, b with
    | .«% '#' %» x0 x1, .«% '#' %» y0 y1 =>
      match decEq_expressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_expressionNoteIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_expressionIR (a b : expressionIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .TRUE, .TRUE =>
      _root_.Decidable.isTrue rfl
    | .FALSE, .FALSE =>
      _root_.Decidable.isTrue rfl
    | .D x0, .D y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% W %» x0 x1, .«% W %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% S %» x0 x1, .«% S %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'"' % '"'» x0, .«'"' % '"'» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | ._BARE x0, ._BARE y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'.' %» x0, .«'.' %» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'...'», .«'...'» =>
      _root_.Decidable.isTrue rfl
    | .«% %» x0 x1, .«% %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typedExpressionIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% % %» x0 x1 x2, .«% % %» y0 y1 y2 =>
      match decEq_typedExpressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_typedExpressionIR x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% '?' % ':' %» x0 x1 x2, .«% '?' % ':' %» y0 y1 y2 =>
      match decEq_typedExpressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typedExpressionIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_typedExpressionIR x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«`( % `) %» x0 x1, .«`( % `) %» y0 y1 =>
      match decEq_typeIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typedExpressionIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'{#}'», .«'{#}'» =>
      _root_.Decidable.isTrue rfl
    | .«SEQ `{ % `}» x0, .«SEQ `{ % `}» y0 =>
      match decEq_shape_9b6d9349f232 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SEQ `{ % ',' '...' `}» x0, .«SEQ `{ % ',' '...' `}» y0 =>
      match decEq_shape_9b6d9349f232 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«RECORD `{ % `}» x0, .«RECORD `{ % `}» y0 =>
      match decEq_shape_7aa8ff8b88e4 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«RECORD `{ % ',' '...' `}» x0, .«RECORD `{ % ',' '...' `}» y0 =>
      match decEq_shape_7aa8ff8b88e4 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«ERROR '.' %» x0, .«ERROR '.' %» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% '.' %» x0 x1, .«% '.' %» y0 y1 =>
      match decEq_memberAccessBaseIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% `[ % `]» x0 x1, .«% `[ % `]» y0 y1 =>
      match decEq_typedExpressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typedExpressionIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% `[ % % % `]» x0 x1 x2 x3, .«% `[ % % % `]» y0 y1 y2 y3 =>
      match decEq_typedExpressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typedExpressionIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match decEq_typedExpressionIR x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; rfl)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% `( % `)» x0 x1, .«% `( % `)» y0 y1 =>
      match decEq_constructorTargetIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_5673b07b4cf2 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% `< % `> `( % `)» x0 x1 x2, .«% `< % `> `( % `)» y0 y1 y2 =>
      match decEq_callableTargetIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_5673b07b4cf2 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«`( % `)» x0, .«`( % `)» y0 =>
      match decEq_typedExpressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .TRUE, .FALSE => nomatch hc
    | .TRUE, .D _ => nomatch hc
    | .TRUE, .«% W %» _ _ => nomatch hc
    | .TRUE, .«% S %» _ _ => nomatch hc
    | .TRUE, .«'"' % '"'» _ => nomatch hc
    | .TRUE, ._BARE _ => nomatch hc
    | .TRUE, .«'.' %» _ => nomatch hc
    | .TRUE, .«'...'» => nomatch hc
    | .TRUE, .«% %» _ _ => nomatch hc
    | .TRUE, .«% % %» _ _ _ => nomatch hc
    | .TRUE, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .TRUE, .«`( % `) %» _ _ => nomatch hc
    | .TRUE, .«'{#}'» => nomatch hc
    | .TRUE, .«SEQ `{ % `}» _ => nomatch hc
    | .TRUE, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .TRUE, .«RECORD `{ % `}» _ => nomatch hc
    | .TRUE, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .TRUE, .«ERROR '.' %» _ => nomatch hc
    | .TRUE, .«% '.' %» _ _ => nomatch hc
    | .TRUE, .«% `[ % `]» _ _ => nomatch hc
    | .TRUE, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .TRUE, .«% `( % `)» _ _ => nomatch hc
    | .TRUE, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .TRUE, .«`( % `)» _ => nomatch hc
    | .FALSE, .TRUE => nomatch hc
    | .FALSE, .D _ => nomatch hc
    | .FALSE, .«% W %» _ _ => nomatch hc
    | .FALSE, .«% S %» _ _ => nomatch hc
    | .FALSE, .«'"' % '"'» _ => nomatch hc
    | .FALSE, ._BARE _ => nomatch hc
    | .FALSE, .«'.' %» _ => nomatch hc
    | .FALSE, .«'...'» => nomatch hc
    | .FALSE, .«% %» _ _ => nomatch hc
    | .FALSE, .«% % %» _ _ _ => nomatch hc
    | .FALSE, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .FALSE, .«`( % `) %» _ _ => nomatch hc
    | .FALSE, .«'{#}'» => nomatch hc
    | .FALSE, .«SEQ `{ % `}» _ => nomatch hc
    | .FALSE, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .FALSE, .«RECORD `{ % `}» _ => nomatch hc
    | .FALSE, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .FALSE, .«ERROR '.' %» _ => nomatch hc
    | .FALSE, .«% '.' %» _ _ => nomatch hc
    | .FALSE, .«% `[ % `]» _ _ => nomatch hc
    | .FALSE, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .FALSE, .«% `( % `)» _ _ => nomatch hc
    | .FALSE, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .FALSE, .«`( % `)» _ => nomatch hc
    | .D _, .TRUE => nomatch hc
    | .D _, .FALSE => nomatch hc
    | .D _, .«% W %» _ _ => nomatch hc
    | .D _, .«% S %» _ _ => nomatch hc
    | .D _, .«'"' % '"'» _ => nomatch hc
    | .D _, ._BARE _ => nomatch hc
    | .D _, .«'.' %» _ => nomatch hc
    | .D _, .«'...'» => nomatch hc
    | .D _, .«% %» _ _ => nomatch hc
    | .D _, .«% % %» _ _ _ => nomatch hc
    | .D _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .D _, .«`( % `) %» _ _ => nomatch hc
    | .D _, .«'{#}'» => nomatch hc
    | .D _, .«SEQ `{ % `}» _ => nomatch hc
    | .D _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .D _, .«RECORD `{ % `}» _ => nomatch hc
    | .D _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .D _, .«ERROR '.' %» _ => nomatch hc
    | .D _, .«% '.' %» _ _ => nomatch hc
    | .D _, .«% `[ % `]» _ _ => nomatch hc
    | .D _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .D _, .«% `( % `)» _ _ => nomatch hc
    | .D _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .D _, .«`( % `)» _ => nomatch hc
    | .«% W %» _ _, .TRUE => nomatch hc
    | .«% W %» _ _, .FALSE => nomatch hc
    | .«% W %» _ _, .D _ => nomatch hc
    | .«% W %» _ _, .«% S %» _ _ => nomatch hc
    | .«% W %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% W %» _ _, ._BARE _ => nomatch hc
    | .«% W %» _ _, .«'.' %» _ => nomatch hc
    | .«% W %» _ _, .«'...'» => nomatch hc
    | .«% W %» _ _, .«% %» _ _ => nomatch hc
    | .«% W %» _ _, .«% % %» _ _ _ => nomatch hc
    | .«% W %» _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% W %» _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% W %» _ _, .«'{#}'» => nomatch hc
    | .«% W %» _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% W %» _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% W %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% W %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% W %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% W %» _ _, .«% '.' %» _ _ => nomatch hc
    | .«% W %» _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% W %» _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% W %» _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% W %» _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% W %» _ _, .«`( % `)» _ => nomatch hc
    | .«% S %» _ _, .TRUE => nomatch hc
    | .«% S %» _ _, .FALSE => nomatch hc
    | .«% S %» _ _, .D _ => nomatch hc
    | .«% S %» _ _, .«% W %» _ _ => nomatch hc
    | .«% S %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% S %» _ _, ._BARE _ => nomatch hc
    | .«% S %» _ _, .«'.' %» _ => nomatch hc
    | .«% S %» _ _, .«'...'» => nomatch hc
    | .«% S %» _ _, .«% %» _ _ => nomatch hc
    | .«% S %» _ _, .«% % %» _ _ _ => nomatch hc
    | .«% S %» _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% S %» _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% S %» _ _, .«'{#}'» => nomatch hc
    | .«% S %» _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% S %» _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% S %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% S %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% S %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% S %» _ _, .«% '.' %» _ _ => nomatch hc
    | .«% S %» _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% S %» _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% S %» _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% S %» _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% S %» _ _, .«`( % `)» _ => nomatch hc
    | .«'"' % '"'» _, .TRUE => nomatch hc
    | .«'"' % '"'» _, .FALSE => nomatch hc
    | .«'"' % '"'» _, .D _ => nomatch hc
    | .«'"' % '"'» _, .«% W %» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% S %» _ _ => nomatch hc
    | .«'"' % '"'» _, ._BARE _ => nomatch hc
    | .«'"' % '"'» _, .«'.' %» _ => nomatch hc
    | .«'"' % '"'» _, .«'...'» => nomatch hc
    | .«'"' % '"'» _, .«% %» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% % %» _ _ _ => nomatch hc
    | .«'"' % '"'» _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«'"' % '"'» _, .«`( % `) %» _ _ => nomatch hc
    | .«'"' % '"'» _, .«'{#}'» => nomatch hc
    | .«'"' % '"'» _, .«SEQ `{ % `}» _ => nomatch hc
    | .«'"' % '"'» _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«'"' % '"'» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«'"' % '"'» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«'"' % '"'» _, .«ERROR '.' %» _ => nomatch hc
    | .«'"' % '"'» _, .«% '.' %» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% `[ % `]» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«'"' % '"'» _, .«% `( % `)» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«'"' % '"'» _, .«`( % `)» _ => nomatch hc
    | ._BARE _, .TRUE => nomatch hc
    | ._BARE _, .FALSE => nomatch hc
    | ._BARE _, .D _ => nomatch hc
    | ._BARE _, .«% W %» _ _ => nomatch hc
    | ._BARE _, .«% S %» _ _ => nomatch hc
    | ._BARE _, .«'"' % '"'» _ => nomatch hc
    | ._BARE _, .«'.' %» _ => nomatch hc
    | ._BARE _, .«'...'» => nomatch hc
    | ._BARE _, .«% %» _ _ => nomatch hc
    | ._BARE _, .«% % %» _ _ _ => nomatch hc
    | ._BARE _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | ._BARE _, .«`( % `) %» _ _ => nomatch hc
    | ._BARE _, .«'{#}'» => nomatch hc
    | ._BARE _, .«SEQ `{ % `}» _ => nomatch hc
    | ._BARE _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | ._BARE _, .«RECORD `{ % `}» _ => nomatch hc
    | ._BARE _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | ._BARE _, .«ERROR '.' %» _ => nomatch hc
    | ._BARE _, .«% '.' %» _ _ => nomatch hc
    | ._BARE _, .«% `[ % `]» _ _ => nomatch hc
    | ._BARE _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | ._BARE _, .«% `( % `)» _ _ => nomatch hc
    | ._BARE _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | ._BARE _, .«`( % `)» _ => nomatch hc
    | .«'.' %» _, .TRUE => nomatch hc
    | .«'.' %» _, .FALSE => nomatch hc
    | .«'.' %» _, .D _ => nomatch hc
    | .«'.' %» _, .«% W %» _ _ => nomatch hc
    | .«'.' %» _, .«% S %» _ _ => nomatch hc
    | .«'.' %» _, .«'"' % '"'» _ => nomatch hc
    | .«'.' %» _, ._BARE _ => nomatch hc
    | .«'.' %» _, .«'...'» => nomatch hc
    | .«'.' %» _, .«% %» _ _ => nomatch hc
    | .«'.' %» _, .«% % %» _ _ _ => nomatch hc
    | .«'.' %» _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«'.' %» _, .«`( % `) %» _ _ => nomatch hc
    | .«'.' %» _, .«'{#}'» => nomatch hc
    | .«'.' %» _, .«SEQ `{ % `}» _ => nomatch hc
    | .«'.' %» _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«'.' %» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«'.' %» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«'.' %» _, .«ERROR '.' %» _ => nomatch hc
    | .«'.' %» _, .«% '.' %» _ _ => nomatch hc
    | .«'.' %» _, .«% `[ % `]» _ _ => nomatch hc
    | .«'.' %» _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«'.' %» _, .«% `( % `)» _ _ => nomatch hc
    | .«'.' %» _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«'.' %» _, .«`( % `)» _ => nomatch hc
    | .«'...'», .TRUE => nomatch hc
    | .«'...'», .FALSE => nomatch hc
    | .«'...'», .D _ => nomatch hc
    | .«'...'», .«% W %» _ _ => nomatch hc
    | .«'...'», .«% S %» _ _ => nomatch hc
    | .«'...'», .«'"' % '"'» _ => nomatch hc
    | .«'...'», ._BARE _ => nomatch hc
    | .«'...'», .«'.' %» _ => nomatch hc
    | .«'...'», .«% %» _ _ => nomatch hc
    | .«'...'», .«% % %» _ _ _ => nomatch hc
    | .«'...'», .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«'...'», .«`( % `) %» _ _ => nomatch hc
    | .«'...'», .«'{#}'» => nomatch hc
    | .«'...'», .«SEQ `{ % `}» _ => nomatch hc
    | .«'...'», .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«'...'», .«RECORD `{ % `}» _ => nomatch hc
    | .«'...'», .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«'...'», .«ERROR '.' %» _ => nomatch hc
    | .«'...'», .«% '.' %» _ _ => nomatch hc
    | .«'...'», .«% `[ % `]» _ _ => nomatch hc
    | .«'...'», .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«'...'», .«% `( % `)» _ _ => nomatch hc
    | .«'...'», .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«'...'», .«`( % `)» _ => nomatch hc
    | .«% %» _ _, .TRUE => nomatch hc
    | .«% %» _ _, .FALSE => nomatch hc
    | .«% %» _ _, .D _ => nomatch hc
    | .«% %» _ _, .«% W %» _ _ => nomatch hc
    | .«% %» _ _, .«% S %» _ _ => nomatch hc
    | .«% %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% %» _ _, ._BARE _ => nomatch hc
    | .«% %» _ _, .«'.' %» _ => nomatch hc
    | .«% %» _ _, .«'...'» => nomatch hc
    | .«% %» _ _, .«% % %» _ _ _ => nomatch hc
    | .«% %» _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% %» _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% %» _ _, .«'{#}'» => nomatch hc
    | .«% %» _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% %» _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% %» _ _, .«% '.' %» _ _ => nomatch hc
    | .«% %» _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% %» _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% %» _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% %» _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% %» _ _, .«`( % `)» _ => nomatch hc
    | .«% % %» _ _ _, .TRUE => nomatch hc
    | .«% % %» _ _ _, .FALSE => nomatch hc
    | .«% % %» _ _ _, .D _ => nomatch hc
    | .«% % %» _ _ _, .«% W %» _ _ => nomatch hc
    | .«% % %» _ _ _, .«% S %» _ _ => nomatch hc
    | .«% % %» _ _ _, .«'"' % '"'» _ => nomatch hc
    | .«% % %» _ _ _, ._BARE _ => nomatch hc
    | .«% % %» _ _ _, .«'.' %» _ => nomatch hc
    | .«% % %» _ _ _, .«'...'» => nomatch hc
    | .«% % %» _ _ _, .«% %» _ _ => nomatch hc
    | .«% % %» _ _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% % %» _ _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% % %» _ _ _, .«'{#}'» => nomatch hc
    | .«% % %» _ _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% % %» _ _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% % %» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% % %» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% % %» _ _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% % %» _ _ _, .«% '.' %» _ _ => nomatch hc
    | .«% % %» _ _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% % %» _ _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% % %» _ _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% % %» _ _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% % %» _ _ _, .«`( % `)» _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .TRUE => nomatch hc
    | .«% '?' % ':' %» _ _ _, .FALSE => nomatch hc
    | .«% '?' % ':' %» _ _ _, .D _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% W %» _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% S %» _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«'"' % '"'» _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, ._BARE _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«'.' %» _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«'...'» => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% %» _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% % %» _ _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«'{#}'» => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% '.' %» _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% '?' % ':' %» _ _ _, .«`( % `)» _ => nomatch hc
    | .«`( % `) %» _ _, .TRUE => nomatch hc
    | .«`( % `) %» _ _, .FALSE => nomatch hc
    | .«`( % `) %» _ _, .D _ => nomatch hc
    | .«`( % `) %» _ _, .«% W %» _ _ => nomatch hc
    | .«`( % `) %» _ _, .«% S %» _ _ => nomatch hc
    | .«`( % `) %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«`( % `) %» _ _, ._BARE _ => nomatch hc
    | .«`( % `) %» _ _, .«'.' %» _ => nomatch hc
    | .«`( % `) %» _ _, .«'...'» => nomatch hc
    | .«`( % `) %» _ _, .«% %» _ _ => nomatch hc
    | .«`( % `) %» _ _, .«% % %» _ _ _ => nomatch hc
    | .«`( % `) %» _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«`( % `) %» _ _, .«'{#}'» => nomatch hc
    | .«`( % `) %» _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«`( % `) %» _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«`( % `) %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«`( % `) %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«`( % `) %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«`( % `) %» _ _, .«% '.' %» _ _ => nomatch hc
    | .«`( % `) %» _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«`( % `) %» _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«`( % `) %» _ _, .«% `( % `)» _ _ => nomatch hc
    | .«`( % `) %» _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«`( % `) %» _ _, .«`( % `)» _ => nomatch hc
    | .«'{#}'», .TRUE => nomatch hc
    | .«'{#}'», .FALSE => nomatch hc
    | .«'{#}'», .D _ => nomatch hc
    | .«'{#}'», .«% W %» _ _ => nomatch hc
    | .«'{#}'», .«% S %» _ _ => nomatch hc
    | .«'{#}'», .«'"' % '"'» _ => nomatch hc
    | .«'{#}'», ._BARE _ => nomatch hc
    | .«'{#}'», .«'.' %» _ => nomatch hc
    | .«'{#}'», .«'...'» => nomatch hc
    | .«'{#}'», .«% %» _ _ => nomatch hc
    | .«'{#}'», .«% % %» _ _ _ => nomatch hc
    | .«'{#}'», .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«'{#}'», .«`( % `) %» _ _ => nomatch hc
    | .«'{#}'», .«SEQ `{ % `}» _ => nomatch hc
    | .«'{#}'», .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«'{#}'», .«RECORD `{ % `}» _ => nomatch hc
    | .«'{#}'», .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«'{#}'», .«ERROR '.' %» _ => nomatch hc
    | .«'{#}'», .«% '.' %» _ _ => nomatch hc
    | .«'{#}'», .«% `[ % `]» _ _ => nomatch hc
    | .«'{#}'», .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«'{#}'», .«% `( % `)» _ _ => nomatch hc
    | .«'{#}'», .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«'{#}'», .«`( % `)» _ => nomatch hc
    | .«SEQ `{ % `}» _, .TRUE => nomatch hc
    | .«SEQ `{ % `}» _, .FALSE => nomatch hc
    | .«SEQ `{ % `}» _, .D _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% W %» _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% S %» _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«'"' % '"'» _ => nomatch hc
    | .«SEQ `{ % `}» _, ._BARE _ => nomatch hc
    | .«SEQ `{ % `}» _, .«'.' %» _ => nomatch hc
    | .«SEQ `{ % `}» _, .«'...'» => nomatch hc
    | .«SEQ `{ % `}» _, .«% %» _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% % %» _ _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«`( % `) %» _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«'{#}'» => nomatch hc
    | .«SEQ `{ % `}» _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«SEQ `{ % `}» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SEQ `{ % `}» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SEQ `{ % `}» _, .«ERROR '.' %» _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% '.' %» _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% `[ % `]» _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% `( % `)» _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«SEQ `{ % `}» _, .«`( % `)» _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .TRUE => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .FALSE => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .D _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% W %» _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% S %» _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«'"' % '"'» _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, ._BARE _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«'.' %» _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«'...'» => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% %» _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% % %» _ _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«`( % `) %» _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«'{#}'» => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«SEQ `{ % `}» _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«ERROR '.' %» _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% '.' %» _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% `[ % `]» _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% `( % `)» _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«SEQ `{ % ',' '...' `}» _, .«`( % `)» _ => nomatch hc
    | .«RECORD `{ % `}» _, .TRUE => nomatch hc
    | .«RECORD `{ % `}» _, .FALSE => nomatch hc
    | .«RECORD `{ % `}» _, .D _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% W %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% S %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«'"' % '"'» _ => nomatch hc
    | .«RECORD `{ % `}» _, ._BARE _ => nomatch hc
    | .«RECORD `{ % `}» _, .«'.' %» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«'...'» => nomatch hc
    | .«RECORD `{ % `}» _, .«% %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% % %» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«`( % `) %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«'{#}'» => nomatch hc
    | .«RECORD `{ % `}» _, .«SEQ `{ % `}» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«ERROR '.' %» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% '.' %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% `[ % `]» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% `( % `)» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«`( % `)» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .TRUE => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .FALSE => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .D _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% W %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% S %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«'"' % '"'» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, ._BARE _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«'.' %» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«'...'» => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% % %» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«`( % `) %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«'{#}'» => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SEQ `{ % `}» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«ERROR '.' %» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% '.' %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% `[ % `]» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% `( % `)» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«`( % `)» _ => nomatch hc
    | .«ERROR '.' %» _, .TRUE => nomatch hc
    | .«ERROR '.' %» _, .FALSE => nomatch hc
    | .«ERROR '.' %» _, .D _ => nomatch hc
    | .«ERROR '.' %» _, .«% W %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% S %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«'"' % '"'» _ => nomatch hc
    | .«ERROR '.' %» _, ._BARE _ => nomatch hc
    | .«ERROR '.' %» _, .«'.' %» _ => nomatch hc
    | .«ERROR '.' %» _, .«'...'» => nomatch hc
    | .«ERROR '.' %» _, .«% %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% % %» _ _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«ERROR '.' %» _, .«`( % `) %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«'{#}'» => nomatch hc
    | .«ERROR '.' %» _, .«SEQ `{ % `}» _ => nomatch hc
    | .«ERROR '.' %» _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«ERROR '.' %» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«ERROR '.' %» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«ERROR '.' %» _, .«% '.' %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% `[ % `]» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% `( % `)» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«ERROR '.' %» _, .«`( % `)» _ => nomatch hc
    | .«% '.' %» _ _, .TRUE => nomatch hc
    | .«% '.' %» _ _, .FALSE => nomatch hc
    | .«% '.' %» _ _, .D _ => nomatch hc
    | .«% '.' %» _ _, .«% W %» _ _ => nomatch hc
    | .«% '.' %» _ _, .«% S %» _ _ => nomatch hc
    | .«% '.' %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% '.' %» _ _, ._BARE _ => nomatch hc
    | .«% '.' %» _ _, .«'.' %» _ => nomatch hc
    | .«% '.' %» _ _, .«'...'» => nomatch hc
    | .«% '.' %» _ _, .«% %» _ _ => nomatch hc
    | .«% '.' %» _ _, .«% % %» _ _ _ => nomatch hc
    | .«% '.' %» _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% '.' %» _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% '.' %» _ _, .«'{#}'» => nomatch hc
    | .«% '.' %» _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% '.' %» _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% '.' %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% '.' %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% '.' %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% '.' %» _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% '.' %» _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% '.' %» _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% '.' %» _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% '.' %» _ _, .«`( % `)» _ => nomatch hc
    | .«% `[ % `]» _ _, .TRUE => nomatch hc
    | .«% `[ % `]» _ _, .FALSE => nomatch hc
    | .«% `[ % `]» _ _, .D _ => nomatch hc
    | .«% `[ % `]» _ _, .«% W %» _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«% S %» _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% `[ % `]» _ _, ._BARE _ => nomatch hc
    | .«% `[ % `]» _ _, .«'.' %» _ => nomatch hc
    | .«% `[ % `]» _ _, .«'...'» => nomatch hc
    | .«% `[ % `]» _ _, .«% %» _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«% % %» _ _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«'{#}'» => nomatch hc
    | .«% `[ % `]» _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% `[ % `]» _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% `[ % `]» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% `[ % `]» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% `[ % `]» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% `[ % `]» _ _, .«% '.' %» _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% `[ % `]» _ _, .«`( % `)» _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .TRUE => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .FALSE => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .D _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% W %» _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% S %» _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«'"' % '"'» _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, ._BARE _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«'.' %» _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«'...'» => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% %» _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% % %» _ _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«'{#}'» => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% '.' %» _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% `[ % % % `]» _ _ _ _, .«`( % `)» _ => nomatch hc
    | .«% `( % `)» _ _, .TRUE => nomatch hc
    | .«% `( % `)» _ _, .FALSE => nomatch hc
    | .«% `( % `)» _ _, .D _ => nomatch hc
    | .«% `( % `)» _ _, .«% W %» _ _ => nomatch hc
    | .«% `( % `)» _ _, .«% S %» _ _ => nomatch hc
    | .«% `( % `)» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% `( % `)» _ _, ._BARE _ => nomatch hc
    | .«% `( % `)» _ _, .«'.' %» _ => nomatch hc
    | .«% `( % `)» _ _, .«'...'» => nomatch hc
    | .«% `( % `)» _ _, .«% %» _ _ => nomatch hc
    | .«% `( % `)» _ _, .«% % %» _ _ _ => nomatch hc
    | .«% `( % `)» _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% `( % `)» _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% `( % `)» _ _, .«'{#}'» => nomatch hc
    | .«% `( % `)» _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% `( % `)» _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% `( % `)» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% `( % `)» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% `( % `)» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% `( % `)» _ _, .«% '.' %» _ _ => nomatch hc
    | .«% `( % `)» _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% `( % `)» _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% `( % `)» _ _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
    | .«% `( % `)» _ _, .«`( % `)» _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .TRUE => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .FALSE => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .D _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% W %» _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% S %» _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«'"' % '"'» _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, ._BARE _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«'.' %» _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«'...'» => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% %» _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% % %» _ _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«`( % `) %» _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«'{#}'» => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«SEQ `{ % `}» _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% '.' %» _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% `[ % `]» _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«% `( % `)» _ _ => nomatch hc
    | .«% `< % `> `( % `)» _ _ _, .«`( % `)» _ => nomatch hc
    | .«`( % `)» _, .TRUE => nomatch hc
    | .«`( % `)» _, .FALSE => nomatch hc
    | .«`( % `)» _, .D _ => nomatch hc
    | .«`( % `)» _, .«% W %» _ _ => nomatch hc
    | .«`( % `)» _, .«% S %» _ _ => nomatch hc
    | .«`( % `)» _, .«'"' % '"'» _ => nomatch hc
    | .«`( % `)» _, ._BARE _ => nomatch hc
    | .«`( % `)» _, .«'.' %» _ => nomatch hc
    | .«`( % `)» _, .«'...'» => nomatch hc
    | .«`( % `)» _, .«% %» _ _ => nomatch hc
    | .«`( % `)» _, .«% % %» _ _ _ => nomatch hc
    | .«`( % `)» _, .«% '?' % ':' %» _ _ _ => nomatch hc
    | .«`( % `)» _, .«`( % `) %» _ _ => nomatch hc
    | .«`( % `)» _, .«'{#}'» => nomatch hc
    | .«`( % `)» _, .«SEQ `{ % `}» _ => nomatch hc
    | .«`( % `)» _, .«SEQ `{ % ',' '...' `}» _ => nomatch hc
    | .«`( % `)» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«`( % `)» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«`( % `)» _, .«ERROR '.' %» _ => nomatch hc
    | .«`( % `)» _, .«% '.' %» _ _ => nomatch hc
    | .«`( % `)» _, .«% `[ % `]» _ _ => nomatch hc
    | .«`( % `)» _, .«% `[ % % % `]» _ _ _ _ => nomatch hc
    | .«`( % `)» _, .«% `( % `)» _ _ => nomatch hc
    | .«`( % `)» _, .«% `< % `> `( % `)» _ _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_shape_9b6d9349f232 (a b : (_root_.List typedExpressionIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_typedExpressionIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_9b6d9349f232 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_shape_7aa8ff8b88e4 (a b : (_root_.List namedExpressionIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_namedExpressionIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_7aa8ff8b88e4 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_namedExpressionIR (a b : namedExpressionIR) : _root_.Decidable (a = b) :=
  match a, b with
    | .«% '=' %» x0 x1, .«% '=' %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typedExpressionIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_memberAccessBaseIR (a b : memberAccessBaseIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .TYPE x0, .TYPE y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% '#' %» x0 x1, .«% '#' %» y0 y1 =>
      match decEq_expressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_expressionNoteIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .TYPE _, .«% '#' %» _ _ => nomatch hc
    | .«% '#' %» _ _, .TYPE _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_expressionNoteIR (a b : expressionNoteIR) : _root_.Decidable (a = b) :=
  match a, b with
    | .«`( % % `)» x0 x1, .«`( % % `)» y0 y1 =>
      match decEq_typeIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_constructorTargetIR (a b : constructorTargetIR) : _root_.Decidable (a = b) :=
  match a, b with
    | .«% `< % `>» x0 x1, .«% `< % `>» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_002eb71903a3 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_shape_5673b07b4cf2 (a b : (_root_.List argumentIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_argumentIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_5673b07b4cf2 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_argumentIR (a b : argumentIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .«% '#' %» x0 x1, .«% '#' %» y0 y1 =>
      match decEq_expressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_expressionNoteIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% '=' %» x0 x1, .«% '=' %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_typedExpressionIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% '=' '_'» x0, .«% '=' '_'» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'_'», .«'_'» =>
      _root_.Decidable.isTrue rfl
    | .«% '#' %» _ _, .«% '=' %» _ _ => nomatch hc
    | .«% '#' %» _ _, .«% '=' '_'» _ => nomatch hc
    | .«% '#' %» _ _, .«'_'» => nomatch hc
    | .«% '=' %» _ _, .«% '#' %» _ _ => nomatch hc
    | .«% '=' %» _ _, .«% '=' '_'» _ => nomatch hc
    | .«% '=' %» _ _, .«'_'» => nomatch hc
    | .«% '=' '_'» _, .«% '#' %» _ _ => nomatch hc
    | .«% '=' '_'» _, .«% '=' %» _ _ => nomatch hc
    | .«% '=' '_'» _, .«'_'» => nomatch hc
    | .«'_'», .«% '#' %» _ _ => nomatch hc
    | .«'_'», .«% '=' %» _ _ => nomatch hc
    | .«'_'», .«% '=' '_'» _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_callableTargetIR (a b : callableTargetIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | ._BARE x0, ._BARE y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'.' %» x0, .«'.' %» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% '.' %» x0 x1, .«% '.' %» y0 y1 =>
      match decEq_typedExpressionIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«TYPE % '.' %» x0 x1, .«TYPE % '.' %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«`( % `)» x0, .«`( % `)» y0 =>
      match decEq_callableTargetIR x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | ._BARE _, .«'.' %» _ => nomatch hc
    | ._BARE _, .«% '.' %» _ _ => nomatch hc
    | ._BARE _, .«TYPE % '.' %» _ _ => nomatch hc
    | ._BARE _, .«`( % `)» _ => nomatch hc
    | .«'.' %» _, ._BARE _ => nomatch hc
    | .«'.' %» _, .«% '.' %» _ _ => nomatch hc
    | .«'.' %» _, .«TYPE % '.' %» _ _ => nomatch hc
    | .«'.' %» _, .«`( % `)» _ => nomatch hc
    | .«% '.' %» _ _, ._BARE _ => nomatch hc
    | .«% '.' %» _ _, .«'.' %» _ => nomatch hc
    | .«% '.' %» _ _, .«TYPE % '.' %» _ _ => nomatch hc
    | .«% '.' %» _ _, .«`( % `)» _ => nomatch hc
    | .«TYPE % '.' %» _ _, ._BARE _ => nomatch hc
    | .«TYPE % '.' %» _ _, .«'.' %» _ => nomatch hc
    | .«TYPE % '.' %» _ _, .«% '.' %» _ _ => nomatch hc
    | .«TYPE % '.' %» _ _, .«`( % `)» _ => nomatch hc
    | .«`( % `)» _, ._BARE _ => nomatch hc
    | .«`( % `)» _, .«'.' %» _ => nomatch hc
    | .«`( % `)» _, .«% '.' %» _ _ => nomatch hc
    | .«`( % `)» _, .«TYPE % '.' %» _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

end

instance : _root_.DecidableEq fieldTypeIR := decEq_fieldTypeIR

instance : _root_.DecidableEq typeIR := decEq_typeIR

instance : _root_.DecidableEq parameterInitializerIR := decEq_parameterInitializerIR

instance : _root_.DecidableEq parameterIR := decEq_parameterIR

instance : _root_.DecidableEq externMethodTypeDefIR := decEq_externMethodTypeDefIR

instance : _root_.DecidableEq namedExpressionIR := decEq_namedExpressionIR

instance : _root_.DecidableEq callableTargetIR := decEq_callableTargetIR

instance : _root_.DecidableEq constructorTargetIR := decEq_constructorTargetIR

instance : _root_.DecidableEq expressionIR := decEq_expressionIR

instance : _root_.DecidableEq expressionNoteIR := decEq_expressionNoteIR

instance : _root_.DecidableEq typedExpressionIR := decEq_typedExpressionIR

instance : _root_.DecidableEq memberAccessBaseIR := decEq_memberAccessBaseIR

instance : _root_.DecidableEq argumentIR := decEq_argumentIR


abbrev externMethodTypeDefEnv : Type := (map callableId externMethodTypeDefIR)


abbrev typeArgumentIR : Type := typeIR


abbrev parameterInitializerOptIR : Type := (_root_.Option parameterInitializerIR)


abbrev namedExpressionListIR : Type := (_root_.List namedExpressionIR)


abbrev typedExpressionListIR : Type := (_root_.List typedExpressionIR)


abbrev typeArgumentListIR : Type := (_root_.List typeArgumentIR)


abbrev argumentListIR : Type := (_root_.List argumentIR)


inductive typedefTypeIR : Type where
  | TYPEDEF : typeId → typeIR → typedefTypeIR
deriving _root_.DecidableEq


inductive newTypeIR : Type where
  | TYPE : typeId → typeIR → newTypeIR
deriving _root_.DecidableEq


inductive aliasTypeIR : Type where
  | TYPEDEF : typeId → typeIR → aliasTypeIR
  | TYPE : typeId → typeIR → aliasTypeIR
deriving _root_.DecidableEq


inductive listTypeIR : Type where
  | «LIST `< % `>» : typeIR → listTypeIR
deriving _root_.DecidableEq


inductive tupleTypeIR : Type where
  | «TUPLE `< % `>» : (_root_.List typeIR) → tupleTypeIR
deriving _root_.DecidableEq


inductive arrayTypeIR : Type where
  | «ARRAY % `[ % `]» : typeIR → _root_.Nat → arrayTypeIR
deriving _root_.DecidableEq


inductive headerStackTypeIR : Type where
  | «HEADER_STACK % `[ % `]» : typeIR → _root_.Nat → headerStackTypeIR
deriving _root_.DecidableEq


inductive structTypeIR : Type where
  | «STRUCT % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → structTypeIR
deriving _root_.DecidableEq


inductive headerTypeIR : Type where
  | «HEADER % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → headerTypeIR
deriving _root_.DecidableEq


inductive headerUnionTypeIR : Type where
  | «HEADER_UNION % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → headerUnionTypeIR
deriving _root_.DecidableEq


inductive serializableEnumTypeIR : Type where
  | «ENUM % `< % `> `{ % `}» : typeId → typeIR → (_root_.List valueFieldIR) → serializableEnumTypeIR
deriving _root_.DecidableEq

end SpecTec
