import SpecTecDecl0007

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive p4program : Type where
  | _EMPTY : p4program
  | «% %» : p4program → declaration → p4program
  | «% ';'» : p4program → p4program
deriving _root_.DecidableEq


inductive cursor : Type where
  | GLOBAL : cursor
  | BLOCK : cursor
  | LOCAL : cursor
deriving _root_.DecidableEq


abbrev nameIR : Type := _root_.String


abbrev id : Type := nameIR


abbrev typeId : Type := nameIR


inductive callTargetId : Type where
  | «% `( % `)» : nameIR → (_root_.List id) → callTargetId
deriving _root_.DecidableEq


abbrev callableId : Type := callTargetId


abbrev constructorId : Type := callTargetId


def «$callableId':case_2:downcast:0» (arg0 : parameterList) : (_root_.Option parameter) := match arg0 with | .«% % % % %» field0 field1 field2 field3 field4 => some (parameter.«% % % % %» field0 field1 field2 field3 field4) | _ => none


def «$callableId':case_3:downcast:0» (arg0 : parameterList) : (_root_.Option nonEmptyParameterList) := match arg0 with | .«% % % % %» field0 field1 field2 field3 field4 => some (nonEmptyParameterList.«% % % % %» field0 field1 field2 field3 field4) | .«% ',' %» field0 field1 => some (nonEmptyParameterList.«% ',' %» field0 field1) | _ => none


abbrev objectId : Type := (_root_.List nameIR)


inductive boolValue : Type where
  | _B : _root_.Bool → boolValue
deriving _root_.DecidableEq


inductive errorValue : Type where
  | «ERROR '.' %» : nameIR → errorValue
deriving _root_.DecidableEq


inductive matchKindValue : Type where
  | «MATCH_KIND '.' %» : nameIR → matchKindValue
deriving _root_.DecidableEq


abbrev stringValue : Type := stringLiteral


inductive integerValue : Type where
  | D : _root_.Int → integerValue
  | «% W %» : _root_.Nat → _root_.Int → integerValue
  | «% S %» : _root_.Nat → _root_.Int → integerValue
  | «% '.' % V %» : _root_.Nat → _root_.Nat → _root_.Int → integerValue
deriving _root_.DecidableEq


inductive baseValue : Type where
  | _B : _root_.Bool → baseValue
  | «ERROR '.' %» : nameIR → baseValue
  | «MATCH_KIND '.' %» : nameIR → baseValue
  | «'"' % '"'» : _root_.String → baseValue
  | D : _root_.Int → baseValue
  | «% W %» : _root_.Nat → _root_.Int → baseValue
  | «% S %» : _root_.Nat → _root_.Int → baseValue
  | «% '.' % V %» : _root_.Nat → _root_.Nat → _root_.Int → baseValue
deriving _root_.DecidableEq


inductive objectReferenceValue : Type where
  | REF : objectId → objectReferenceValue
deriving _root_.DecidableEq


inductive defaultValue : Type where
  | DEFAULT : defaultValue
deriving _root_.DecidableEq


inductive invalidHeaderValue : Type where
  | «'{#}'» : invalidHeaderValue
deriving _root_.DecidableEq


inductive tableMetadataEnumValue : Type where
  | «TABLE_ENUM % '.' %» : typeId → nameIR → tableMetadataEnumValue
deriving _root_.DecidableEq


mutual

inductive fieldValue : Type where
  | «% % ';'» : value → nameIR → fieldValue

inductive value : Type where
  | _B : _root_.Bool → value
  | «ERROR '.' %» : nameIR → value
  | «MATCH_KIND '.' %» : nameIR → value
  | «'"' % '"'» : _root_.String → value
  | D : _root_.Int → value
  | «% W %» : _root_.Nat → _root_.Int → value
  | «% S %» : _root_.Nat → _root_.Int → value
  | «% '.' % V %» : _root_.Nat → _root_.Nat → _root_.Int → value
  | «LIST `[ % `]» : (_root_.List value) → value
  | «TUPLE `( % `)» : (_root_.List value) → value
  | «ARRAY `[ % `]» : (_root_.List value) → value
  | «HEADER_STACK `[ % `( % `) `]» : (_root_.List value) → _root_.Nat → value
  | «STRUCT % `{ % `}» : typeId → (_root_.List fieldValue) → value
  | «HEADER % `{ % ';' % `}» : typeId → _root_.Bool → (_root_.List fieldValue) → value
  | «HEADER_UNION % `{ % `}» : typeId → (_root_.List fieldValue) → value
  | «% '.' %» : typeId → nameIR → value
  | «% '.' % '.' %» : typeId → nameIR → value → value
  | REF : objectId → value
  | DEFAULT : value
  | «'{#}'» : value
  | «SEQ `( % `)» : (_root_.List value) → value
  | «SEQ `( % ',' '...' `)» : (_root_.List value) → value
  | «RECORD `{ % `}» : (_root_.List fieldValue) → value
  | «RECORD `{ % ',' '...' `}» : (_root_.List fieldValue) → value
  | «SET `{ % `}» : value → value
  | «SET `{ % `( % `) `}» : (_root_.List value) → _root_.Nat → value
  | «SET `{ % '&&&' % `}» : value → value → value
  | «SET `{ % '..' % `}» : value → value → value
  | «SET `{ '...' `}» : value
  | «TABLE_ENUM % '.' %» : typeId → nameIR → value
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolValue → boolValue → tableMetadataEnumValue → value

end


mutual

def decEq_fieldValue (a b : fieldValue) : _root_.Decidable (a = b) :=
  match a, b with
    | .«% % ';'» x0 x1, .«% % ';'» y0 y1 =>
      match decEq_value x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_value (a b : value) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | ._B x0, ._B y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«ERROR '.' %» x0, .«ERROR '.' %» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«MATCH_KIND '.' %» x0, .«MATCH_KIND '.' %» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«'"' % '"'» x0, .«'"' % '"'» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
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
    | .«% '.' % V %» x0 x1 x2, .«% '.' % V %» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«LIST `[ % `]» x0, .«LIST `[ % `]» y0 =>
      match decEq_shape_87ed6afdba0f x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«TUPLE `( % `)» x0, .«TUPLE `( % `)» y0 =>
      match decEq_shape_87ed6afdba0f x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«ARRAY `[ % `]» x0, .«ARRAY `[ % `]» y0 =>
      match decEq_shape_87ed6afdba0f x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«HEADER_STACK `[ % `( % `) `]» x0 x1, .«HEADER_STACK `[ % `( % `) `]» y0 y1 =>
      match decEq_shape_87ed6afdba0f x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«STRUCT % `{ % `}» x0 x1, .«STRUCT % `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_2b5100be8236 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«HEADER % `{ % ';' % `}» x0 x1 x2, .«HEADER % `{ % ';' % `}» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_shape_2b5100be8236 x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«HEADER_UNION % `{ % `}» x0 x1, .«HEADER_UNION % `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_2b5100be8236 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% '.' %» x0 x1, .«% '.' %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% '.' % '.' %» x0 x1 x2, .«% '.' % '.' %» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_value x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .REF x0, .REF y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .DEFAULT, .DEFAULT =>
      _root_.Decidable.isTrue rfl
    | .«'{#}'», .«'{#}'» =>
      _root_.Decidable.isTrue rfl
    | .«SEQ `( % `)» x0, .«SEQ `( % `)» y0 =>
      match decEq_shape_87ed6afdba0f x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SEQ `( % ',' '...' `)» x0, .«SEQ `( % ',' '...' `)» y0 =>
      match decEq_shape_87ed6afdba0f x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«RECORD `{ % `}» x0, .«RECORD `{ % `}» y0 =>
      match decEq_shape_2b5100be8236 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«RECORD `{ % ',' '...' `}» x0, .«RECORD `{ % ',' '...' `}» y0 =>
      match decEq_shape_2b5100be8236 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SET `{ % `}» x0, .«SET `{ % `}» y0 =>
      match decEq_value x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SET `{ % `( % `) `}» x0 x1, .«SET `{ % `( % `) `}» y0 y1 =>
      match decEq_shape_87ed6afdba0f x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SET `{ % '&&&' % `}» x0 x1, .«SET `{ % '&&&' % `}» y0 y1 =>
      match decEq_value x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_value x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SET `{ % '..' % `}» x0 x1, .«SET `{ % '..' % `}» y0 y1 =>
      match decEq_value x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_value x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«SET `{ '...' `}», .«SET `{ '...' `}» =>
      _root_.Decidable.isTrue rfl
    | .«TABLE_ENUM % '.' %» x0 x1, .«TABLE_ENUM % '.' %» y0 y1 =>
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
    | ._B _, .«ERROR '.' %» _ => nomatch hc
    | ._B _, .«MATCH_KIND '.' %» _ => nomatch hc
    | ._B _, .«'"' % '"'» _ => nomatch hc
    | ._B _, .D _ => nomatch hc
    | ._B _, .«% W %» _ _ => nomatch hc
    | ._B _, .«% S %» _ _ => nomatch hc
    | ._B _, .«% '.' % V %» _ _ _ => nomatch hc
    | ._B _, .«LIST `[ % `]» _ => nomatch hc
    | ._B _, .«TUPLE `( % `)» _ => nomatch hc
    | ._B _, .«ARRAY `[ % `]» _ => nomatch hc
    | ._B _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | ._B _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | ._B _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | ._B _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | ._B _, .«% '.' %» _ _ => nomatch hc
    | ._B _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | ._B _, .REF _ => nomatch hc
    | ._B _, .DEFAULT => nomatch hc
    | ._B _, .«'{#}'» => nomatch hc
    | ._B _, .«SEQ `( % `)» _ => nomatch hc
    | ._B _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | ._B _, .«RECORD `{ % `}» _ => nomatch hc
    | ._B _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | ._B _, .«SET `{ % `}» _ => nomatch hc
    | ._B _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | ._B _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | ._B _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | ._B _, .«SET `{ '...' `}» => nomatch hc
    | ._B _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | ._B _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«ERROR '.' %» _, ._B _ => nomatch hc
    | .«ERROR '.' %» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«ERROR '.' %» _, .«'"' % '"'» _ => nomatch hc
    | .«ERROR '.' %» _, .D _ => nomatch hc
    | .«ERROR '.' %» _, .«% W %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% S %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«ERROR '.' %» _, .«LIST `[ % `]» _ => nomatch hc
    | .«ERROR '.' %» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«ERROR '.' %» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«ERROR '.' %» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«ERROR '.' %» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% '.' %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«ERROR '.' %» _, .REF _ => nomatch hc
    | .«ERROR '.' %» _, .DEFAULT => nomatch hc
    | .«ERROR '.' %» _, .«'{#}'» => nomatch hc
    | .«ERROR '.' %» _, .«SEQ `( % `)» _ => nomatch hc
    | .«ERROR '.' %» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«ERROR '.' %» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«ERROR '.' %» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«ERROR '.' %» _, .«SET `{ % `}» _ => nomatch hc
    | .«ERROR '.' %» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«SET `{ '...' `}» => nomatch hc
    | .«ERROR '.' %» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«ERROR '.' %» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, ._B _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«ERROR '.' %» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«'"' % '"'» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .D _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«% W %» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«% S %» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«LIST `[ % `]» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«% '.' %» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .REF _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .DEFAULT => nomatch hc
    | .«MATCH_KIND '.' %» _, .«'{#}'» => nomatch hc
    | .«MATCH_KIND '.' %» _, .«SEQ `( % `)» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«SET `{ % `}» _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«SET `{ '...' `}» => nomatch hc
    | .«MATCH_KIND '.' %» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«MATCH_KIND '.' %» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«'"' % '"'» _, ._B _ => nomatch hc
    | .«'"' % '"'» _, .«ERROR '.' %» _ => nomatch hc
    | .«'"' % '"'» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«'"' % '"'» _, .D _ => nomatch hc
    | .«'"' % '"'» _, .«% W %» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% S %» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«'"' % '"'» _, .«LIST `[ % `]» _ => nomatch hc
    | .«'"' % '"'» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«'"' % '"'» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«'"' % '"'» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«'"' % '"'» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«'"' % '"'» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«'"' % '"'» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% '.' %» _ _ => nomatch hc
    | .«'"' % '"'» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«'"' % '"'» _, .REF _ => nomatch hc
    | .«'"' % '"'» _, .DEFAULT => nomatch hc
    | .«'"' % '"'» _, .«'{#}'» => nomatch hc
    | .«'"' % '"'» _, .«SEQ `( % `)» _ => nomatch hc
    | .«'"' % '"'» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«'"' % '"'» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«'"' % '"'» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«'"' % '"'» _, .«SET `{ % `}» _ => nomatch hc
    | .«'"' % '"'» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«'"' % '"'» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«'"' % '"'» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«'"' % '"'» _, .«SET `{ '...' `}» => nomatch hc
    | .«'"' % '"'» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«'"' % '"'» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .D _, ._B _ => nomatch hc
    | .D _, .«ERROR '.' %» _ => nomatch hc
    | .D _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .D _, .«'"' % '"'» _ => nomatch hc
    | .D _, .«% W %» _ _ => nomatch hc
    | .D _, .«% S %» _ _ => nomatch hc
    | .D _, .«% '.' % V %» _ _ _ => nomatch hc
    | .D _, .«LIST `[ % `]» _ => nomatch hc
    | .D _, .«TUPLE `( % `)» _ => nomatch hc
    | .D _, .«ARRAY `[ % `]» _ => nomatch hc
    | .D _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .D _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .D _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .D _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .D _, .«% '.' %» _ _ => nomatch hc
    | .D _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .D _, .REF _ => nomatch hc
    | .D _, .DEFAULT => nomatch hc
    | .D _, .«'{#}'» => nomatch hc
    | .D _, .«SEQ `( % `)» _ => nomatch hc
    | .D _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .D _, .«RECORD `{ % `}» _ => nomatch hc
    | .D _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .D _, .«SET `{ % `}» _ => nomatch hc
    | .D _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .D _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .D _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .D _, .«SET `{ '...' `}» => nomatch hc
    | .D _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .D _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«% W %» _ _, ._B _ => nomatch hc
    | .«% W %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% W %» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«% W %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% W %» _ _, .D _ => nomatch hc
    | .«% W %» _ _, .«% S %» _ _ => nomatch hc
    | .«% W %» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«% W %» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«% W %» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«% W %» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«% W %» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«% W %» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«% W %» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«% W %» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«% W %» _ _, .«% '.' %» _ _ => nomatch hc
    | .«% W %» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«% W %» _ _, .REF _ => nomatch hc
    | .«% W %» _ _, .DEFAULT => nomatch hc
    | .«% W %» _ _, .«'{#}'» => nomatch hc
    | .«% W %» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«% W %» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«% W %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% W %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% W %» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«% W %» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«% W %» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«% W %» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«% W %» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«% W %» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«% W %» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«% S %» _ _, ._B _ => nomatch hc
    | .«% S %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% S %» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«% S %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% S %» _ _, .D _ => nomatch hc
    | .«% S %» _ _, .«% W %» _ _ => nomatch hc
    | .«% S %» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«% S %» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«% S %» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«% S %» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«% S %» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«% S %» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«% S %» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«% S %» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«% S %» _ _, .«% '.' %» _ _ => nomatch hc
    | .«% S %» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«% S %» _ _, .REF _ => nomatch hc
    | .«% S %» _ _, .DEFAULT => nomatch hc
    | .«% S %» _ _, .«'{#}'» => nomatch hc
    | .«% S %» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«% S %» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«% S %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% S %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% S %» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«% S %» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«% S %» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«% S %» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«% S %» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«% S %» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«% S %» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, ._B _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«'"' % '"'» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .D _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«% W %» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«% S %» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«% '.' %» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .REF _ => nomatch hc
    | .«% '.' % V %» _ _ _, .DEFAULT => nomatch hc
    | .«% '.' % V %» _ _ _, .«'{#}'» => nomatch hc
    | .«% '.' % V %» _ _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«SET `{ % `}» _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«SET `{ '...' `}» => nomatch hc
    | .«% '.' % V %» _ _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«% '.' % V %» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«LIST `[ % `]» _, ._B _ => nomatch hc
    | .«LIST `[ % `]» _, .«ERROR '.' %» _ => nomatch hc
    | .«LIST `[ % `]» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«LIST `[ % `]» _, .«'"' % '"'» _ => nomatch hc
    | .«LIST `[ % `]» _, .D _ => nomatch hc
    | .«LIST `[ % `]» _, .«% W %» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«% S %» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«LIST `[ % `]» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«LIST `[ % `]» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«% '.' %» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«LIST `[ % `]» _, .REF _ => nomatch hc
    | .«LIST `[ % `]» _, .DEFAULT => nomatch hc
    | .«LIST `[ % `]» _, .«'{#}'» => nomatch hc
    | .«LIST `[ % `]» _, .«SEQ `( % `)» _ => nomatch hc
    | .«LIST `[ % `]» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«LIST `[ % `]» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«LIST `[ % `]» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«LIST `[ % `]» _, .«SET `{ % `}» _ => nomatch hc
    | .«LIST `[ % `]» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«SET `{ '...' `}» => nomatch hc
    | .«LIST `[ % `]» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«LIST `[ % `]» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«TUPLE `( % `)» _, ._B _ => nomatch hc
    | .«TUPLE `( % `)» _, .«ERROR '.' %» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«'"' % '"'» _ => nomatch hc
    | .«TUPLE `( % `)» _, .D _ => nomatch hc
    | .«TUPLE `( % `)» _, .«% W %» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«% S %» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«LIST `[ % `]» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«% '.' %» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .REF _ => nomatch hc
    | .«TUPLE `( % `)» _, .DEFAULT => nomatch hc
    | .«TUPLE `( % `)» _, .«'{#}'» => nomatch hc
    | .«TUPLE `( % `)» _, .«SEQ `( % `)» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«SET `{ % `}» _ => nomatch hc
    | .«TUPLE `( % `)» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«SET `{ '...' `}» => nomatch hc
    | .«TUPLE `( % `)» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«TUPLE `( % `)» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, ._B _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«ERROR '.' %» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«'"' % '"'» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .D _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«% W %» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«% S %» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«LIST `[ % `]» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«% '.' %» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .REF _ => nomatch hc
    | .«ARRAY `[ % `]» _, .DEFAULT => nomatch hc
    | .«ARRAY `[ % `]» _, .«'{#}'» => nomatch hc
    | .«ARRAY `[ % `]» _, .«SEQ `( % `)» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«SET `{ % `}» _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«SET `{ '...' `}» => nomatch hc
    | .«ARRAY `[ % `]» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«ARRAY `[ % `]» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, ._B _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«'"' % '"'» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .D _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«% W %» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«% S %» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«% '.' %» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .REF _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .DEFAULT => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«'{#}'» => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«HEADER_STACK `[ % `( % `) `]» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, ._B _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«'"' % '"'» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .D _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«% W %» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«% S %» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«% '.' %» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .REF _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .DEFAULT => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«'{#}'» => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«STRUCT % `{ % `}» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, ._B _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«ERROR '.' %» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«'"' % '"'» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .D _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«% W %» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«% S %» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«% '.' %» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .REF _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .DEFAULT => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«'{#}'» => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«SET `{ % `}» _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«SET `{ '...' `}» => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«HEADER % `{ % ';' % `}» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, ._B _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«'"' % '"'» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .D _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«% W %» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«% S %» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«% '.' %» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .REF _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .DEFAULT => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«'{#}'» => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«HEADER_UNION % `{ % `}» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«% '.' %» _ _, ._B _ => nomatch hc
    | .«% '.' %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% '.' %» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«% '.' %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«% '.' %» _ _, .D _ => nomatch hc
    | .«% '.' %» _ _, .«% W %» _ _ => nomatch hc
    | .«% '.' %» _ _, .«% S %» _ _ => nomatch hc
    | .«% '.' %» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«% '.' %» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«% '.' %» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«% '.' %» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«% '.' %» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«% '.' %» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«% '.' %» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«% '.' %» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«% '.' %» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«% '.' %» _ _, .REF _ => nomatch hc
    | .«% '.' %» _ _, .DEFAULT => nomatch hc
    | .«% '.' %» _ _, .«'{#}'» => nomatch hc
    | .«% '.' %» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«% '.' %» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«% '.' %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% '.' %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% '.' %» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«% '.' %» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«% '.' %» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«% '.' %» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«% '.' %» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«% '.' %» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«% '.' %» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, ._B _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«ERROR '.' %» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«'"' % '"'» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .D _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«% W %» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«% S %» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«% '.' %» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .REF _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .DEFAULT => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«'{#}'» => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«SET `{ % `}» _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«SET `{ '...' `}» => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«% '.' % '.' %» _ _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .REF _, ._B _ => nomatch hc
    | .REF _, .«ERROR '.' %» _ => nomatch hc
    | .REF _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .REF _, .«'"' % '"'» _ => nomatch hc
    | .REF _, .D _ => nomatch hc
    | .REF _, .«% W %» _ _ => nomatch hc
    | .REF _, .«% S %» _ _ => nomatch hc
    | .REF _, .«% '.' % V %» _ _ _ => nomatch hc
    | .REF _, .«LIST `[ % `]» _ => nomatch hc
    | .REF _, .«TUPLE `( % `)» _ => nomatch hc
    | .REF _, .«ARRAY `[ % `]» _ => nomatch hc
    | .REF _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .REF _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .REF _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .REF _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .REF _, .«% '.' %» _ _ => nomatch hc
    | .REF _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .REF _, .DEFAULT => nomatch hc
    | .REF _, .«'{#}'» => nomatch hc
    | .REF _, .«SEQ `( % `)» _ => nomatch hc
    | .REF _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .REF _, .«RECORD `{ % `}» _ => nomatch hc
    | .REF _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .REF _, .«SET `{ % `}» _ => nomatch hc
    | .REF _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .REF _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .REF _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .REF _, .«SET `{ '...' `}» => nomatch hc
    | .REF _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .REF _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .DEFAULT, ._B _ => nomatch hc
    | .DEFAULT, .«ERROR '.' %» _ => nomatch hc
    | .DEFAULT, .«MATCH_KIND '.' %» _ => nomatch hc
    | .DEFAULT, .«'"' % '"'» _ => nomatch hc
    | .DEFAULT, .D _ => nomatch hc
    | .DEFAULT, .«% W %» _ _ => nomatch hc
    | .DEFAULT, .«% S %» _ _ => nomatch hc
    | .DEFAULT, .«% '.' % V %» _ _ _ => nomatch hc
    | .DEFAULT, .«LIST `[ % `]» _ => nomatch hc
    | .DEFAULT, .«TUPLE `( % `)» _ => nomatch hc
    | .DEFAULT, .«ARRAY `[ % `]» _ => nomatch hc
    | .DEFAULT, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .DEFAULT, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .DEFAULT, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .DEFAULT, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .DEFAULT, .«% '.' %» _ _ => nomatch hc
    | .DEFAULT, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .DEFAULT, .REF _ => nomatch hc
    | .DEFAULT, .«'{#}'» => nomatch hc
    | .DEFAULT, .«SEQ `( % `)» _ => nomatch hc
    | .DEFAULT, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .DEFAULT, .«RECORD `{ % `}» _ => nomatch hc
    | .DEFAULT, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .DEFAULT, .«SET `{ % `}» _ => nomatch hc
    | .DEFAULT, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .DEFAULT, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .DEFAULT, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .DEFAULT, .«SET `{ '...' `}» => nomatch hc
    | .DEFAULT, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .DEFAULT, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«'{#}'», ._B _ => nomatch hc
    | .«'{#}'», .«ERROR '.' %» _ => nomatch hc
    | .«'{#}'», .«MATCH_KIND '.' %» _ => nomatch hc
    | .«'{#}'», .«'"' % '"'» _ => nomatch hc
    | .«'{#}'», .D _ => nomatch hc
    | .«'{#}'», .«% W %» _ _ => nomatch hc
    | .«'{#}'», .«% S %» _ _ => nomatch hc
    | .«'{#}'», .«% '.' % V %» _ _ _ => nomatch hc
    | .«'{#}'», .«LIST `[ % `]» _ => nomatch hc
    | .«'{#}'», .«TUPLE `( % `)» _ => nomatch hc
    | .«'{#}'», .«ARRAY `[ % `]» _ => nomatch hc
    | .«'{#}'», .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«'{#}'», .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«'{#}'», .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«'{#}'», .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«'{#}'», .«% '.' %» _ _ => nomatch hc
    | .«'{#}'», .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«'{#}'», .REF _ => nomatch hc
    | .«'{#}'», .DEFAULT => nomatch hc
    | .«'{#}'», .«SEQ `( % `)» _ => nomatch hc
    | .«'{#}'», .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«'{#}'», .«RECORD `{ % `}» _ => nomatch hc
    | .«'{#}'», .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«'{#}'», .«SET `{ % `}» _ => nomatch hc
    | .«'{#}'», .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«'{#}'», .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«'{#}'», .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«'{#}'», .«SET `{ '...' `}» => nomatch hc
    | .«'{#}'», .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«'{#}'», .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SEQ `( % `)» _, ._B _ => nomatch hc
    | .«SEQ `( % `)» _, .«ERROR '.' %» _ => nomatch hc
    | .«SEQ `( % `)» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«SEQ `( % `)» _, .«'"' % '"'» _ => nomatch hc
    | .«SEQ `( % `)» _, .D _ => nomatch hc
    | .«SEQ `( % `)» _, .«% W %» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«% S %» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«LIST `[ % `]» _ => nomatch hc
    | .«SEQ `( % `)» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«SEQ `( % `)» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«SEQ `( % `)» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«% '.' %» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«SEQ `( % `)» _, .REF _ => nomatch hc
    | .«SEQ `( % `)» _, .DEFAULT => nomatch hc
    | .«SEQ `( % `)» _, .«'{#}'» => nomatch hc
    | .«SEQ `( % `)» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«SEQ `( % `)» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SEQ `( % `)» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SEQ `( % `)» _, .«SET `{ % `}» _ => nomatch hc
    | .«SEQ `( % `)» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«SET `{ '...' `}» => nomatch hc
    | .«SEQ `( % `)» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«SEQ `( % `)» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, ._B _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«ERROR '.' %» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«'"' % '"'» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .D _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«% W %» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«% S %» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«LIST `[ % `]» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«% '.' %» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .REF _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .DEFAULT => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«'{#}'» => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«SEQ `( % `)» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«SET `{ % `}» _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«SET `{ '...' `}» => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«SEQ `( % ',' '...' `)» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, ._B _ => nomatch hc
    | .«RECORD `{ % `}» _, .«ERROR '.' %» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«'"' % '"'» _ => nomatch hc
    | .«RECORD `{ % `}» _, .D _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% W %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% S %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«LIST `[ % `]» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% '.' %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .REF _ => nomatch hc
    | .«RECORD `{ % `}» _, .DEFAULT => nomatch hc
    | .«RECORD `{ % `}» _, .«'{#}'» => nomatch hc
    | .«RECORD `{ % `}» _, .«SEQ `( % `)» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SET `{ % `}» _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«SET `{ '...' `}» => nomatch hc
    | .«RECORD `{ % `}» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«RECORD `{ % `}» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, ._B _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«ERROR '.' %» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«'"' % '"'» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .D _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% W %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% S %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«LIST `[ % `]» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% '.' %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .REF _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .DEFAULT => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«'{#}'» => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SEQ `( % `)» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SET `{ % `}» _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«SET `{ '...' `}» => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«RECORD `{ % ',' '...' `}» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SET `{ % `}» _, ._B _ => nomatch hc
    | .«SET `{ % `}» _, .«ERROR '.' %» _ => nomatch hc
    | .«SET `{ % `}» _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«SET `{ % `}» _, .«'"' % '"'» _ => nomatch hc
    | .«SET `{ % `}» _, .D _ => nomatch hc
    | .«SET `{ % `}» _, .«% W %» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«% S %» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«SET `{ % `}» _, .«LIST `[ % `]» _ => nomatch hc
    | .«SET `{ % `}» _, .«TUPLE `( % `)» _ => nomatch hc
    | .«SET `{ % `}» _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«SET `{ % `}» _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«SET `{ % `}» _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«% '.' %» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«SET `{ % `}» _, .REF _ => nomatch hc
    | .«SET `{ % `}» _, .DEFAULT => nomatch hc
    | .«SET `{ % `}» _, .«'{#}'» => nomatch hc
    | .«SET `{ % `}» _, .«SEQ `( % `)» _ => nomatch hc
    | .«SET `{ % `}» _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«SET `{ % `}» _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SET `{ % `}» _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SET `{ % `}» _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«SET `{ '...' `}» => nomatch hc
    | .«SET `{ % `}» _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«SET `{ % `}» _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, ._B _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«'"' % '"'» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .D _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«% W %» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«% S %» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«% '.' %» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .REF _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .DEFAULT => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«'{#}'» => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«SET `{ % `( % `) `}» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, ._B _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«'"' % '"'» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .D _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«% W %» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«% S %» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«% '.' %» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .REF _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .DEFAULT => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«'{#}'» => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«SET `{ % '&&&' % `}» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, ._B _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«'"' % '"'» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .D _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«% W %» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«% S %» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«% '.' %» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .REF _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .DEFAULT => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«'{#}'» => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«SET `{ % '..' % `}» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«SET `{ '...' `}», ._B _ => nomatch hc
    | .«SET `{ '...' `}», .«ERROR '.' %» _ => nomatch hc
    | .«SET `{ '...' `}», .«MATCH_KIND '.' %» _ => nomatch hc
    | .«SET `{ '...' `}», .«'"' % '"'» _ => nomatch hc
    | .«SET `{ '...' `}», .D _ => nomatch hc
    | .«SET `{ '...' `}», .«% W %» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«% S %» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«% '.' % V %» _ _ _ => nomatch hc
    | .«SET `{ '...' `}», .«LIST `[ % `]» _ => nomatch hc
    | .«SET `{ '...' `}», .«TUPLE `( % `)» _ => nomatch hc
    | .«SET `{ '...' `}», .«ARRAY `[ % `]» _ => nomatch hc
    | .«SET `{ '...' `}», .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«SET `{ '...' `}», .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«% '.' %» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«SET `{ '...' `}», .REF _ => nomatch hc
    | .«SET `{ '...' `}», .DEFAULT => nomatch hc
    | .«SET `{ '...' `}», .«'{#}'» => nomatch hc
    | .«SET `{ '...' `}», .«SEQ `( % `)» _ => nomatch hc
    | .«SET `{ '...' `}», .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«SET `{ '...' `}», .«RECORD `{ % `}» _ => nomatch hc
    | .«SET `{ '...' `}», .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«SET `{ '...' `}», .«SET `{ % `}» _ => nomatch hc
    | .«SET `{ '...' `}», .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«TABLE_ENUM % '.' %» _ _ => nomatch hc
    | .«SET `{ '...' `}», .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, ._B _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«ERROR '.' %» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«'"' % '"'» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .D _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«% W %» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«% S %» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«% '.' %» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .REF _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .DEFAULT => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«'{#}'» => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«SET `{ % `}» _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«SET `{ '...' `}» => nomatch hc
    | .«TABLE_ENUM % '.' %» _ _, .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, ._B _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«ERROR '.' %» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«MATCH_KIND '.' %» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«'"' % '"'» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .D _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«% W %» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«% S %» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«% '.' % V %» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«LIST `[ % `]» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«TUPLE `( % `)» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«ARRAY `[ % `]» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«HEADER_STACK `[ % `( % `) `]» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«STRUCT % `{ % `}» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«HEADER % `{ % ';' % `}» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«HEADER_UNION % `{ % `}» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«% '.' %» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«% '.' % '.' %» _ _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .REF _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .DEFAULT => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«'{#}'» => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SEQ `( % `)» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SEQ `( % ',' '...' `)» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«RECORD `{ % `}» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«RECORD `{ % ',' '...' `}» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SET `{ % `}» _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SET `{ % `( % `) `}» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SET `{ % '&&&' % `}» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SET `{ % '..' % `}» _ _ => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«SET `{ '...' `}» => nomatch hc
    | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _, .«TABLE_ENUM % '.' %» _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_shape_87ed6afdba0f (a b : (_root_.List value)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_value x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_87ed6afdba0f x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_shape_2b5100be8236 (a b : (_root_.List fieldValue)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_fieldValue x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_2b5100be8236 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

end

instance : _root_.DecidableEq fieldValue := decEq_fieldValue

instance : _root_.DecidableEq value := decEq_value


inductive listValue : Type where
  | «LIST `[ % `]» : (_root_.List value) → listValue
deriving _root_.DecidableEq


inductive tupleValue : Type where
  | «TUPLE `( % `)» : (_root_.List value) → tupleValue
deriving _root_.DecidableEq


inductive arrayValue : Type where
  | «ARRAY `[ % `]» : (_root_.List value) → arrayValue
deriving _root_.DecidableEq


inductive headerStackValue : Type where
  | «HEADER_STACK `[ % `( % `) `]» : (_root_.List value) → _root_.Nat → headerStackValue
deriving _root_.DecidableEq


inductive structValue : Type where
  | «STRUCT % `{ % `}» : typeId → (_root_.List fieldValue) → structValue
deriving _root_.DecidableEq


inductive headerValue : Type where
  | «HEADER % `{ % ';' % `}» : typeId → _root_.Bool → (_root_.List fieldValue) → headerValue
deriving _root_.DecidableEq


inductive headerUnionValue : Type where
  | «HEADER_UNION % `{ % `}» : typeId → (_root_.List fieldValue) → headerUnionValue
deriving _root_.DecidableEq


inductive enumValue : Type where
  | «% '.' %» : typeId → nameIR → enumValue
  | «% '.' % '.' %» : typeId → nameIR → value → enumValue
deriving _root_.DecidableEq


inductive dataValue : Type where
  | «LIST `[ % `]» : (_root_.List value) → dataValue
  | «TUPLE `( % `)» : (_root_.List value) → dataValue
  | «ARRAY `[ % `]» : (_root_.List value) → dataValue
  | «HEADER_STACK `[ % `( % `) `]» : (_root_.List value) → _root_.Nat → dataValue
  | «STRUCT % `{ % `}» : typeId → (_root_.List fieldValue) → dataValue
  | «HEADER % `{ % ';' % `}» : typeId → _root_.Bool → (_root_.List fieldValue) → dataValue
  | «HEADER_UNION % `{ % `}» : typeId → (_root_.List fieldValue) → dataValue
  | «% '.' %» : typeId → nameIR → dataValue
  | «% '.' % '.' %» : typeId → nameIR → value → dataValue
deriving _root_.DecidableEq

end SpecTec
