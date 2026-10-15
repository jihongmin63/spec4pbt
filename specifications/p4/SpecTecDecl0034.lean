import SpecTecDecl0033

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$typedExpressionIR_as_typedLvalueIR:case_6:downcast:0» (arg0 : expressionIR) : (_root_.Option parenthesizedExpressionIR) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpressionIR.«`( % `)» field0) | _ => none


abbrev emptyStatementIR : Type := emptyStatement


inductive assignmentStatementIR : Type where
  | «% % % ';'» : typedLvalueIR → assignop → typedExpressionIR → assignmentStatementIR
deriving _root_.DecidableEq


inductive callStatementIR : Type where
  | «% `< % `> `( % `) ';'» : callableTargetIR → typeArgumentListIR → argumentListIR → callStatementIR
deriving _root_.DecidableEq


inductive directApplicationStatementIR : Type where
  | «% '.' APPLY `( % `) ';'» : constructorTargetIR → argumentListIR → directApplicationStatementIR
deriving _root_.DecidableEq


inductive returnStatementIR : Type where
  | «RETURN ';'» : returnStatementIR
  | «RETURN % ';'» : typedExpressionIR → returnStatementIR
deriving _root_.DecidableEq


abbrev exitStatementIR : Type := exitStatement


inductive forUpdateStatementIR : Type where
  | «% `< % `> `( % `)» : callableTargetIR → typeArgumentListIR → argumentListIR → forUpdateStatementIR
  | «% % %» : typedLvalueIR → assignop → typedExpressionIR → forUpdateStatementIR
deriving _root_.DecidableEq


abbrev forUpdateStatementListIR : Type := (_root_.List forUpdateStatementIR)


inductive forCollectionExpressionIR : Type where
  | «% '#' %» : expressionIR → expressionNoteIR → forCollectionExpressionIR
  | «% '..' %» : typedExpressionIR → typedExpressionIR → forCollectionExpressionIR
deriving _root_.DecidableEq


inductive switchLabelIR : Type where
  | DEFAULT : switchLabelIR
  | «% '#' %» : expressionIR → expressionNoteIR → switchLabelIR
deriving _root_.DecidableEq


abbrev breakStatementIR : Type := breakStatement


abbrev continueStatementIR : Type := continueStatement


inductive constantDeclarationIR : Type where
  | «% CONST % % % ';'» : annotationList → typeIR → nameIR → constantInitializerIR → constantDeclarationIR
deriving _root_.DecidableEq


abbrev initializerOptIR : Type := (_root_.Option initializerIR)


inductive forInitStatementIR : Type where
  | «% % % %» : annotationList → typeIR → nameIR → initializerOptIR → forInitStatementIR
  | «% `< % `> `( % `)» : callableTargetIR → typeArgumentListIR → argumentListIR → forInitStatementIR
  | «% % %» : typedLvalueIR → assignop → typedExpressionIR → forInitStatementIR
deriving _root_.DecidableEq


abbrev forInitStatementListIR : Type := (_root_.List forInitStatementIR)


mutual

inductive blockStatementIR : Type where
  | «% `{ % `}» : annotationList → (_root_.List blockElementStatementIR) → blockStatementIR

inductive switchCaseIR : Type where
  | «% ':' %» : switchLabelIR → blockStatementIR → switchCaseIR
  | «% ':'» : switchLabelIR → switchCaseIR

inductive statementIR : Type where
  | «';'» : statementIR
  | «% % % ';'» : typedLvalueIR → assignop → typedExpressionIR → statementIR
  | «% `< % `> `( % `) ';'» : callableTargetIR → typeArgumentListIR → argumentListIR → statementIR
  | «% '.' APPLY `( % `) ';'» : constructorTargetIR → argumentListIR → statementIR
  | «RETURN ';'» : statementIR
  | «RETURN % ';'» : typedExpressionIR → statementIR
  | «EXIT ';'» : statementIR
  | «% `{ % `}» : annotationList → (_root_.List blockElementStatementIR) → statementIR
  | «IF `( % `) %» : typedExpressionIR → statementIR → statementIR
  | «IF `( % `) % ELSE %» : typedExpressionIR → statementIR → statementIR → statementIR
  | «% FOR `( % ';' % ';' % `) %» : annotationList → forInitStatementListIR → typedExpressionIR → forUpdateStatementListIR → statementIR → statementIR
  | «% FOR `( % % IN % `) %» : annotationList → typeIR → nameIR → forCollectionExpressionIR → statementIR → statementIR
  | «% FOR `( % % % IN % `) %» : annotationList → annotationList → typeIR → nameIR → forCollectionExpressionIR → statementIR → statementIR
  | «BREAK ';'» : statementIR
  | «CONTINUE ';'» : statementIR
  | «SWITCH `( % `) `{ % `}» : typedExpressionIR → (_root_.List switchCaseIR) → statementIR

inductive blockElementStatementIR : Type where
  | «% CONST % % % ';'» : annotationList → typeIR → nameIR → constantInitializerIR → blockElementStatementIR
  | «% % % % ';'» : annotationList → typeIR → nameIR → initializerOptIR → blockElementStatementIR
  | «';'» : blockElementStatementIR
  | «% % % ';'» : typedLvalueIR → assignop → typedExpressionIR → blockElementStatementIR
  | «% `< % `> `( % `) ';'» : callableTargetIR → typeArgumentListIR → argumentListIR → blockElementStatementIR
  | «% '.' APPLY `( % `) ';'» : constructorTargetIR → argumentListIR → blockElementStatementIR
  | «RETURN ';'» : blockElementStatementIR
  | «RETURN % ';'» : typedExpressionIR → blockElementStatementIR
  | «EXIT ';'» : blockElementStatementIR
  | «% `{ % `}» : annotationList → (_root_.List blockElementStatementIR) → blockElementStatementIR
  | «IF `( % `) %» : typedExpressionIR → statementIR → blockElementStatementIR
  | «IF `( % `) % ELSE %» : typedExpressionIR → statementIR → statementIR → blockElementStatementIR
  | «% FOR `( % ';' % ';' % `) %» : annotationList → forInitStatementListIR → typedExpressionIR → forUpdateStatementListIR → statementIR → blockElementStatementIR
  | «% FOR `( % % IN % `) %» : annotationList → typeIR → nameIR → forCollectionExpressionIR → statementIR → blockElementStatementIR
  | «% FOR `( % % % IN % `) %» : annotationList → annotationList → typeIR → nameIR → forCollectionExpressionIR → statementIR → blockElementStatementIR
  | «BREAK ';'» : blockElementStatementIR
  | «CONTINUE ';'» : blockElementStatementIR
  | «SWITCH `( % `) `{ % `}» : typedExpressionIR → (_root_.List switchCaseIR) → blockElementStatementIR

end


mutual

def decEq_blockStatementIR (a b : blockStatementIR) : _root_.Decidable (a = b) :=
  match a, b with
    | .«% `{ % `}» x0 x1, .«% `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_b77b8ff6a165 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_shape_b77b8ff6a165 (a b : (_root_.List blockElementStatementIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_blockElementStatementIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_b77b8ff6a165 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_blockElementStatementIR (a b : blockElementStatementIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .«% CONST % % % ';'» x0 x1 x2 x3, .«% CONST % % % ';'» y0 y1 y2 y3 =>
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
    | .«% % % % ';'» x0 x1 x2 x3, .«% % % % ';'» y0 y1 y2 y3 =>
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
    | .«';'», .«';'» =>
      _root_.Decidable.isTrue rfl
    | .«% % % ';'» x0 x1 x2, .«% % % ';'» y0 y1 y2 =>
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
    | .«% `< % `> `( % `) ';'» x0 x1 x2, .«% `< % `> `( % `) ';'» y0 y1 y2 =>
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
    | .«% '.' APPLY `( % `) ';'» x0 x1, .«% '.' APPLY `( % `) ';'» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«RETURN ';'», .«RETURN ';'» =>
      _root_.Decidable.isTrue rfl
    | .«RETURN % ';'» x0, .«RETURN % ';'» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«EXIT ';'», .«EXIT ';'» =>
      _root_.Decidable.isTrue rfl
    | .«% `{ % `}» x0 x1, .«% `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_b77b8ff6a165 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«IF `( % `) %» x0 x1, .«IF `( % `) %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_statementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«IF `( % `) % ELSE %» x0 x1 x2, .«IF `( % `) % ELSE %» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_statementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_statementIR x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% FOR `( % ';' % ';' % `) %» x0 x1 x2 x3 x4, .«% FOR `( % ';' % ';' % `) %» y0 y1 y2 y3 y4 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match decEq_statementIR x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; rfl)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% FOR `( % % IN % `) %» x0 x1 x2 x3 x4, .«% FOR `( % % IN % `) %» y0 y1 y2 y3 y4 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match decEq_statementIR x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; rfl)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% FOR `( % % % IN % `) %» x0 x1 x2 x3 x4 x5, .«% FOR `( % % % IN % `) %» y0 y1 y2 y3 y4 y5 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match _root_.decEq x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                match decEq_statementIR x5 y5 with
                | _root_.Decidable.isTrue h5 =>
                  _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; cases h5; rfl)
                | _root_.Decidable.isFalse h5 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«BREAK ';'», .«BREAK ';'» =>
      _root_.Decidable.isTrue rfl
    | .«CONTINUE ';'», .«CONTINUE ';'» =>
      _root_.Decidable.isTrue rfl
    | .«SWITCH `( % `) `{ % `}» x0 x1, .«SWITCH `( % `) `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_6821c8fdded7 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% CONST % % % ';'» _ _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«';'» => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«RETURN ';'» => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«EXIT ';'» => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«BREAK ';'» => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«';'» => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«RETURN ';'» => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«EXIT ';'» => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«BREAK ';'» => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«';'», .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«';'», .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«';'», .«RETURN ';'» => nomatch hc
    | .«';'», .«RETURN % ';'» _ => nomatch hc
    | .«';'», .«EXIT ';'» => nomatch hc
    | .«';'», .«% `{ % `}» _ _ => nomatch hc
    | .«';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«';'», .«BREAK ';'» => nomatch hc
    | .«';'», .«CONTINUE ';'» => nomatch hc
    | .«';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«RETURN ';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% % % ';'» _ _ _, .«EXIT ';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«BREAK ';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«RETURN ';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«EXIT ';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«BREAK ';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«RETURN ';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«EXIT ';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«BREAK ';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«CONTINUE ';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«RETURN ';'», .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«RETURN ';'», .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«RETURN ';'», .«';'» => nomatch hc
    | .«RETURN ';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«RETURN ';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«RETURN ';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«RETURN ';'», .«RETURN % ';'» _ => nomatch hc
    | .«RETURN ';'», .«EXIT ';'» => nomatch hc
    | .«RETURN ';'», .«% `{ % `}» _ _ => nomatch hc
    | .«RETURN ';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«RETURN ';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«RETURN ';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«RETURN ';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«RETURN ';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«RETURN ';'», .«BREAK ';'» => nomatch hc
    | .«RETURN ';'», .«CONTINUE ';'» => nomatch hc
    | .«RETURN ';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«';'» => nomatch hc
    | .«RETURN % ';'» _, .«% % % ';'» _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«RETURN % ';'» _, .«RETURN ';'» => nomatch hc
    | .«RETURN % ';'» _, .«EXIT ';'» => nomatch hc
    | .«RETURN % ';'» _, .«% `{ % `}» _ _ => nomatch hc
    | .«RETURN % ';'» _, .«IF `( % `) %» _ _ => nomatch hc
    | .«RETURN % ';'» _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«BREAK ';'» => nomatch hc
    | .«RETURN % ';'» _, .«CONTINUE ';'» => nomatch hc
    | .«RETURN % ';'» _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«EXIT ';'», .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«EXIT ';'», .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«EXIT ';'», .«';'» => nomatch hc
    | .«EXIT ';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«EXIT ';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«EXIT ';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«EXIT ';'», .«RETURN ';'» => nomatch hc
    | .«EXIT ';'», .«RETURN % ';'» _ => nomatch hc
    | .«EXIT ';'», .«% `{ % `}» _ _ => nomatch hc
    | .«EXIT ';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«EXIT ';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«EXIT ';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«EXIT ';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«EXIT ';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«EXIT ';'», .«BREAK ';'» => nomatch hc
    | .«EXIT ';'», .«CONTINUE ';'» => nomatch hc
    | .«EXIT ';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«';'» => nomatch hc
    | .«% `{ % `}» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«RETURN ';'» => nomatch hc
    | .«% `{ % `}» _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% `{ % `}» _ _, .«EXIT ';'» => nomatch hc
    | .«% `{ % `}» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«BREAK ';'» => nomatch hc
    | .«% `{ % `}» _ _, .«CONTINUE ';'» => nomatch hc
    | .«% `{ % `}» _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«RETURN ';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«RETURN % ';'» _ => nomatch hc
    | .«IF `( % `) %» _ _, .«EXIT ';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«BREAK ';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«CONTINUE ';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«RETURN ';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«EXIT ';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«BREAK ';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«RETURN ';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«EXIT ';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«BREAK ';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«RETURN ';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«EXIT ';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«BREAK ';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«RETURN ';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«EXIT ';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«BREAK ';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«BREAK ';'», .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«BREAK ';'», .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«BREAK ';'», .«';'» => nomatch hc
    | .«BREAK ';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«BREAK ';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«BREAK ';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«BREAK ';'», .«RETURN ';'» => nomatch hc
    | .«BREAK ';'», .«RETURN % ';'» _ => nomatch hc
    | .«BREAK ';'», .«EXIT ';'» => nomatch hc
    | .«BREAK ';'», .«% `{ % `}» _ _ => nomatch hc
    | .«BREAK ';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«BREAK ';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«BREAK ';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«BREAK ';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«BREAK ';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«BREAK ';'», .«CONTINUE ';'» => nomatch hc
    | .«BREAK ';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«CONTINUE ';'», .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«';'» => nomatch hc
    | .«CONTINUE ';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«CONTINUE ';'», .«RETURN ';'» => nomatch hc
    | .«CONTINUE ';'», .«RETURN % ';'» _ => nomatch hc
    | .«CONTINUE ';'», .«EXIT ';'» => nomatch hc
    | .«CONTINUE ';'», .«% `{ % `}» _ _ => nomatch hc
    | .«CONTINUE ';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«CONTINUE ';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«BREAK ';'» => nomatch hc
    | .«CONTINUE ';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«';'» => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«RETURN ';'» => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«RETURN % ';'» _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«EXIT ';'» => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«BREAK ';'» => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«CONTINUE ';'» => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_statementIR (a b : statementIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .«';'», .«';'» =>
      _root_.Decidable.isTrue rfl
    | .«% % % ';'» x0 x1 x2, .«% % % ';'» y0 y1 y2 =>
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
    | .«% `< % `> `( % `) ';'» x0 x1 x2, .«% `< % `> `( % `) ';'» y0 y1 y2 =>
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
    | .«% '.' APPLY `( % `) ';'» x0 x1, .«% '.' APPLY `( % `) ';'» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«RETURN ';'», .«RETURN ';'» =>
      _root_.Decidable.isTrue rfl
    | .«RETURN % ';'» x0, .«RETURN % ';'» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«EXIT ';'», .«EXIT ';'» =>
      _root_.Decidable.isTrue rfl
    | .«% `{ % `}» x0 x1, .«% `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_b77b8ff6a165 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«IF `( % `) %» x0 x1, .«IF `( % `) %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_statementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«IF `( % `) % ELSE %» x0 x1 x2, .«IF `( % `) % ELSE %» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_statementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_statementIR x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% FOR `( % ';' % ';' % `) %» x0 x1 x2 x3 x4, .«% FOR `( % ';' % ';' % `) %» y0 y1 y2 y3 y4 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match decEq_statementIR x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; rfl)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% FOR `( % % IN % `) %» x0 x1 x2 x3 x4, .«% FOR `( % % IN % `) %» y0 y1 y2 y3 y4 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match decEq_statementIR x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; rfl)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% FOR `( % % % IN % `) %» x0 x1 x2 x3 x4 x5, .«% FOR `( % % % IN % `) %» y0 y1 y2 y3 y4 y5 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match _root_.decEq x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                match decEq_statementIR x5 y5 with
                | _root_.Decidable.isTrue h5 =>
                  _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; cases h5; rfl)
                | _root_.Decidable.isFalse h5 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«BREAK ';'», .«BREAK ';'» =>
      _root_.Decidable.isTrue rfl
    | .«CONTINUE ';'», .«CONTINUE ';'» =>
      _root_.Decidable.isTrue rfl
    | .«SWITCH `( % `) `{ % `}» x0 x1, .«SWITCH `( % `) `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_6821c8fdded7 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«';'», .«RETURN ';'» => nomatch hc
    | .«';'», .«RETURN % ';'» _ => nomatch hc
    | .«';'», .«EXIT ';'» => nomatch hc
    | .«';'», .«% `{ % `}» _ _ => nomatch hc
    | .«';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«';'», .«BREAK ';'» => nomatch hc
    | .«';'», .«CONTINUE ';'» => nomatch hc
    | .«';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«RETURN ';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% % % ';'» _ _ _, .«EXIT ';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«BREAK ';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«RETURN ';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«EXIT ';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«BREAK ';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«RETURN ';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«EXIT ';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«BREAK ';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«CONTINUE ';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«RETURN ';'», .«';'» => nomatch hc
    | .«RETURN ';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«RETURN ';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«RETURN ';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«RETURN ';'», .«RETURN % ';'» _ => nomatch hc
    | .«RETURN ';'», .«EXIT ';'» => nomatch hc
    | .«RETURN ';'», .«% `{ % `}» _ _ => nomatch hc
    | .«RETURN ';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«RETURN ';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«RETURN ';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«RETURN ';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«RETURN ';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«RETURN ';'», .«BREAK ';'» => nomatch hc
    | .«RETURN ';'», .«CONTINUE ';'» => nomatch hc
    | .«RETURN ';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«RETURN % ';'» _, .«';'» => nomatch hc
    | .«RETURN % ';'» _, .«% % % ';'» _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«RETURN % ';'» _, .«RETURN ';'» => nomatch hc
    | .«RETURN % ';'» _, .«EXIT ';'» => nomatch hc
    | .«RETURN % ';'» _, .«% `{ % `}» _ _ => nomatch hc
    | .«RETURN % ';'» _, .«IF `( % `) %» _ _ => nomatch hc
    | .«RETURN % ';'» _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«RETURN % ';'» _, .«BREAK ';'» => nomatch hc
    | .«RETURN % ';'» _, .«CONTINUE ';'» => nomatch hc
    | .«RETURN % ';'» _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«EXIT ';'», .«';'» => nomatch hc
    | .«EXIT ';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«EXIT ';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«EXIT ';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«EXIT ';'», .«RETURN ';'» => nomatch hc
    | .«EXIT ';'», .«RETURN % ';'» _ => nomatch hc
    | .«EXIT ';'», .«% `{ % `}» _ _ => nomatch hc
    | .«EXIT ';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«EXIT ';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«EXIT ';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«EXIT ';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«EXIT ';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«EXIT ';'», .«BREAK ';'» => nomatch hc
    | .«EXIT ';'», .«CONTINUE ';'» => nomatch hc
    | .«EXIT ';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«';'» => nomatch hc
    | .«% `{ % `}» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«RETURN ';'» => nomatch hc
    | .«% `{ % `}» _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% `{ % `}» _ _, .«EXIT ';'» => nomatch hc
    | .«% `{ % `}» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«BREAK ';'» => nomatch hc
    | .«% `{ % `}» _ _, .«CONTINUE ';'» => nomatch hc
    | .«% `{ % `}» _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«RETURN ';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«RETURN % ';'» _ => nomatch hc
    | .«IF `( % `) %» _ _, .«EXIT ';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«BREAK ';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«CONTINUE ';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«RETURN ';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«EXIT ';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«BREAK ';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«RETURN ';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«EXIT ';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«BREAK ';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«RETURN ';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«EXIT ';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«BREAK ';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% FOR `( % % IN % `) %» _ _ _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«RETURN ';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«RETURN % ';'» _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«EXIT ';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«BREAK ';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«CONTINUE ';'» => nomatch hc
    | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _, .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«BREAK ';'», .«';'» => nomatch hc
    | .«BREAK ';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«BREAK ';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«BREAK ';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«BREAK ';'», .«RETURN ';'» => nomatch hc
    | .«BREAK ';'», .«RETURN % ';'» _ => nomatch hc
    | .«BREAK ';'», .«EXIT ';'» => nomatch hc
    | .«BREAK ';'», .«% `{ % `}» _ _ => nomatch hc
    | .«BREAK ';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«BREAK ';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«BREAK ';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«BREAK ';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«BREAK ';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«BREAK ';'», .«CONTINUE ';'» => nomatch hc
    | .«BREAK ';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«CONTINUE ';'», .«';'» => nomatch hc
    | .«CONTINUE ';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«CONTINUE ';'», .«RETURN ';'» => nomatch hc
    | .«CONTINUE ';'», .«RETURN % ';'» _ => nomatch hc
    | .«CONTINUE ';'», .«EXIT ';'» => nomatch hc
    | .«CONTINUE ';'», .«% `{ % `}» _ _ => nomatch hc
    | .«CONTINUE ';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«CONTINUE ';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«CONTINUE ';'», .«BREAK ';'» => nomatch hc
    | .«CONTINUE ';'», .«SWITCH `( % `) `{ % `}» _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«';'» => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«RETURN ';'» => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«RETURN % ';'» _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«EXIT ';'» => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% FOR `( % % IN % `) %» _ _ _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«BREAK ';'» => nomatch hc
    | .«SWITCH `( % `) `{ % `}» _ _, .«CONTINUE ';'» => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_shape_6821c8fdded7 (a b : (_root_.List switchCaseIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_switchCaseIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_6821c8fdded7 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_switchCaseIR (a b : switchCaseIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .«% ':' %» x0 x1, .«% ':' %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_blockStatementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% ':'» x0, .«% ':'» y0 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% ':' %» _ _, .«% ':'» _ => nomatch hc
    | .«% ':'» _, .«% ':' %» _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

end

instance : _root_.DecidableEq blockStatementIR := decEq_blockStatementIR

instance : _root_.DecidableEq switchCaseIR := decEq_switchCaseIR

instance : _root_.DecidableEq statementIR := decEq_statementIR

instance : _root_.DecidableEq blockElementStatementIR := decEq_blockElementStatementIR


abbrev switchCaseListIR : Type := (_root_.List switchCaseIR)


abbrev blockElementStatementListIR : Type := (_root_.List blockElementStatementIR)


inductive conditionalStatementIR : Type where
  | «IF `( % `) %» : typedExpressionIR → statementIR → conditionalStatementIR
  | «IF `( % `) % ELSE %» : typedExpressionIR → statementIR → statementIR → conditionalStatementIR
deriving _root_.DecidableEq


inductive forStatementIR : Type where
  | «% FOR `( % ';' % ';' % `) %» : annotationList → forInitStatementListIR → typedExpressionIR → forUpdateStatementListIR → statementIR → forStatementIR
  | «% FOR `( % % IN % `) %» : annotationList → typeIR → nameIR → forCollectionExpressionIR → statementIR → forStatementIR
  | «% FOR `( % % % IN % `) %» : annotationList → annotationList → typeIR → nameIR → forCollectionExpressionIR → statementIR → forStatementIR
deriving _root_.DecidableEq


inductive switchStatementIR : Type where
  | «SWITCH `( % `) `{ % `}» : typedExpressionIR → switchCaseListIR → switchStatementIR
deriving _root_.DecidableEq


inductive variableDeclarationIR : Type where
  | «% % % % ';'» : annotationList → typeIR → nameIR → initializerOptIR → variableDeclarationIR
deriving _root_.DecidableEq


inductive functionPrototypeIR : Type where
  | «% % `< % ',' % `> `( % `)» : typeIR → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → functionPrototypeIR
deriving _root_.DecidableEq


inductive functionDeclarationIR : Type where
  | «% % %» : annotationList → functionPrototypeIR → blockStatementIR → functionDeclarationIR
deriving _root_.DecidableEq


inductive actionDeclarationIR : Type where
  | «% ACTION % `( % `) %» : annotationList → nameIR → parameterListIR → blockStatementIR → actionDeclarationIR
deriving _root_.DecidableEq


mutual

inductive objectInitializerIR : Type where
  | «'=' `{ % `}» : (_root_.List objectDeclarationIR) → objectInitializerIR

inductive objectDeclarationIR : Type where
  | «% % %» : annotationList → functionPrototypeIR → blockStatementIR → objectDeclarationIR
  | «% % % `( % `) % % ';'» : annotationList → typeIR → constructorTargetIR → argumentListIR → nameIR → (_root_.Option objectInitializerIR) → objectDeclarationIR

end


mutual

def decEq_objectInitializerIR (a b : objectInitializerIR) : _root_.Decidable (a = b) :=
  match a, b with
    | .«'=' `{ % `}» x0, .«'=' `{ % `}» y0 =>
      match decEq_shape_c360a1210979 x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        _root_.Decidable.isTrue (by cases h0; rfl)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
termination_by structural a

def decEq_shape_c360a1210979 (a b : (_root_.List objectDeclarationIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_objectDeclarationIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_c360a1210979 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_objectDeclarationIR (a b : objectDeclarationIR) : _root_.Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b with
    | .«% % %» x0 x1 x2, .«% % %» y0 y1 y2 =>
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
    | .«% % % `( % `) % % ';'» x0 x1 x2 x3 x4 x5, .«% % % `( % `) % % ';'» y0 y1 y2 y3 y4 y5 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match _root_.decEq x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match _root_.decEq x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            match _root_.decEq x3 y3 with
            | _root_.Decidable.isTrue h3 =>
              match _root_.decEq x4 y4 with
              | _root_.Decidable.isTrue h4 =>
                match decEq_shape_076e95a0b0bc x5 y5 with
                | _root_.Decidable.isTrue h5 =>
                  _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; cases h3; cases h4; cases h5; rfl)
                | _root_.Decidable.isFalse h5 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
              | _root_.Decidable.isFalse h4 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
            | _root_.Decidable.isFalse h3 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% % %» _ _ _, .«% % % `( % `) % % ';'» _ _ _ _ _ _ => nomatch hc
    | .«% % % `( % `) % % ';'» _ _ _ _ _ _, .«% % %» _ _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_shape_076e95a0b0bc (a b : (_root_.Option objectInitializerIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | _root_.Option.none, _root_.Option.none => _root_.Decidable.isTrue rfl
  | _root_.Option.some x0, _root_.Option.some y0 =>
    match decEq_objectInitializerIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      _root_.Decidable.isTrue (by cases h0; rfl)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | _root_.Option.none, _root_.Option.some _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _root_.Option.some _, _root_.Option.none => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

end

instance : _root_.DecidableEq objectInitializerIR := decEq_objectInitializerIR

instance : _root_.DecidableEq objectDeclarationIR := decEq_objectDeclarationIR


abbrev objectInitializerOptIR : Type := (_root_.Option objectInitializerIR)


abbrev objectDeclarationListIR : Type := (_root_.List objectDeclarationIR)

end SpecTec
