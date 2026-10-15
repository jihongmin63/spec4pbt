import SpecTecDecl0034

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive instantiationIR : Type where
  | «% % % `( % `) % % ';'» : annotationList → typeIR → constructorTargetIR → argumentListIR → nameIR → objectInitializerOptIR → instantiationIR
deriving _root_.DecidableEq


inductive errorDeclarationIR : Type where
  | «ERROR `{ % `}» : nameListIR → errorDeclarationIR
deriving _root_.DecidableEq


inductive matchKindDeclarationIR : Type where
  | «MATCH_KIND `{ % `}» : nameListIR → matchKindDeclarationIR
deriving _root_.DecidableEq


inductive enumTypeDeclarationIR : Type where
  | «% ENUM % `{ % `}» : annotationList → nameIR → nameListIR → enumTypeDeclarationIR
  | «% ENUM % % `{ % `}» : annotationList → typeIR → nameIR → namedValueListIR → enumTypeDeclarationIR
deriving _root_.DecidableEq


inductive typeFieldIR : Type where
  | «% % % ';'» : annotationList → typeIR → nameIR → typeFieldIR
deriving _root_.DecidableEq


abbrev typeFieldListIR : Type := (_root_.List typeFieldIR)


inductive structTypeDeclarationIR : Type where
  | «% STRUCT % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → structTypeDeclarationIR
deriving _root_.DecidableEq


inductive headerTypeDeclarationIR : Type where
  | «% HEADER % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → headerTypeDeclarationIR
deriving _root_.DecidableEq


inductive headerUnionTypeDeclarationIR : Type where
  | «% HEADER_UNION % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → headerUnionTypeDeclarationIR
deriving _root_.DecidableEq


inductive derivedTypeDeclarationIR : Type where
  | «% ENUM % `{ % `}» : annotationList → nameIR → nameListIR → derivedTypeDeclarationIR
  | «% ENUM % % `{ % `}» : annotationList → typeIR → nameIR → namedValueListIR → derivedTypeDeclarationIR
  | «% STRUCT % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → derivedTypeDeclarationIR
  | «% HEADER % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → derivedTypeDeclarationIR
  | «% HEADER_UNION % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → derivedTypeDeclarationIR
deriving _root_.DecidableEq


inductive typedefIR : Type where
  | VOID : typedefIR
  | BOOL : typedefIR
  | ERROR : typedefIR
  | MATCH_KIND : typedefIR
  | STRING : typedefIR
  | INT : typedefIR
  | «INT `< % `>» : _root_.Nat → typedefIR
  | «BIT `< % `>» : _root_.Nat → typedefIR
  | «VARBIT `< % `>» : _root_.Nat → typedefIR
  | _NAME : typeId → typedefIR
  | TYPEDEF : typeId → typeIR → typedefIR
  | TYPE : typeId → typeIR → typedefIR
  | «LIST `< % `>» : typeIR → typedefIR
  | «TUPLE `< % `>» : (_root_.List typeIR) → typedefIR
  | «ARRAY % `[ % `]» : typeIR → _root_.Nat → typedefIR
  | «HEADER_STACK % `[ % `]» : typeIR → _root_.Nat → typedefIR
  | «STRUCT % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → typedefIR
  | «HEADER % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → typedefIR
  | «HEADER_UNION % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → typedefIR
  | «ENUM % `{ % `}» : typeId → (_root_.List nameIR) → typedefIR
  | «ENUM % `< % `> `{ % `}» : typeId → typeIR → (_root_.List valueFieldIR) → typedefIR
  | «EXTERN % `< % `> %» : typeId → (_root_.List typeArgumentIR) → externMethodTypeDefEnv → typedefIR
  | «PARSER % `< % `> `( % `)» : typeId → (_root_.List typeArgumentIR) → (_root_.List parameterIR) → typedefIR
  | «CONTROL % `< % `> `( % `)» : typeId → (_root_.List typeArgumentIR) → (_root_.List parameterIR) → typedefIR
  | «PACKAGE % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List typeIR) → typedefIR
  | «TABLE % `{ % `}» : typeId → tableMetadataStructTypeIR → typedefIR
  | DEFAULT : typedefIR
  | HEADER_INVALID : typedefIR
  | «SEQ `< % `>» : (_root_.List typeIR) → typedefIR
  | «SEQ `< % ',' '...' `>» : (_root_.List typeIR) → typedefIR
  | «RECORD `{ % `}» : (_root_.List fieldTypeIR) → typedefIR
  | «RECORD `{ % ',' '...' `}» : (_root_.List fieldTypeIR) → typedefIR
  | «SET `< % `>» : typeIR → typedefIR
  | «TABLE_ENUM % `{ % `}» : typeId → (_root_.List nameIR) → typedefIR
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolTypeIR → boolTypeIR → tableMetadataEnumTypeIR → typedefIR
  | «% ENUM % `{ % `}» : annotationList → nameIR → nameListIR → typedefIR
  | «% ENUM % % `{ % `}» : annotationList → typeIR → nameIR → namedValueListIR → typedefIR
  | «% STRUCT % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → typedefIR
  | «% HEADER % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → typedefIR
  | «% HEADER_UNION % `< % `> `{ % `}» : annotationList → nameIR → typeParameterListIR → typeFieldListIR → typedefIR
deriving _root_.DecidableEq


inductive typedefDeclarationIR : Type where
  | «% TYPEDEF % % ';'» : annotationList → typedefIR → nameIR → typedefDeclarationIR
  | «% TYPE % % ';'» : annotationList → typeIR → nameIR → typedefDeclarationIR
deriving _root_.DecidableEq


inductive externFunctionDeclarationIR : Type where
  | «% EXTERN % ';'» : annotationList → functionPrototypeIR → externFunctionDeclarationIR
deriving _root_.DecidableEq


inductive externConstructorPrototypeIR : Type where
  | «% % `< ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → parameterListIR → externConstructorPrototypeIR
deriving _root_.DecidableEq


abbrev externConstructorPrototypeListIR : Type := (_root_.List externConstructorPrototypeIR)


inductive externMethodPrototypeIR : Type where
  | «% % ';'» : annotationList → functionPrototypeIR → externMethodPrototypeIR
  | «% ABSTRACT % ';'» : annotationList → functionPrototypeIR → externMethodPrototypeIR
deriving _root_.DecidableEq


abbrev externMethodPrototypeListIR : Type := (_root_.List externMethodPrototypeIR)


inductive externObjectDeclarationIR : Type where
  | «% EXTERN % `< % ',' `> `{ % % `}» : annotationList → nameIR → typeParameterListIR → externConstructorPrototypeListIR → externMethodPrototypeListIR → externObjectDeclarationIR
deriving _root_.DecidableEq


inductive externDeclarationIR : Type where
  | «% EXTERN % ';'» : annotationList → functionPrototypeIR → externDeclarationIR
  | «% EXTERN % `< % ',' `> `{ % % `}» : annotationList → nameIR → typeParameterListIR → externConstructorPrototypeListIR → externMethodPrototypeListIR → externDeclarationIR
deriving _root_.DecidableEq


inductive selectCaseIR : Type where
  | «% ':' % ';'» : keysetExpressionIR → nameIR → selectCaseIR
deriving _root_.DecidableEq


abbrev selectCaseListIR : Type := (_root_.List selectCaseIR)


inductive selectExpressionIR : Type where
  | «SELECT `( % `) `{ % `}» : typedExpressionListIR → selectCaseListIR → selectExpressionIR
deriving _root_.DecidableEq


inductive stateExpressionIR : Type where
  | «% ';'» : nameIR → stateExpressionIR
  | «SELECT `( % `) `{ % `}» : typedExpressionListIR → selectCaseListIR → stateExpressionIR
deriving _root_.DecidableEq


inductive transitionStatementIR : Type where
  | TRANSITION : stateExpressionIR → transitionStatementIR
deriving _root_.DecidableEq


inductive valueSetDeclarationIR : Type where
  | «% VALUE_SET `< % `> `( % `) % ';'» : annotationList → typeIR → typedExpressionIR → nameIR → valueSetDeclarationIR
deriving _root_.DecidableEq


inductive parserTypeDeclarationIR : Type where
  | «% PARSER % `< % ',' % `> `( % `) ';'» : annotationList → nameIR → typeParameterListIR → typeParameterListIR → parameterListIR → parserTypeDeclarationIR
deriving _root_.DecidableEq


mutual

inductive parserStatementIR : Type where
  | «';'» : parserStatementIR
  | «% % % ';'» : typedLvalueIR → assignop → typedExpressionIR → parserStatementIR
  | «% `< % `> `( % `) ';'» : callableTargetIR → typeArgumentListIR → argumentListIR → parserStatementIR
  | «% '.' APPLY `( % `) ';'» : constructorTargetIR → argumentListIR → parserStatementIR
  | «% `{ % `}» : annotationList → (_root_.List parserBlockElementStatementIR) → parserStatementIR
  | «IF `( % `) %» : typedExpressionIR → parserStatementIR → parserStatementIR
  | «IF `( % `) % ELSE %» : typedExpressionIR → parserStatementIR → parserStatementIR → parserStatementIR

inductive parserBlockElementStatementIR : Type where
  | «% CONST % % % ';'» : annotationList → typeIR → nameIR → constantInitializerIR → parserBlockElementStatementIR
  | «% % % % ';'» : annotationList → typeIR → nameIR → initializerOptIR → parserBlockElementStatementIR
  | «';'» : parserBlockElementStatementIR
  | «% % % ';'» : typedLvalueIR → assignop → typedExpressionIR → parserBlockElementStatementIR
  | «% `< % `> `( % `) ';'» : callableTargetIR → typeArgumentListIR → argumentListIR → parserBlockElementStatementIR
  | «% '.' APPLY `( % `) ';'» : constructorTargetIR → argumentListIR → parserBlockElementStatementIR
  | «% `{ % `}» : annotationList → (_root_.List parserBlockElementStatementIR) → parserBlockElementStatementIR
  | «IF `( % `) %» : typedExpressionIR → parserStatementIR → parserBlockElementStatementIR
  | «IF `( % `) % ELSE %» : typedExpressionIR → parserStatementIR → parserStatementIR → parserBlockElementStatementIR

end


mutual

def decEq_parserStatementIR (a b : parserStatementIR) : _root_.Decidable (a = b) :=
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
    | .«% `{ % `}» x0 x1, .«% `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_bb8caf8ed4d2 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«IF `( % `) %» x0 x1, .«IF `( % `) %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_parserStatementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«IF `( % `) % ELSE %» x0 x1 x2, .«IF `( % `) % ELSE %» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_parserStatementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_parserStatementIR x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«';'», .«% `{ % `}» _ _ => nomatch hc
    | .«';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«';'» => nomatch hc
    | .«% `{ % `}» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

def decEq_shape_bb8caf8ed4d2 (a b : (_root_.List parserBlockElementStatementIR)) : _root_.Decidable (a = b) :=
  match a, b with
  | [], [] => _root_.Decidable.isTrue rfl
  | x0 :: x1, y0 :: y1 =>
    match decEq_parserBlockElementStatementIR x0 y0 with
    | _root_.Decidable.isTrue h0 =>
      match decEq_shape_bb8caf8ed4d2 x1 y1 with
      | _root_.Decidable.isTrue h1 =>
        _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
      | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)
  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)
termination_by structural a

def decEq_parserBlockElementStatementIR (a b : parserBlockElementStatementIR) : _root_.Decidable (a = b) :=
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
    | .«% `{ % `}» x0 x1, .«% `{ % `}» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_shape_bb8caf8ed4d2 x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«IF `( % `) %» x0 x1, .«IF `( % `) %» y0 y1 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_parserStatementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          _root_.Decidable.isTrue (by cases h0; cases h1; rfl)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«IF `( % `) % ELSE %» x0 x1 x2, .«IF `( % `) % ELSE %» y0 y1 y2 =>
      match _root_.decEq x0 y0 with
      | _root_.Decidable.isTrue h0 =>
        match decEq_parserStatementIR x1 y1 with
        | _root_.Decidable.isTrue h1 =>
          match decEq_parserStatementIR x2 y2 with
          | _root_.Decidable.isTrue h2 =>
            _root_.Decidable.isTrue (by cases h0; cases h1; cases h2; rfl)
          | _root_.Decidable.isFalse h2 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
        | _root_.Decidable.isFalse h1 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
      | _root_.Decidable.isFalse h0 => _root_.Decidable.isFalse (by intro e; injection e; contradiction)
    | .«% CONST % % % ';'» _ _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«';'» => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% CONST % % % ';'» _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«';'» => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% % % % ';'» _ _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«';'», .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«';'», .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«';'», .«% % % ';'» _ _ _ => nomatch hc
    | .«';'», .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«';'», .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«';'», .«% `{ % `}» _ _ => nomatch hc
    | .«';'», .«IF `( % `) %» _ _ => nomatch hc
    | .«';'», .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«';'» => nomatch hc
    | .«% % % ';'» _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% % % ';'» _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«';'» => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% `< % `> `( % `) ';'» _ _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«';'» => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% '.' APPLY `( % `) ';'» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«';'» => nomatch hc
    | .«% `{ % `}» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«IF `( % `) %» _ _ => nomatch hc
    | .«% `{ % `}» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«';'» => nomatch hc
    | .«IF `( % `) %» _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) %» _ _, .«IF `( % `) % ELSE %» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% CONST % % % ';'» _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% % % % ';'» _ _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«';'» => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% % % ';'» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% `< % `> `( % `) ';'» _ _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% '.' APPLY `( % `) ';'» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«% `{ % `}» _ _ => nomatch hc
    | .«IF `( % `) % ELSE %» _ _ _, .«IF `( % `) %» _ _ => nomatch hc
  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))
termination_by structural a

end

instance : _root_.DecidableEq parserStatementIR := decEq_parserStatementIR

instance : _root_.DecidableEq parserBlockElementStatementIR := decEq_parserBlockElementStatementIR


abbrev parserBlockElementStatementListIR : Type := (_root_.List parserBlockElementStatementIR)


inductive parserBlockStatementIR : Type where
  | «% `{ % `}» : annotationList → parserBlockElementStatementListIR → parserBlockStatementIR
deriving _root_.DecidableEq


inductive parserConditionalStatementIR : Type where
  | «IF `( % `) %» : typedExpressionIR → parserStatementIR → parserConditionalStatementIR
  | «IF `( % `) % ELSE %» : typedExpressionIR → parserStatementIR → parserStatementIR → parserConditionalStatementIR
deriving _root_.DecidableEq


inductive parserStateIR : Type where
  | «% STATE % `{ % % `}» : annotationList → nameIR → parserBlockElementStatementListIR → transitionStatementIR → parserStateIR
deriving _root_.DecidableEq

end SpecTec
