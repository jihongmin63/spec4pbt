import pbt.p4.Unparse

set_option autoImplicit false

namespace Spec4Pbt.P4

private def namedError : SpecTec.p4program :=
  .«% %» ._EMPTY (.«ERROR `{ % `}» (._ID "E"))

private def namedEnum : SpecTec.p4program :=
  .«% %» ._EMPTY
    (.«% ENUM % `{ % % `}» ._EMPTY (._ID "Tags")
      (.«% ',' %» (._ID "A") (._ID "B")) ._EMPTY)

private def namedStruct : SpecTec.p4program :=
  .«% %» ._EMPTY
    (.«% STRUCT % % `{ % `}» ._EMPTY (._ID "Headers") ._EMPTY
      (.«% %» ._EMPTY
        (.«% % % ';'» ._EMPTY (.«BIT `< % `>» 8) (._ID "f"))))

private def namedTypedef : SpecTec.p4program :=
  .«% %» ._EMPTY (.«% TYPEDEF % % ';'» ._EMPTY .BOOL (._ID "Flag"))

private def namedType : SpecTec.p4program :=
  .«% %» ._EMPTY (.«% TYPE % % ';'» ._EMPTY .BOOL (._ID "Flag2"))

private def emptyAction : SpecTec.p4program :=
  .«% %» ._EMPTY
    (.«% ACTION % `( % `) %» ._EMPTY (._ID "Noop") ._EMPTY
      (.«% `{ % `}» ._EMPTY ._EMPTY))

private def emptyNameError : SpecTec.p4program :=
  .«% %» ._EMPTY (.«ERROR `{ % `}» (._ID ""))

private def keywordNameError : SpecTec.p4program :=
  .«% %» ._EMPTY (.«ERROR `{ % `}» (._ID "if"))

private def priorityNameError : SpecTec.p4program :=
  .«% %» ._EMPTY (.«ERROR `{ % `}» (._ID "priority"))

private def dontcareNameError : SpecTec.p4program :=
  .«% %» ._EMPTY (.«ERROR `{ % `}» (._ID "_"))

private def unexpectedAnnotationEnum : SpecTec.p4program :=
  let body : SpecTec.annotationBody := .«% %» ._EMPTY .UNEXPECTED_TOKEN
  .«% %» ._EMPTY
    (.«% ENUM % `{ % % `}»
      (.«'@' % `( % `)» (._ID "Tag") body)
      (._ID "Tags") (._ID "A") ._EMPTY)

private def precedenceConst : SpecTec.p4program :=
  .«% %» ._EMPTY
    (.«% CONST % % % ';'» ._EMPTY .INT (._ID "x")
      (.«'=' %»
        (SpecTec.expression.«% % %»
          (SpecTec.expression.«% % %» (.D 1) .«'+'» (.D 2))
          .«'*'» (.D 3))))

private def negativeWidthStruct : SpecTec.p4program :=
  .«% %» ._EMPTY
    (.«% STRUCT % % `{ % `}» ._EMPTY (._ID "BadWidth") ._EMPTY
      (.«% %» ._EMPTY
        (.«% % % ';'» ._EMPTY (.«BIT `< % `>» (-1)) (._ID "f"))))

private def outerElseAction : SpecTec.p4program :=
  let thenBranch : SpecTec.statement :=
    .«IF `( % `) %» (._ID "inner") .«';'»
  let outerIf : SpecTec.blockElementStatement :=
    .«IF `( % `) % ELSE %» (._ID "outer") thenBranch .«';'»
  .«% %» ._EMPTY
    (.«% ACTION % `( % `) %» ._EMPTY (._ID "A") ._EMPTY
      (.«% `{ % `}» ._EMPTY (.«% %» ._EMPTY outerIf)))

private def stringConst (payload : String) : SpecTec.p4program :=
  .«% %» ._EMPTY
    (.«% CONST % % % ';'» ._EMPTY .STRING (._ID "msg")
      (.«'=' %» (SpecTec.expression.«'"' % '"'» payload)))

/-- An empty syntax tree emits no source text. -/
example : unparseProgram SpecTec.p4program._EMPTY = .ok "" := by rfl

/-- The ERROR declaration retains its identifier and enclosing punctuation. -/
example : unparseProgram namedError = .ok "error { E }\n" := by rfl

/-- Name-list order and commas survive rendering. -/
example : unparseProgram namedEnum = .ok "enum Tags { A , B }\n" := by rfl

/-- A field-bearing struct retains the bit width, field name, and semicolon. -/
example : unparseProgram namedStruct =
    .ok "struct Headers { bit < 8 > f ; }\n" := by rfl

/-- TYPEDEF and TYPE use different keywords for the same source type. -/
example : unparseProgram namedTypedef = .ok "typedef bool Flag ;\n" := by rfl
example : unparseProgram namedType = .ok "type bool Flag2 ;\n" := by rfl

/-- An empty action body keeps both the parameter and block delimiters. -/
example : unparseProgram emptyAction = .ok "action Noop ( ) { }\n" := by rfl

/-- An explicit top-level semicolon remains visible. -/
example : unparseProgram (.«% ';'» ._EMPTY) = .ok ";\n" := by rfl

/-- An explicit semicolon preceding a declaration remains in source order. -/
example : unparseProgram (.«% %» (SpecTec.p4program.«% ';'» ._EMPTY)
    (.«ERROR `{ % `}» (._ID "E"))) = .ok ";\nerror { E }\n" := by rfl

/-- Top-level declarations remain in source order. -/
example : unparseProgram
    (.«% %» namedEnum
      (.«% STRUCT % % `{ % `}» ._EMPTY (._ID "Headers") ._EMPTY
        (.«% %» ._EMPTY
          (.«% % % ';'» ._EMPTY (.«BIT `< % `>» 8) (._ID "f"))))) =
    .ok "enum Tags { A , B }\nstruct Headers { bit < 8 > f ; }\n" := by rfl

/-- An empty identifier cannot be rendered as a P4 identifier token. -/
example :
    (match unparseProgram emptyNameError with
      | .error _ => true
      | .ok _ => false) = true := by rfl

/-- A keyword in an `_ID` field is not an identifier token. -/
example :
    (match unparseProgram keywordNameError with
      | .error _ => true
      | .ok _ => false) = true := by rfl

/-- The `priority` keyword also cannot occupy an `_ID` field. -/
example :
    (match unparseProgram priorityNameError with
      | .error _ => true
      | .ok _ => false) = true := by rfl

/-- A lone underscore is the DONTCARE token, not an identifier. -/
example :
    (match unparseProgram dontcareNameError with
      | .error _ => true
      | .ok _ => false) = true := by rfl

/-- A lexer error token inside a source annotation must be rejected. -/
example :
    (match unparseProgram unexpectedAnnotationEnum with
      | .error _ => true
      | .ok _ => false) = true := by rfl

/-- A child addition must stay grouped under multiplication. -/
example : unparseProgram precedenceConst =
    .ok "const int x = ( ( 1 + 2 ) * 3 ) ;\n" := by rfl

/-- Negative literal widths do not form a P4 bit type. -/
example :
    (match unparseProgram negativeWidthStruct with
      | .error _ => true
      | .ok _ => false) = true := by rfl

/-- Braces keep ELSE bound to the outer IF, as specified by the AST. -/
example : unparseProgram outerElseAction =
    .ok "action A ( ) { if ( outer ) { if ( inner ) ; } else ; }\n" := by rfl

/-- Printable ASCII bytes remain unchanged inside a P4 string literal. -/
example : unparseProgram (stringConst "hello") =
    .ok "const string msg = \"hello\" ;\n" := by rfl

/-- A newline byte cannot be escaped into a different P4 string value. -/
example :
    (match unparseProgram (stringConst "hello\nworld") with
      | .error _ => true
      | .ok _ => false) = true := by rfl

end Spec4Pbt.P4
