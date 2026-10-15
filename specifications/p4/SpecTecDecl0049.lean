import SpecTecDecl0048

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$nestable_tuple_in_set:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_tuple_in_set:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_tuple_in_set:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TUPLE `< % `>» _ => 0
  | _ => 1


def «$nestable_tuple_in_set:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_tuple_in_set:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_sequence_in_set:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TUPLE `< % `>» _ => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«SEQ `< % `>» _ => 0
  | _ => 1


def «$nestable_sequence_in_set:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_action:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | _ => 1


def «$nestable_action:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_action:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«EXTERN % `< % `> %» _ _ _ => 0
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_action:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.DEFAULT => 0
  | typeIR.HEADER_INVALID => 0
  | typeIR.«SEQ `< % `>» _ => 0
  | typeIR.«SEQ `< % ',' '...' `>» _ => 0
  | typeIR.«RECORD `{ % `}» _ => 0
  | typeIR.«RECORD `{ % ',' '...' `}» _ => 0
  | typeIR.«SET `< % `>» _ => 0
  | typeIR.«TABLE_ENUM % `{ % `}» _ _ => 0
  | typeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => 0
  | _ => 1


def «$nestable_action:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_definedFunction:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_definedFunction:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«EXTERN % `< % `> %» _ _ _ => 0
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_definedFunction:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.DEFAULT => 0
  | typeIR.HEADER_INVALID => 0
  | typeIR.«SEQ `< % `>» _ => 0
  | typeIR.«SEQ `< % ',' '...' `>» _ => 0
  | typeIR.«RECORD `{ % `}» _ => 0
  | typeIR.«RECORD `{ % ',' '...' `}» _ => 0
  | typeIR.«SET `< % `>» _ => 0
  | typeIR.«TABLE_ENUM % `{ % `}» _ _ => 0
  | typeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => 0
  | _ => 1


def «$nestable_definedFunction:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_externFunction:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_externFunction:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_externFunction:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_externFunction:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_externFunction:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_externFunction:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_externMethod:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_externMethod:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1

end SpecTec
