import SpecTecDecl0020

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$is_defaultable_typeIR:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TUPLE `< % `>» _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ARRAY % `[ % `]» _ _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER_STACK % `[ % `]» _ _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«STRUCT % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:11:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER_UNION % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:12:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:13:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:14:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$is_equalable_typeIR:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.VOID => 0
  | _ => 1


def «$is_equalable_typeIR:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«EXTERN % `< % `> %» _ _ _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.DEFAULT => 0
  | _ => 1


def «$is_equalable_typeIR:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«SEQ `< % `>» _ => 0
  | typeIR.«SEQ `< % ',' '...' `>» _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«RECORD `{ % `}» _ => 0
  | typeIR.«RECORD `{ % ',' '...' `}» _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:11:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.HEADER_INVALID => 0
  | _ => 1


def «$is_equalable_typeIR:matches:12:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«SET `< % `>» _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:13:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE_ENUM % `{ % `}» _ _ => 0
  | typeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => 0
  | _ => 1


def «$is_equalable_typeIR:matches:14:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$is_assignable_typeIR:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.VOID => 0
  | _ => 1


def «$is_assignable_typeIR:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.STRING => 0
  | _ => 1


def «$is_assignable_typeIR:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | _ => 1


def «$is_assignable_typeIR:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$is_assignable_typeIR:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«EXTERN % `< % `> %» _ _ _ => 0
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$is_assignable_typeIR:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
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


def «$is_assignable_typeIR:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$is_serializable_typeIR:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1

end SpecTec
