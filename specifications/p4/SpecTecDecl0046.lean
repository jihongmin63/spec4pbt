import SpecTecDecl0045

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$nestable_tuple:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER_STACK % `[ % `]» _ _ => 0
  | _ => 1


def «$nestable_tuple:matches:11:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«STRUCT % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_tuple:matches:12:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_tuple:matches:13:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER_UNION % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_tuple:matches:14:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_tuple:matches:15:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_array_in_tuple:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«VARBIT `< % `>» _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ARRAY % `[ % `]» _ _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«STRUCT % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_array_in_tuple:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_array:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$nestable_array:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_array:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_array:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«VARBIT `< % `>» _ => 0
  | _ => 1


def «$nestable_array:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_array:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_array:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_array:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ARRAY % `[ % `]» _ _ => 0
  | _ => 1


def «$nestable_array:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«STRUCT % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_array:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_array:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«EXTERN % `< % `> %» _ _ _ => 0
  | _ => 1


def «$nestable_array:matches:11:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_headerStack:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_headerStack:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_headerStack:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1

end SpecTec
