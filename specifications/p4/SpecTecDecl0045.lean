import SpecTecDecl0044

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$nestable_new:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_new:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_new:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_new:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_new:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_new:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_list:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$nestable_list:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.ERROR => 0
  | _ => 1


def «$nestable_list:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.MATCH_KIND => 0
  | _ => 1


def «$nestable_list:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.STRING => 0
  | _ => 1


def «$nestable_list:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | typeIR.«INT `< % `>» _ => 0
  | typeIR.«BIT `< % `>» _ => 0
  | typeIR.«VARBIT `< % `>» _ => 0
  | _ => 1


def «$nestable_list:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_list:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_list:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_list:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«LIST `< % `>» _ => 0
  | _ => 1


def «$nestable_list:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TUPLE `< % `>» _ => 0
  | _ => 1


def «$nestable_list:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER_STACK % `[ % `]» _ _ => 0
  | _ => 1


def «$nestable_list:matches:11:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«STRUCT % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_list:matches:12:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_list:matches:13:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER_UNION % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_list:matches:14:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_list:matches:15:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_tuple:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$nestable_tuple:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.ERROR => 0
  | _ => 1


def «$nestable_tuple:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_tuple:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_tuple:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«VARBIT `< % `>» _ => 0
  | _ => 1


def «$nestable_tuple:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_tuple:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_tuple:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_tuple:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TUPLE `< % `>» _ => 0
  | _ => 1


def «$nestable_tuple:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ARRAY % `[ % `]» _ _ => 0
  | _ => 1

end SpecTec
