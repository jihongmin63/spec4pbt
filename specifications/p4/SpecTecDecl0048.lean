import SpecTecDecl0047

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$nestable_array_in_header:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_headerUnion:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_headerUnion:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_headerUnion:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_headerUnion:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_enum_serializable:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_enum_serializable:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_enum_serializable:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_enum_serializable:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_enum_serializable:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_enum_serializable:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_new_in_enum_serializable:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_new_in_enum_serializable:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_new_in_enum_serializable:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_new_in_enum_serializable:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_new_in_enum_serializable:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_new_in_enum_serializable:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_set:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$nestable_set:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.ERROR => 0
  | _ => 1


def «$nestable_set:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_set:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_set:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_set:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_set:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_set:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TUPLE `< % `>» _ => 0
  | _ => 1


def «$nestable_set:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_set:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«SEQ `< % `>» _ => 0
  | _ => 1


def «$nestable_set:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_tuple_in_set:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$nestable_tuple_in_set:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$nestable_tuple_in_set:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$nestable_tuple_in_set:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1

end SpecTec
