import SpecTecDecl0049

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$nestable_externMethod:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_externMethod:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_externMethod:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_externMethod:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_parserApplyMethod:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_parserApplyMethod:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_parserApplyMethod:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_parserApplyMethod:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_parserApplyMethod:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_parserApplyMethod:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_controlApplyMethod:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_controlApplyMethod:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_controlApplyMethod:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_controlApplyMethod:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_controlApplyMethod:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_constructor_extern:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_constructor_extern:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_constructor_extern:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_constructor_extern:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_constructor_extern:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_constructor_extern:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_constructor_parser:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_constructor_parser:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_constructor_parser:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_constructor_parser:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_constructor_parser:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_constructor_control:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_constructor_control:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_constructor_control:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_constructor_control:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TABLE % `{ % `}» _ _ => 0
  | _ => 1


def «$nestable_constructor_control:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_constructor_package:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1

end SpecTec
