import SpecTecDecl0065

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$compat_satplusminus:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_satplusminus:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «$compat_divmod:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.INT, typeIR.INT => 0
  | _, _ => 1


def «$compat_divmod:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_divmod:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_divmod:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_divmod:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «$compat_shift:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.INT, typeIR.INT => 0
  | _, _ => 1


def «$compat_shift:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.INT, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_shift:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.INT, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_shift:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.INT => 0
  | _, _ => 1


def «$compat_shift:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_shift:matches:5:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_shift:matches:6:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.INT => 0
  | _, _ => 1


def «$compat_shift:matches:7:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_shift:matches:8:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_shift:matches:9:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_shift:matches:10:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_shift:matches:11:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «$compat_compare:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.INT, typeIR.INT => 0
  | _, _ => 1


def «$compat_compare:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_compare:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_compare:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_compare:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_compare:matches:5:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «$compat_bitwise:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_bitwise:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_bitwise:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_bitwise:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_bitwise:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «$compat_concat:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.STRING, typeIR.STRING => 0
  | _, _ => 1


def «$compat_concat:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1

end SpecTec
