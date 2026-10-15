import SpecTecDecl0064

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Call_ok:non-abstract:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «Call_ok:abstract:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «Call_ok:parserApplyMethodTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «Call_ok:controlApplyMethodTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «Call_ok:tableApplyMethodTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option tableApplyMethodTypeIR) := match arg0 with | .«TABLE_APPLY ':' %» field0 => some (tableApplyMethodTypeIR.«TABLE_APPLY ':' %» field0) | _ => none


def «ConstructorType_ok:aliased:downcast:1» (arg0 : typeDefIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


inductive instctxt : Type where
  | NAMED : instctxt
  | ANON : instctxt
deriving _root_.DecidableEq


def «$reduce_serenum:case_1:downcast:3» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$reduce_serenum_unary:case_2:downcast:2» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$reduce_serenum_binary:case_2:downcast:2» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$reduce_serenum_binary:case_3:downcast:3» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$compat_lnot:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$compat_lnot:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$compat_lnot:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$compat_bnot:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$compat_bnot:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$compat_bnot:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$compat_bnot:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$compat_uplusminus:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | _ => 1


def «$compat_uplusminus:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$compat_uplusminus:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$compat_uplusminus:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$compat_uplusminus:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$compat_plusminusmult:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.INT, typeIR.INT => 0
  | _, _ => 1


def «$compat_plusminusmult:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_plusminusmult:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_plusminusmult:matches:3:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1


def «$compat_plusminusmult:matches:4:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, typeIR.TYPEDEF _ _ => 0
  | _, _ => 1


def «$compat_plusminusmult:matches:5:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | _, _ => 0


def «$compat_satplusminus:matches:0:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«INT `< % `>» _, typeIR.«INT `< % `>» _ => 0
  | _, _ => 1


def «$compat_satplusminus:matches:1:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.«BIT `< % `>» _, typeIR.«BIT `< % `>» _ => 0
  | _, _ => 1


def «$compat_satplusminus:matches:2:row» (arg0 : typeIR) (arg1 : typeIR) : _root_.Nat :=
  match arg0, arg1 with
  | typeIR.TYPEDEF _ _, _ => 0
  | _, _ => 1

end SpecTec
