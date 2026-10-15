import SpecTecDecl0043

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Type_wf:default_2:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Type_wf:setTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option setTypeIR) := match arg0 with | .«SET `< % `>» field0 => some (setTypeIR.«SET `< % `>» field0) | _ => none


def «Type_wf:enum:downcast:0» (arg0 : typeIR) : (_root_.Option tableMetadataEnumTypeIR) := match arg0 with | .«TABLE_ENUM % `{ % `}» field0 field1 => some (tableMetadataEnumTypeIR.«TABLE_ENUM % `{ % `}» field0 field1) | _ => none


def «Type_wf:struct:downcast:0» (arg0 : typeIR) : (_root_.Option tableMetadataStructTypeIR) := match arg0 with | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (tableMetadataStructTypeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none


def «CallableType_wf:actionTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option actionTypeIR) := match arg0 with | .«% ACTION % `( % `)» field0 field1 field2 => some (actionTypeIR.«% ACTION % `( % `)» field0 field1 field2) | _ => none


def «CallableType_wf:definedFunctionTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option definedFunctionTypeIR) := match arg0 with | .«FUNCTION % `( % `) ':' %» field0 field1 field2 => some (definedFunctionTypeIR.«FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «CallableType_wf:externFunctionTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externFunctionTypeIR) := match arg0 with | .«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2 => some (externFunctionTypeIR.«EXTERN_FUNCTION % `( % `) ':' %» field0 field1 field2) | _ => none


def «CallableType_wf:builtinMethodTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option builtinMethodTypeIR) := match arg0 with | .BUILTIN_IS_VALID => some (builtinMethodTypeIR.BUILTIN_IS_VALID) | .BUILTIN_SET_VALID => some (builtinMethodTypeIR.BUILTIN_SET_VALID) | .BUILTIN_SET_INVALID => some (builtinMethodTypeIR.BUILTIN_SET_INVALID) | .BUILTIN_PUSH_FRONT => some (builtinMethodTypeIR.BUILTIN_PUSH_FRONT) | .BUILTIN_POP_FRONT => some (builtinMethodTypeIR.BUILTIN_POP_FRONT) | .BUILTIN_SIZE_OF => some (builtinMethodTypeIR.BUILTIN_SIZE_OF) | _ => none


def «CallableType_wf:non-abstract:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «CallableType_wf:abstract:downcast:0» (arg0 : callableTypeIR) : (_root_.Option externMethodTypeIR) := match arg0 with | .«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD % `( % `) ':' %» field0 field1 field2) | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2 => some (externMethodTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» field0 field1 field2) | _ => none


def «CallableType_wf:parserApplyMethodTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option parserApplyMethodTypeIR) := match arg0 with | .«PARSER_APPLY `( % `)» field0 => some (parserApplyMethodTypeIR.«PARSER_APPLY `( % `)» field0) | _ => none


def «CallableType_wf:controlApplyMethodTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option controlApplyMethodTypeIR) := match arg0 with | .«CONTROL_APPLY `( % `)» field0 => some (controlApplyMethodTypeIR.«CONTROL_APPLY `( % `)» field0) | _ => none


def «CallableType_wf:tableApplyMethodTypeIR:downcast:0» (arg0 : callableTypeIR) : (_root_.Option tableApplyMethodTypeIR) := match arg0 with | .«TABLE_APPLY ':' %» field0 => some (tableApplyMethodTypeIR.«TABLE_APPLY ':' %» field0) | _ => none


def «ConstructorType_wf:externObjectTypeIR:downcast:2» (arg0 : typeIR) : (_root_.Option externObjectTypeIR) := match arg0 with | .«EXTERN % `< % `> %» field0 field1 field2 => some (externObjectTypeIR.«EXTERN % `< % `> %» field0 field1 field2) | _ => none


def «ConstructorType_wf:parserObjectTypeIR:downcast:4» (arg0 : typeIR) : (_root_.Option parserObjectTypeIR) := match arg0 with | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (parserObjectTypeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | _ => none


def «ConstructorType_wf:controlObjectTypeIR:downcast:4» (arg0 : typeIR) : (_root_.Option controlObjectTypeIR) := match arg0 with | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (controlObjectTypeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | _ => none


def «ConstructorType_wf:tableObjectTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


def «ConstructorType_wf:packageObjectTypeIR:downcast:2» (arg0 : typeIR) : (_root_.Option packageObjectTypeIR) := match arg0 with | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (packageObjectTypeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$nestable_typedef:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$nestable_typedef:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.ERROR => 0
  | _ => 1


def «$nestable_typedef:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.STRING => 0
  | _ => 1


def «$nestable_typedef:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | typeIR.«INT `< % `>» _ => 0
  | typeIR.«BIT `< % `>» _ => 0
  | typeIR.«VARBIT `< % `>» _ => 0
  | _ => 1


def «$nestable_typedef:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR._NAME _ => 0
  | _ => 1


def «$nestable_typedef:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$nestable_typedef:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$nestable_typedef:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«LIST `< % `>» _ => 0
  | typeIR.«TUPLE `< % `>» _ => 0
  | typeIR.«ARRAY % `[ % `]» _ _ => 0
  | typeIR.«HEADER_STACK % `[ % `]» _ _ => 0
  | typeIR.«STRUCT % `< % `> `{ % `}» _ _ _ => 0
  | typeIR.«HEADER % `< % `> `{ % `}» _ _ _ => 0
  | typeIR.«HEADER_UNION % `< % `> `{ % `}» _ _ _ => 0
  | typeIR.«ENUM % `{ % `}» _ _ => 0
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_typedef:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«EXTERN % `< % `> %» _ _ _ => 0
  | _ => 1


def «$nestable_typedef:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PARSER % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_typedef:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«CONTROL % `< % `> `( % `)» _ _ _ => 0
  | _ => 1


def «$nestable_typedef:matches:11:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«PACKAGE % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$nestable_typedef:matches:12:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$nestable_new:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1

end SpecTec
