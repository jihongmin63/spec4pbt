import SpecTecDecl0021

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$is_serializable_typeIR:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«INT `< % `>» _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«BIT `< % `>» _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«VARBIT `< % `>» _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:6:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ENUM % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:7:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«TUPLE `< % `>» _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:8:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«ARRAY % `[ % `]» _ _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:9:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER_STACK % `[ % `]» _ _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:10:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«STRUCT % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:11:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:12:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.«HEADER_UNION % `< % `> `{ % `}» _ _ _ => 0
  | _ => 1


def «$is_serializable_typeIR:matches:13:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | _ => 0


def «$typeId_of_typeDefIR:case_1:downcast:0» (arg0 : typeDefIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$typeId_of_typeDefIR:case_2:downcast:0» (arg0 : typeDefIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$typeId_of_typeDefIR:case_3:downcast:0» (arg0 : typeDefIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$typeId_of_typeDefIR:case_4:downcast:0» (arg0 : typeDefIR) : (_root_.Option structTypeDefIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeDefIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeId_of_typeDefIR:case_5:downcast:0» (arg0 : typeDefIR) : (_root_.Option headerTypeDefIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeDefIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeId_of_typeDefIR:case_6:downcast:0» (arg0 : typeDefIR) : (_root_.Option headerUnionTypeDefIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeDefIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeId_of_typeDefIR:case_7:downcast:0» (arg0 : typeDefIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «$typeId_of_typeDefIR:case_8:downcast:0» (arg0 : typeDefIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeId_of_typeDefIR:case_9:downcast:0» (arg0 : typeDefIR) : (_root_.Option externObjectTypeDefIR) := match arg0 with | .«EXTERN % `< % ',' % `> %» field0 field1 field2 field3 => some (externObjectTypeDefIR.«EXTERN % `< % ',' % `> %» field0 field1 field2 field3) | _ => none


def «$typeId_of_typeDefIR:case_10:downcast:0» (arg0 : typeDefIR) : (_root_.Option parserObjectTypeDefIR) := match arg0 with | .«PARSER % `< % ',' % `> `( % `)» field0 field1 field2 field3 => some (parserObjectTypeDefIR.«PARSER % `< % ',' % `> `( % `)» field0 field1 field2 field3) | _ => none


def «$typeId_of_typeDefIR:case_11:downcast:0» (arg0 : typeDefIR) : (_root_.Option controlObjectTypeDefIR) := match arg0 with | .«CONTROL % `< % ',' % `> `( % `)» field0 field1 field2 field3 => some (controlObjectTypeDefIR.«CONTROL % `< % ',' % `> `( % `)» field0 field1 field2 field3) | _ => none


def «$typeId_of_typeDefIR:case_12:downcast:0» (arg0 : typeDefIR) : (_root_.Option packageObjectTypeDefIR) := match arg0 with | .«PACKAGE % `< % ',' % `> `{ % `}» field0 field1 field2 field3 => some (packageObjectTypeDefIR.«PACKAGE % `< % ',' % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «$typeId_of_typeDefIR:case_13:downcast:0» (arg0 : typeDefIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


def «$typeIR_of_typeDefIR:case_1:downcast:0» (arg0 : typeDefIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$typeIR_of_typeDefIR:case_2:downcast:0» (arg0 : typeDefIR) : (_root_.Option aliasTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (aliasTypeIR.TYPEDEF field0 field1) | .TYPE field0 field1 => some (aliasTypeIR.TYPE field0 field1) | _ => none


def «$typeIR_of_typeDefIR:case_3:downcast:0» (arg0 : typeDefIR) : (_root_.Option structTypeDefIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeDefIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeIR_of_typeDefIR:case_4:downcast:0» (arg0 : typeDefIR) : (_root_.Option headerTypeDefIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeDefIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeIR_of_typeDefIR:case_5:downcast:0» (arg0 : typeDefIR) : (_root_.Option headerUnionTypeDefIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeDefIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$typeIR_of_typeDefIR:case_6:downcast:0» (arg0 : typeDefIR) : (_root_.Option enumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (enumTypeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (enumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none

end SpecTec
