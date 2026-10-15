import SpecTecDecl0019

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive enumTypeIR : Type where
  | «ENUM % `{ % `}» : typeId → (_root_.List nameIR) → enumTypeIR
  | «ENUM % `< % `> `{ % `}» : typeId → typeIR → (_root_.List valueFieldIR) → enumTypeIR
deriving _root_.DecidableEq


inductive dataTypeIR : Type where
  | «LIST `< % `>» : typeIR → dataTypeIR
  | «TUPLE `< % `>» : (_root_.List typeIR) → dataTypeIR
  | «ARRAY % `[ % `]» : typeIR → _root_.Nat → dataTypeIR
  | «HEADER_STACK % `[ % `]» : typeIR → _root_.Nat → dataTypeIR
  | «STRUCT % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → dataTypeIR
  | «HEADER % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → dataTypeIR
  | «HEADER_UNION % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List fieldTypeIR) → dataTypeIR
  | «ENUM % `{ % `}» : typeId → (_root_.List nameIR) → dataTypeIR
  | «ENUM % `< % `> `{ % `}» : typeId → typeIR → (_root_.List valueFieldIR) → dataTypeIR
deriving _root_.DecidableEq


inductive externObjectTypeIR : Type where
  | «EXTERN % `< % `> %» : typeId → (_root_.List typeArgumentIR) → externMethodTypeDefEnv → externObjectTypeIR
deriving _root_.DecidableEq


inductive parserObjectTypeIR : Type where
  | «PARSER % `< % `> `( % `)» : typeId → (_root_.List typeArgumentIR) → (_root_.List parameterIR) → parserObjectTypeIR
deriving _root_.DecidableEq


inductive controlObjectTypeIR : Type where
  | «CONTROL % `< % `> `( % `)» : typeId → (_root_.List typeArgumentIR) → (_root_.List parameterIR) → controlObjectTypeIR
deriving _root_.DecidableEq


inductive packageObjectTypeIR : Type where
  | «PACKAGE % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List typeIR) → packageObjectTypeIR
deriving _root_.DecidableEq


inductive objectTypeIR : Type where
  | «EXTERN % `< % `> %» : typeId → (_root_.List typeArgumentIR) → externMethodTypeDefEnv → objectTypeIR
  | «PARSER % `< % `> `( % `)» : typeId → (_root_.List typeArgumentIR) → (_root_.List parameterIR) → objectTypeIR
  | «CONTROL % `< % `> `( % `)» : typeId → (_root_.List typeArgumentIR) → (_root_.List parameterIR) → objectTypeIR
  | «PACKAGE % `< % `> `{ % `}» : typeId → (_root_.List typeArgumentIR) → (_root_.List typeIR) → objectTypeIR
  | «TABLE % `{ % `}» : typeId → tableMetadataStructTypeIR → objectTypeIR
deriving _root_.DecidableEq


inductive sequenceTypeIR : Type where
  | «SEQ `< % `>» : (_root_.List typeIR) → sequenceTypeIR
  | «SEQ `< % ',' '...' `>» : (_root_.List typeIR) → sequenceTypeIR
deriving _root_.DecidableEq


inductive recordTypeIR : Type where
  | «RECORD `{ % `}» : (_root_.List fieldTypeIR) → recordTypeIR
  | «RECORD `{ % ',' '...' `}» : (_root_.List fieldTypeIR) → recordTypeIR
deriving _root_.DecidableEq


inductive setTypeIR : Type where
  | «SET `< % `>» : typeIR → setTypeIR
deriving _root_.DecidableEq


inductive synthesizedTypeIR : Type where
  | DEFAULT : synthesizedTypeIR
  | HEADER_INVALID : synthesizedTypeIR
  | «SEQ `< % `>» : (_root_.List typeIR) → synthesizedTypeIR
  | «SEQ `< % ',' '...' `>» : (_root_.List typeIR) → synthesizedTypeIR
  | «RECORD `{ % `}» : (_root_.List fieldTypeIR) → synthesizedTypeIR
  | «RECORD `{ % ',' '...' `}» : (_root_.List fieldTypeIR) → synthesizedTypeIR
  | «SET `< % `>» : typeIR → synthesizedTypeIR
  | «TABLE_ENUM % `{ % `}» : typeId → (_root_.List nameIR) → synthesizedTypeIR
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolTypeIR → boolTypeIR → tableMetadataEnumTypeIR → synthesizedTypeIR
deriving _root_.DecidableEq


abbrev aliasTypeDefIR : Type := aliasTypeIR


inductive structTypeDefIR : Type where
  | «STRUCT % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → structTypeDefIR
deriving _root_.DecidableEq


inductive headerTypeDefIR : Type where
  | «HEADER % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → headerTypeDefIR
deriving _root_.DecidableEq


inductive headerUnionTypeDefIR : Type where
  | «HEADER_UNION % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → headerUnionTypeDefIR
deriving _root_.DecidableEq


abbrev enumTypeDefIR : Type := enumTypeIR


inductive dataTypeDefIR : Type where
  | «STRUCT % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → dataTypeDefIR
  | «HEADER % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → dataTypeDefIR
  | «HEADER_UNION % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → dataTypeDefIR
  | «ENUM % `{ % `}» : typeId → (_root_.List nameIR) → dataTypeDefIR
  | «ENUM % `< % `> `{ % `}» : typeId → typeIR → (_root_.List valueFieldIR) → dataTypeDefIR
deriving _root_.DecidableEq


inductive externObjectTypeDefIR : Type where
  | «EXTERN % `< % ',' % `> %» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → externMethodTypeDefEnv → externObjectTypeDefIR
deriving _root_.DecidableEq


inductive parserObjectTypeDefIR : Type where
  | «PARSER % `< % ',' % `> `( % `)» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → parserObjectTypeDefIR
deriving _root_.DecidableEq


inductive controlObjectTypeDefIR : Type where
  | «CONTROL % `< % ',' % `> `( % `)» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → controlObjectTypeDefIR
deriving _root_.DecidableEq


inductive packageObjectTypeDefIR : Type where
  | «PACKAGE % `< % ',' % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List typeIR) → packageObjectTypeDefIR
deriving _root_.DecidableEq


inductive objectTypeDefIR : Type where
  | «EXTERN % `< % ',' % `> %» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → externMethodTypeDefEnv → objectTypeDefIR
  | «PARSER % `< % ',' % `> `( % `)» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → objectTypeDefIR
  | «CONTROL % `< % ',' % `> `( % `)» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → objectTypeDefIR
  | «PACKAGE % `< % ',' % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List typeIR) → objectTypeDefIR
  | «TABLE % `{ % `}» : typeId → tableMetadataStructTypeIR → objectTypeDefIR
deriving _root_.DecidableEq


inductive typeDefIR : Type where
  | _NAME : typeId → typeDefIR
  | TYPEDEF : typeId → typeIR → typeDefIR
  | TYPE : typeId → typeIR → typeDefIR
  | «STRUCT % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → typeDefIR
  | «HEADER % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → typeDefIR
  | «HEADER_UNION % `< % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List fieldTypeIR) → typeDefIR
  | «ENUM % `{ % `}» : typeId → (_root_.List nameIR) → typeDefIR
  | «ENUM % `< % `> `{ % `}» : typeId → typeIR → (_root_.List valueFieldIR) → typeDefIR
  | «EXTERN % `< % ',' % `> %» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → externMethodTypeDefEnv → typeDefIR
  | «PARSER % `< % ',' % `> `( % `)» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeDefIR
  | «CONTROL % `< % ',' % `> `( % `)» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List parameterIR) → typeDefIR
  | «PACKAGE % `< % ',' % `> `{ % `}» : typeId → (_root_.List typeParameterIR) → (_root_.List typeParameterIR) → (_root_.List typeIR) → typeDefIR
  | «TABLE % `{ % `}» : typeId → tableMetadataStructTypeIR → typeDefIR
deriving _root_.DecidableEq


def «$unroll_typeIR:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$unroll_aliasTypeIR:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$unroll_aliasTypeIR:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$is_defaultable_typeIR:matches:0:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.BOOL => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:1:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.ERROR => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:2:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.STRING => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:3:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.INT => 0
  | typeIR.«INT `< % `>» _ => 0
  | typeIR.«BIT `< % `>» _ => 0
  | typeIR.«VARBIT `< % `>» _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:4:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPEDEF _ _ => 0
  | _ => 1


def «$is_defaultable_typeIR:matches:5:row» (arg0 : typeIR) : _root_.Nat :=
  match arg0 with
  | typeIR.TYPE _ _ => 0
  | _ => 1

end SpecTec
