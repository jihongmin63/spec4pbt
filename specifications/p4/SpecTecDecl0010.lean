import SpecTecDecl0009

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$write_bits_from_value:case_6:downcast:0» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «$write_bits_from_value:case_7:downcast:0» (arg0 : value) : (_root_.Option structValue) := match arg0 with | .«STRUCT % `{ % `}» field0 field1 => some (structValue.«STRUCT % `{ % `}» field0 field1) | _ => none


def «$write_bits_from_value:case_8:downcast:0» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$write_bits_from_value:case_9:downcast:0» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$write_bits_from_value:case_10:downcast:0» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «$write_bits_from_value:case_11:downcast:0» (arg0 : value) : (_root_.Option enumValue) := match arg0 with | .«% '.' %» field0 field1 => some (enumValue.«% '.' %» field0 field1) | .«% '.' % '.' %» field0 field1 field2 => some (enumValue.«% '.' % '.' %» field0 field1 field2) | _ => none


inductive voidTypeIR : Type where
  | VOID : voidTypeIR
deriving _root_.DecidableEq


inductive boolTypeIR : Type where
  | BOOL : boolTypeIR
deriving _root_.DecidableEq


inductive errorTypeIR : Type where
  | ERROR : errorTypeIR
deriving _root_.DecidableEq


inductive matchKindTypeIR : Type where
  | MATCH_KIND : matchKindTypeIR
deriving _root_.DecidableEq


inductive stringTypeIR : Type where
  | STRING : stringTypeIR
deriving _root_.DecidableEq


inductive intTypeIR : Type where
  | INT : intTypeIR
deriving _root_.DecidableEq


inductive fixedIntTypeIR : Type where
  | «INT `< % `>» : _root_.Nat → fixedIntTypeIR
deriving _root_.DecidableEq


inductive fixedBitTypeIR : Type where
  | «BIT `< % `>» : _root_.Nat → fixedBitTypeIR
deriving _root_.DecidableEq


inductive varBitTypeIR : Type where
  | «VARBIT `< % `>» : _root_.Nat → varBitTypeIR
deriving _root_.DecidableEq


inductive integerTypeIR : Type where
  | INT : integerTypeIR
  | «INT `< % `>» : _root_.Nat → integerTypeIR
  | «BIT `< % `>» : _root_.Nat → integerTypeIR
  | «VARBIT `< % `>» : _root_.Nat → integerTypeIR
deriving _root_.DecidableEq


inductive baseTypeIR : Type where
  | VOID : baseTypeIR
  | BOOL : baseTypeIR
  | ERROR : baseTypeIR
  | MATCH_KIND : baseTypeIR
  | STRING : baseTypeIR
  | INT : baseTypeIR
  | «INT `< % `>» : _root_.Nat → baseTypeIR
  | «BIT `< % `>» : _root_.Nat → baseTypeIR
  | «VARBIT `< % `>» : _root_.Nat → baseTypeIR
deriving _root_.DecidableEq


inductive nameTypeIR : Type where
  | _NAME : typeId → nameTypeIR
deriving _root_.DecidableEq


inductive valueFieldIR : Type where
  | «% '=' % ';'» : nameIR → value → valueFieldIR
deriving _root_.DecidableEq


inductive simpleEnumTypeIR : Type where
  | «ENUM % `{ % `}» : typeId → (_root_.List nameIR) → simpleEnumTypeIR
deriving _root_.DecidableEq


inductive defaultTypeIR : Type where
  | DEFAULT : defaultTypeIR
deriving _root_.DecidableEq


inductive invalidHeaderTypeIR : Type where
  | HEADER_INVALID : invalidHeaderTypeIR
deriving _root_.DecidableEq


inductive tableMetadataEnumTypeIR : Type where
  | «TABLE_ENUM % `{ % `}» : typeId → (_root_.List nameIR) → tableMetadataEnumTypeIR
deriving _root_.DecidableEq


inductive tableMetadataStructTypeIR : Type where
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolTypeIR → boolTypeIR → tableMetadataEnumTypeIR → tableMetadataStructTypeIR
deriving _root_.DecidableEq


inductive tableObjectTypeIR : Type where
  | «TABLE % `{ % `}» : typeId → tableMetadataStructTypeIR → tableObjectTypeIR
deriving _root_.DecidableEq


inductive tableMetadataTypeIR : Type where
  | «TABLE_ENUM % `{ % `}» : typeId → (_root_.List nameIR) → tableMetadataTypeIR
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolTypeIR → boolTypeIR → tableMetadataEnumTypeIR → tableMetadataTypeIR
deriving _root_.DecidableEq


abbrev typeParameterIR : Type := typeId


abbrev nameTypeDefIR : Type := nameTypeIR


abbrev tableObjectTypeDefIR : Type := tableObjectTypeIR


def «$width_of_integerTypeIR:case_1:downcast:0» (arg0 : integerTypeIR) : (_root_.Option intTypeIR) := match arg0 with | .INT => some (intTypeIR.INT) | _ => none


def «$width_of_integerTypeIR:case_2:downcast:0» (arg0 : integerTypeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$width_of_integerTypeIR:case_3:downcast:0» (arg0 : integerTypeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none

end SpecTec
