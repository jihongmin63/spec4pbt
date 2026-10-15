import SpecTecDecl0042

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

structure matchPriority : Type where
  («DELTA» : _root_.Nat)
  («LARGEST_WINS» : _root_.Bool)
deriving _root_.DecidableEq


structure matchEntries : Type where
  («SIZE» : _root_.Nat)
  («CONST» : _root_.Bool)
deriving _root_.DecidableEq


inductive matchMode : Type where
  | NONE : matchMode
  | LPM : _root_.Nat → matchMode
  | PRI : matchMode
deriving _root_.DecidableEq


structure tableContext : Type where
  («KEYS» : (_root_.List matchKey))
  («ACTIONS» : (_root_.List matchAction))
  («PRIORITIES» : matchPriority)
  («ENTRIES» : matchEntries)
  («MODE» : matchMode)
deriving _root_.DecidableEq


inductive tableEntryState : Type where
  | LPM : _root_.Nat → tableEntryState
  | NON_LPM : tableEntryState
deriving _root_.DecidableEq


def «$update_mode_tbl:case_2:downcast:8» (arg0 : typeIR) : (_root_.Option integerTypeIR) := match arg0 with | .INT => some (integerTypeIR.INT) | .«INT `< % `>» field0 => some (integerTypeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (integerTypeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (integerTypeIR.«VARBIT `< % `>» field0) | _ => none


def «$tableEntry_lpm_prefix':case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$tableEntry_lpm_prefix':case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$tableEntry_lpm_prefix':case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «Type_wf:baseTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option baseTypeIR) := match arg0 with | .VOID => some (baseTypeIR.VOID) | .BOOL => some (baseTypeIR.BOOL) | .ERROR => some (baseTypeIR.ERROR) | .MATCH_KIND => some (baseTypeIR.MATCH_KIND) | .STRING => some (baseTypeIR.STRING) | .INT => some (baseTypeIR.INT) | .«INT `< % `>» field0 => some (baseTypeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (baseTypeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (baseTypeIR.«VARBIT `< % `>» field0) | _ => none


def «Type_wf:nameTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «Type_wf:typedefTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «Type_wf:newTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «Type_wf:listTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «Type_wf:tupleTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «Type_wf:arrayTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «Type_wf:headerStackTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «Type_wf:structTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Type_wf:headerTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Type_wf:headerUnionTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Type_wf:non-serializable:downcast:0» (arg0 : typeIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «Type_wf:serializable:downcast:0» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Type_wf:externObjectTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option externObjectTypeIR) := match arg0 with | .«EXTERN % `< % `> %» field0 field1 field2 => some (externObjectTypeIR.«EXTERN % `< % `> %» field0 field1 field2) | _ => none


def «Type_wf:parserObjectTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option parserObjectTypeIR) := match arg0 with | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (parserObjectTypeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | _ => none


def «Type_wf:controlObjectTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option controlObjectTypeIR) := match arg0 with | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (controlObjectTypeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | _ => none


def «Type_wf:packageObjectTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option packageObjectTypeIR) := match arg0 with | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (packageObjectTypeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Type_wf:tableObjectTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option tableObjectTypeIR) := match arg0 with | .«TABLE % `{ % `}» field0 field1 => some (tableObjectTypeIR.«TABLE % `{ % `}» field0 field1) | _ => none


def «Type_wf:defaultTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option defaultTypeIR) := match arg0 with | .DEFAULT => some (defaultTypeIR.DEFAULT) | _ => none


def «Type_wf:invalidHeaderTypeIR:downcast:0» (arg0 : typeIR) : (_root_.Option invalidHeaderTypeIR) := match arg0 with | .HEADER_INVALID => some (invalidHeaderTypeIR.HEADER_INVALID) | _ => none


def «Type_wf:non-default:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Type_wf:default:downcast:0» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «Type_wf:non-default_2:downcast:0» (arg0 : typeIR) : (_root_.Option recordTypeIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordTypeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordTypeIR.«RECORD `{ % ',' '...' `}» field0) | _ => none

end SpecTec
