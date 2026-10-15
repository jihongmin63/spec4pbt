import SpecTecDecl0070

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$insert_NoAction_tablePropertyIR:case_2:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableActionsPropertyIR) := match arg0 with | .«ACTIONS '=' `{ % `}» field0 => some (tableActionsPropertyIR.«ACTIONS '=' `{ % `}» field0) | _ => none


def «$insert_NoAction_tablePropertyIR:case_3:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableActionsPropertyIR) := match arg0 with | .«ACTIONS '=' `{ % `}» field0 => some (tableActionsPropertyIR.«ACTIONS '=' `{ % `}» field0) | _ => none


inductive strict : Type where
  | STRICT : strict
  | LAX : strict
deriving _root_.DecidableEq


abbrev strictness : Type := (map typeId strict)


inductive infer : Type where
  | «KNOWN AS %» : typeIR → infer
  | UNKNOWN : infer
deriving _root_.DecidableEq


abbrev constraint : Type := (map typeId infer)


abbrev inference : Type := (map typeId typeIR)


def «$infer_pair:case_1:downcast:0» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$resolve_inference':case_1:downcast:1» (arg0 : typeIR) : (_root_.Option sequenceTypeIR) := match arg0 with | .«SEQ `< % `>» field0 => some (sequenceTypeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (sequenceTypeIR.«SEQ `< % ',' '...' `>» field0) | _ => none


def «$gen_constraint_pair:case_1:downcast:0» (arg0 : typeIR) : (_root_.Option nameTypeIR) := match arg0 with | ._NAME field0 => some (nameTypeIR._NAME field0) | _ => none


def «$gen_constraint_pair:case_2:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$gen_constraint_pair:case_3:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$gen_constraint_pair:case_4:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$gen_constraint_pair:case_4:downcast:1» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$gen_constraint_pair:case_5:downcast:0» (arg0 : typeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «$gen_constraint_pair:case_5:downcast:1» (arg0 : typeIR) : (_root_.Option listTypeIR) := match arg0 with | .«LIST `< % `>» field0 => some (listTypeIR.«LIST `< % `>» field0) | _ => none


def «$gen_constraint_pair:case_6:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$gen_constraint_pair:case_6:downcast:1» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$gen_constraint_pair:case_7:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$gen_constraint_pair:case_7:downcast:1» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$gen_constraint_pair:case_8:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$gen_constraint_pair:case_8:downcast:1» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$gen_constraint_pair:case_9:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_9:downcast:1» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_10:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_10:downcast:1» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_11:downcast:0» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_11:downcast:1» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_12:downcast:0» (arg0 : typeIR) : (_root_.Option externObjectTypeIR) := match arg0 with | .«EXTERN % `< % `> %» field0 field1 field2 => some (externObjectTypeIR.«EXTERN % `< % `> %» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_12:downcast:1» (arg0 : typeIR) : (_root_.Option externObjectTypeIR) := match arg0 with | .«EXTERN % `< % `> %» field0 field1 field2 => some (externObjectTypeIR.«EXTERN % `< % `> %» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_13:downcast:0» (arg0 : typeIR) : (_root_.Option parserObjectTypeIR) := match arg0 with | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (parserObjectTypeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | _ => none


def «$gen_constraint_pair:case_13:downcast:1» (arg0 : typeIR) : (_root_.Option parserObjectTypeIR) := match arg0 with | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (parserObjectTypeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | _ => none

end SpecTec
