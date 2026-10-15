import SpecTecDecl0031

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$sizeof_minSizeInBits':case_4:downcast:0» (arg0 : typeIR) : (_root_.Option varBitTypeIR) := match arg0 with | .«VARBIT `< % `>» field0 => some (varBitTypeIR.«VARBIT `< % `>» field0) | _ => none


def «$sizeof_minSizeInBits':case_5:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$sizeof_minSizeInBits':case_6:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$sizeof_minSizeInBits':case_7:downcast:0» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$sizeof_minSizeInBits':case_8:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$sizeof_minSizeInBits':case_9:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$sizeof_minSizeInBits':case_10:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$sizeof_minSizeInBits':case_11:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$sizeof_minSizeInBits':case_12:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$sizeof_minSizeInBits':case_13:downcast:0» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$sizeof_maxSizeInBits':case_1:downcast:0» (arg0 : typeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «$sizeof_maxSizeInBits':case_2:downcast:0» (arg0 : typeIR) : (_root_.Option fixedIntTypeIR) := match arg0 with | .«INT `< % `>» field0 => some (fixedIntTypeIR.«INT `< % `>» field0) | _ => none


def «$sizeof_maxSizeInBits':case_3:downcast:0» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «$sizeof_maxSizeInBits':case_4:downcast:0» (arg0 : typeIR) : (_root_.Option varBitTypeIR) := match arg0 with | .«VARBIT `< % `>» field0 => some (varBitTypeIR.«VARBIT `< % `>» field0) | _ => none


def «$sizeof_maxSizeInBits':case_5:downcast:0» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$sizeof_maxSizeInBits':case_6:downcast:0» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$sizeof_maxSizeInBits':case_7:downcast:0» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$sizeof_maxSizeInBits':case_8:downcast:0» (arg0 : typeIR) : (_root_.Option tupleTypeIR) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleTypeIR.«TUPLE `< % `>» field0) | _ => none


def «$sizeof_maxSizeInBits':case_9:downcast:0» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «$sizeof_maxSizeInBits':case_10:downcast:0» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «$sizeof_maxSizeInBits':case_11:downcast:0» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$sizeof_maxSizeInBits':case_12:downcast:0» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$sizeof_maxSizeInBits':case_13:downcast:0» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «$prefixedNonTypeName:case_1:downcast:0» (arg0 : prefixedNonTypeName) : (_root_.Option nonTypeName) := match arg0 with | ._ID field0 => some (nonTypeName._ID field0) | .APPLY => some (nonTypeName.APPLY) | .KEY => some (nonTypeName.KEY) | .ACTIONS => some (nonTypeName.ACTIONS) | .STATE => some (nonTypeName.STATE) | .ENTRIES => some (nonTypeName.ENTRIES) | .TYPE => some (nonTypeName.TYPE) | .PRIORITY => some (nonTypeName.PRIORITY) | _ => none


def «$prefixedTypeName:case_1:downcast:0» (arg0 : prefixedTypeName) : (_root_.Option typeIdentifier) := match arg0 with | ._TID field0 => some (typeIdentifier._TID field0) | _ => none


abbrev nameListIR : Type := (_root_.List nameIR)


abbrev typeParameterListIR : Type := (_root_.List typeParameterIR)


abbrev parameterListIR : Type := (_root_.List parameterIR)


abbrev constructorParameterListIR : Type := (_root_.List parameterIR)


inductive namedValueIR : Type where
  | «% '=' %» : nameIR → value → namedValueIR
deriving _root_.DecidableEq


abbrev namedValueListIR : Type := (_root_.List namedValueIR)


abbrev literalExpressionIR : Type := literalExpression

end SpecTec
