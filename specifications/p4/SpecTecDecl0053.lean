import SpecTecDecl0052

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Expr_eval_lctk:parenthesizedExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option parenthesizedExpressionIR) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpressionIR.«`( % `)» field0) | _ => none


def «Argument_eval_lctk:typedExpressionIR:downcast:0» (arg0 : argumentIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Type_ok:boolean:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:error:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:matchKind:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:string:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:arbitraryInt:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:integer:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:expression:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:expression:downcast:2» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Type_ok:none:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:integer_2:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:expression_2:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:expression_2:downcast:2» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Type_ok:integer_3:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:expression_3:downcast:0» (arg0 : typeOrVoid) : (_root_.Option baseType) := match arg0 with | .BOOL => some (baseType.BOOL) | .ERROR => some (baseType.ERROR) | .MATCH_KIND => some (baseType.MATCH_KIND) | .STRING => some (baseType.STRING) | .INT => some (baseType.INT) | .«INT `< % `>» field0 => some (baseType.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (baseType.«INT `< `( % `) `>» field0) | .BIT => some (baseType.BIT) | .«BIT `< % `>» field0 => some (baseType.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (baseType.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (baseType.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (baseType.«VARBIT `< `( % `) `>» field0) | _ => none


def «Type_ok:expression_3:downcast:2» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Type_ok:identifier:downcast:0» (arg0 : typeOrVoid) : (_root_.Option identifier) := match arg0 with | ._ID field0 => some (identifier._ID field0) | _ => none


def «Type_ok:monomorphic:downcast:0» (arg0 : typeOrVoid) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «Type_ok:polymorphic:downcast:0» (arg0 : typeOrVoid) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «Type_ok:specializedType:downcast:0» (arg0 : typeOrVoid) : (_root_.Option specializedType) := match arg0 with | .«% `< % `>» field0 field1 => some (specializedType.«% `< % `>» field0 field1) | _ => none


def «Type_ok:headerStackType:downcast:0» (arg0 : typeOrVoid) : (_root_.Option arrayType) := match arg0 with | .«% `[ % `]» field0 field1 => some (arrayType.«% `[ % `]» field0 field1) | _ => none


def «Type_ok:headerStackType:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Type_ok:arrayType:downcast:0» (arg0 : typeOrVoid) : (_root_.Option arrayType) := match arg0 with | .«% `[ % `]» field0 field1 => some (arrayType.«% `[ % `]» field0 field1) | _ => none


def «Type_ok:arrayType:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Type_ok:listType:downcast:0» (arg0 : typeOrVoid) : (_root_.Option listType) := match arg0 with | .«LIST `< % `>» field0 => some (listType.«LIST `< % `>» field0) | _ => none


def «Type_ok:tupleType:downcast:0» (arg0 : typeOrVoid) : (_root_.Option tupleType) := match arg0 with | .«TUPLE `< % `>» field0 => some (tupleType.«TUPLE `< % `>» field0) | _ => none


def «TypeArgument_ok:type:downcast:0» (arg0 : typeArgument) : (_root_.Option type) := match arg0 with | .BOOL => some (type.BOOL) | .ERROR => some (type.ERROR) | .MATCH_KIND => some (type.MATCH_KIND) | .STRING => some (type.STRING) | .INT => some (type.INT) | .«INT `< % `>» field0 => some (type.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (type.«INT `< `( % `) `>» field0) | .BIT => some (type.BIT) | .«BIT `< % `>» field0 => some (type.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (type.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (type.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (type.«VARBIT `< `( % `) `>» field0) | ._TID field0 => some (type._TID field0) | .«_TID '.' %» field0 => some (type.«_TID '.' %» field0) | .«% `< % `>» field0 field1 => some (type.«% `< % `>» field0 field1) | .«% `[ % `]» field0 field1 => some (type.«% `[ % `]» field0 field1) | .«LIST `< % `>» field0 => some (type.«LIST `< % `>» field0) | .«TUPLE `< % `>» field0 => some (type.«TUPLE `< % `>» field0) | _ => none


def «TypeArgument_ok:nonTypeName:downcast:0» (arg0 : typeArgument) : (_root_.Option nonTypeName) := match arg0 with | ._ID field0 => some (nonTypeName._ID field0) | .APPLY => some (nonTypeName.APPLY) | .KEY => some (nonTypeName.KEY) | .ACTIONS => some (nonTypeName.ACTIONS) | .STATE => some (nonTypeName.STATE) | .ENTRIES => some (nonTypeName.ENTRIES) | .TYPE => some (nonTypeName.TYPE) | .PRIORITY => some (nonTypeName.PRIORITY) | _ => none


inductive castResult : Type where
  | OK : (_root_.List typeIR) → castResult
  | FAIL : castResult
deriving _root_.DecidableEq


def «Cast_expl_neq:boolean-fixBit:downcast:0» (arg0 : typeIR) : (_root_.Option boolTypeIR) := match arg0 with | .BOOL => some (boolTypeIR.BOOL) | _ => none


def «Cast_expl_neq:boolean:downcast:0» (arg0 : typeIR) : (_root_.Option intTypeIR) := match arg0 with | .INT => some (intTypeIR.INT) | _ => none

end SpecTec
