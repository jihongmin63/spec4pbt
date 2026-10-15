import SpecTecDecl0088

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «ControlLocalDecls_eval:cons-head-cont:downcast:0» (arg0 : controlLocalDeclarationResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


inductive declarationResult : Type where
  | _EMPTY : declarationResult
  | EXIT : declarationResult
  | REJECT : errorValue → declarationResult
deriving _root_.DecidableEq


def «ParserBlockElementStmt_eval:variableDeclarationIR-reject:downcast:1» (arg0 : declarationResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserBlockElementStmt_eval:variableDeclarationIR-empty:downcast:1» (arg0 : declarationResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ParserLocalDecl_eval:reject:downcast:1» (arg0 : declarationResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserLocalDecl_eval:cont:downcast:1» (arg0 : declarationResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ControlLocalDecl_eval:exit:downcast:1» (arg0 : declarationResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «ControlLocalDecl_eval:cont:downcast:1» (arg0 : declarationResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «VarDecl_eval:initializer-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «VarDecl_eval:initializer-cont:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


inductive calleeResult : Type where
  | _CONT : callee → calleeResult
  | EXIT : calleeResult
  | REJECT : errorValue → calleeResult
deriving _root_.DecidableEq


def «Expr_eval:callee-abort:downcast:1» (arg0 : calleeResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:callee-cont-call-abort:downcast:1» (arg0 : calleeResult) : (_root_.Option (continueResult callee)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:callee-cont-call-return:downcast:1» (arg0 : calleeResult) : (_root_.Option (continueResult callee)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:callee-abort:downcast:1» (arg0 : calleeResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:callee-cont-call-abort:downcast:1» (arg0 : calleeResult) : (_root_.Option (continueResult callee)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:callee-cont-call-return:downcast:1» (arg0 : calleeResult) : (_root_.Option (continueResult callee)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:actionCallee:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «Callee_eval:actionCallee:downcast:2:1» (arg0 : callableDef) : (_root_.Option actionDef) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDef.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «Callee_eval:externFunctionCallee:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «Callee_eval:externFunctionCallee:downcast:2» (arg0 : callableDef) : (_root_.Option externFunctionDef) := match arg0 with | .«EXTERN_FUNCTION % `< % `> `( % `)» field0 field1 field2 => some (externFunctionDef.«EXTERN_FUNCTION % `< % `> `( % `)» field0 field1 field2) | _ => none


def «Callee_eval:definedFunctionCallee:downcast:0» (arg0 : callableTargetIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «Callee_eval:definedFunctionCallee:downcast:2» (arg0 : callableDef) : (_root_.Option definedFunctionDef) := match arg0 with | .«FUNCTION % `< % `> `( % `) %» field0 field1 field2 field3 => some (definedFunctionDef.«FUNCTION % `< % `> `( % `) %» field0 field1 field2 field3) | _ => none


def «Callee_eval:abort:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Callee_eval:cont:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:abort_2:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Callee_eval:cont_2:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:abort_3:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Callee_eval:cont_3:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:abort_4:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Callee_eval:cont_4:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Callee_eval:abort_5:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none

end SpecTec
