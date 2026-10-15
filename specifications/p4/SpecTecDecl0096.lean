import SpecTecDecl0095

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «SelectCases_match:cons-head-match:downcast:0» (arg0 : selectCaseMatchResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «SelectCases_match:cons-head-match_2:downcast:0» (arg0 : selectCaseMatchResult) : (_root_.Option (continueResult (_root_.Option _root_.String))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


inductive tableKeyValue : Type where
  | «% ':' %» : value → nameIR → tableKeyValue
deriving _root_.DecidableEq


inductive tableKeyResult : Type where
  | _CONT : tableKeyValue → tableKeyResult
  | EXIT : tableKeyResult
deriving _root_.DecidableEq


def «TableKey_eval:exit:downcast:0» (arg0 : expressionResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «TableKey_eval:cont:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


inductive tableKeysResult : Type where
  | _CONT : (_root_.List tableKeyValue) → tableKeysResult
  | EXIT : tableKeysResult
deriving _root_.DecidableEq


def «Table_eval:keys-exit:downcast:0» (arg0 : tableKeysResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «Table_eval:keys-cont-matches-exit:downcast:0» (arg0 : tableKeysResult) : (_root_.Option (continueResult (_root_.List tableKeyValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Table_eval:keys-cont-matches-cont-action-exit:downcast:0» (arg0 : tableKeysResult) : (_root_.Option (continueResult (_root_.List tableKeyValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Table_eval:keys-cont-matches-cont-action-cont:downcast:0» (arg0 : tableKeysResult) : (_root_.Option (continueResult (_root_.List tableKeyValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «TableKeys_eval:cons-head-exit:downcast:0» (arg0 : tableKeyResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «TableKeys_eval:cons-head-cont-tail-exit:downcast:0» (arg0 : tableKeyResult) : (_root_.Option (continueResult tableKeyValue)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «TableKeys_eval:cons-head-cont-tail-exit:downcast:1» (arg0 : tableKeysResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «TableKeys_eval:cons-head-cont-tail-cont:downcast:0» (arg0 : tableKeyResult) : (_root_.Option (continueResult tableKeyValue)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «TableKeys_eval:cons-head-cont-tail-cont:downcast:1» (arg0 : tableKeysResult) : (_root_.Option (continueResult (_root_.List tableKeyValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


inductive tableMatch : Type where
  | «% ':' %» : (_root_.Option _root_.Nat) → tableActionReferenceIR → tableMatch
deriving _root_.DecidableEq


inductive tableMatchResult : Type where
  | _CONT : (_root_.Option tableMatch) → tableMatchResult
  | EXIT : tableMatchResult
deriving _root_.DecidableEq


def «TableMatch_eval:exit:downcast:1» (arg0 : keysetExpressionResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «TableMatch_eval:no-match:downcast:1» (arg0 : keysetExpressionResult) : (_root_.Option (continueResult (_root_.List setValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «TableMatch_eval:match:downcast:1» (arg0 : keysetExpressionResult) : (_root_.Option (continueResult (_root_.List setValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


inductive tableMatchesResult : Type where
  | _CONT : (_root_.List tableMatch) → tableMatchesResult
  | EXIT : tableMatchesResult
deriving _root_.DecidableEq


def «Table_eval:keys-cont-matches-exit:downcast:1» (arg0 : tableMatchesResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «Table_eval:keys-cont-matches-cont-action-exit:downcast:1» (arg0 : tableMatchesResult) : (_root_.Option (continueResult (_root_.List tableMatch))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Table_eval:keys-cont-matches-cont-action-cont:downcast:1» (arg0 : tableMatchesResult) : (_root_.Option (continueResult (_root_.List tableMatch))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «TableMatches_eval:cons-head-exit:downcast:0» (arg0 : tableMatchResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «TableMatches_eval:cons-head-cont-tail-exit:downcast:0» (arg0 : tableMatchResult) : (_root_.Option (continueResult (_root_.Option tableMatch))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «TableMatches_eval:cons-head-cont-tail-exit:downcast:1» (arg0 : tableMatchesResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «TableMatches_eval:cons-head-cont-tail-cont:downcast:0» (arg0 : tableMatchResult) : (_root_.Option (continueResult (_root_.Option tableMatch))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «TableMatches_eval:cons-head-cont-tail-cont:downcast:1» (arg0 : tableMatchesResult) : (_root_.Option (continueResult (_root_.List tableMatch))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «$largest_priority_wins:case_1:downcast:4» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


inductive actionResult : Type where
  | EXIT : actionResult
  | RETURN : (_root_.Option value) → actionResult
deriving _root_.DecidableEq

end SpecTec
