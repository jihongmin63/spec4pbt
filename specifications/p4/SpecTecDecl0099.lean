import SpecTecDecl0098

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «PSA_ingress_init_packet_in:rule:downcast:2» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «PSA_ingress_init_packet_out:rule:downcast:2» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «PSA_ingress_init_globals:rule:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_ingress_hdr_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_ingress_user_meta_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_ingress_pipeline_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_ingress_parser_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_ingress_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_ingress_deparser_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «PSA_ingress_parser:cont:downcast:9» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «PSA_ingress_parser:reject:downcast:9» (arg0 : statementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «PSA_ingress:exit:downcast:7» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «PSA_ingress:cont:downcast:7» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «PSA_ingress_deparser:continueEmptyResult:downcast:10» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «PSA_ingress_deparser:exit:downcast:10» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «PSA_egress_init_packet_in:rule:downcast:2» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «PSA_egress_init_packet_out:rule:downcast:2» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «PSA_egress_init_globals:rule:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «PSA_egress_init_globals:rule:downcast:12» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$PSA_setup_egress_hdr_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_egress_user_meta_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_egress_pipeline_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_egress_parser_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_egress_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_egress_deparser_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «PSA_egress_parser:cont:downcast:10» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «PSA_egress_parser:reject:downcast:10» (arg0 : statementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «PSA_egress:exit:downcast:7» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «PSA_egress:cont:downcast:7» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «PSA_egress_deparser:continueEmptyResult:downcast:10» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «PSA_egress_deparser:exit:downcast:10» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «cast:abortResult:callResult» : abortResult → callResult
  | .EXIT  => (.EXIT )
  | .REJECT a0 => (.REJECT a0)

end SpecTec
