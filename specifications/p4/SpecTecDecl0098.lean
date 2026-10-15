import SpecTecDecl0097

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «V1Model_parser:reject:downcast:6» (arg0 : statementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «V1Model_verify:continueEmptyResult:downcast:4» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «V1Model_verify:exit:downcast:4» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «V1Model_ingress:exit:downcast:5» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «V1Model_ingress:cont:downcast:5» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «V1Model_egress:continueEmptyResult:downcast:5» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «V1Model_egress:exit:downcast:5» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «V1Model_check:continueEmptyResult:downcast:4» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «V1Model_check:exit:downcast:4» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «V1Model_deparse:continueEmptyResult:downcast:4» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «V1Model_deparse:exit:downcast:4» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «$field_list_annotation_index:case_1:downcast:4» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$field_list_annotation_index':case_1:downcast:1» (arg0 : annotationToken) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$V1Model_meta_fields_of_index:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_meta_fields_of_index:case_1:downcast:3» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «V1Model_setup_preserved_meta_fields:rule:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «EBPF_init_packet_in:rule:downcast:2» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «EBPF_init_globals:rule:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$eBPF_setup_headers_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$eBPF_setup_main_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$eBPF_setup_parse_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$eBPF_setup_filter_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «EBPF_parse:cont:downcast:4» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «EBPF_parse:reject:downcast:4» (arg0 : statementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «EBPF_filter:continueEmptyResult:downcast:3» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «EBPF_filter:exit:downcast:3» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «$PSA_setup_normal_meta_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_clone_i2e_meta_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_clone_e2e_meta_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_resubmit_meta_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_recirculate_meta_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$PSA_setup_main_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none

end SpecTec
