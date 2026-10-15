import SpecTecDecl0096

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Call_eval:copyin-cont-ActionBody-exit:downcast:4» (arg0 : actionResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «ActionBody_eval:cont:downcast:0» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ActionBody_eval:exit:downcast:0» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


inductive definedFunctionResult : Type where
  | EXIT : definedFunctionResult
  | RETURN : (_root_.Option value) → definedFunctionResult
deriving _root_.DecidableEq


def «DefinedFunctionBody_eval:cont:downcast:0» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «DefinedFunctionBody_eval:exit:downcast:0» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «DefinedFunctionBody_eval:return-void:downcast:0» (arg0 : statementResult) : (_root_.Option returnResult) := match arg0 with | .RETURN field0 => some (returnResult.RETURN field0) | _ => none


def «$cast_control_plane:case_3:downcast:1» (arg0 : expressionIR) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$cast_control_plane:case_3:downcast:2» (arg0 : typeIR) : (_root_.Option intTypeIR) := match arg0 with | .INT => some (intTypeIR.INT) | _ => none


def «$cast_control_plane:case_3:downcast:8» (arg0 : value) : (_root_.Option errorValue) := match arg0 with | .«ERROR '.' %» field0 => some (errorValue.«ERROR '.' %» field0) | _ => none


def «$cast_control_plane:case_4:downcast:1» (arg0 : typeIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «$cast_control_plane:case_5:downcast:1» (arg0 : typeIR) : (_root_.Option newTypeIR) := match arg0 with | .TYPE field0 field1 => some (newTypeIR.TYPE field0 field1) | _ => none


def «$cast_control_plane:case_6:downcast:1» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


abbrev tableEntryPriorityInterface : Type := (_root_.Option _root_.Int)


inductive tableKeyValueInterface : Type where
  | _BIN : _root_.String → tableKeyValueInterface
  | _HEX : _root_.String → tableKeyValueInterface
  | _DEC : _root_.String → tableKeyValueInterface
  | «% _SLASH %» : _root_.String → _root_.Nat → tableKeyValueInterface
deriving _root_.DecidableEq


abbrev tableKeyInterface : Type := (nameIR × tableKeyValueInterface)


abbrev tableKeysetInterface : Type := (_root_.List tableKeyInterface)


abbrev tableActionArgumentInterface : Type := (nameIR × _root_.Int)


abbrev tableActionInterface : Type := (nameIR × (_root_.List tableActionArgumentInterface))


def «V1Model_init_packet_in:rule:downcast:2» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «V1Model_init_packet_out:rule:downcast:2» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «V1Model_init_globals:rule:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_hdr_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_meta_argument:case_1:downcast:1» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_main_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_parser_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_verify_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_ingress_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_egress_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_check_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «$V1Model_setup_deparse_callee:case_1:downcast:2» (arg0 : object) : (_root_.Option packageObject) := match arg0 with | .«PACKAGE `< % `> `{ % `}» field0 field1 => some (packageObject.«PACKAGE `< % `> `{ % `}» field0 field1) | _ => none


def «V1Model_parser:cont:downcast:6» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none

end SpecTec
