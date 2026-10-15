import SpecTecDecl0076

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «ParserLocalDecl_inst:variableDeclarationIR:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserLocalDecl_inst:valueSetDeclarationIR:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option valueSetDeclarationIR) := match arg0 with | .«% VALUE_SET `< % `> `( % `) % ';'» field0 field1 field2 field3 => some (valueSetDeclarationIR.«% VALUE_SET `< % `> `( % `) % ';'» field0 field1 field2 field3) | _ => none


def «ParserLocalDecl_inst:valueSetDeclarationIR:downcast:1» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «TableAction_inst:name-annotation-dot-prefix:downcast:1» (arg0 : callableDef) : (_root_.Option actionDef) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDef.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «TableAction_inst:name-annotation:downcast:1» (arg0 : callableDef) : (_root_.Option actionDef) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDef.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «TableAction_inst:no-name-annotation:downcast:1» (arg0 : callableDef) : (_root_.Option actionDef) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDef.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «TableProperty_inst:tableKeysPropertyIR:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableKeysPropertyIR) := match arg0 with | .«KEY '=' `{ % `}» field0 => some (tableKeysPropertyIR.«KEY '=' `{ % `}» field0) | _ => none


def «TableProperty_inst:tableActionsPropertyIR:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableActionsPropertyIR) := match arg0 with | .«ACTIONS '=' `{ % `}» field0 => some (tableActionsPropertyIR.«ACTIONS '=' `{ % `}» field0) | _ => none


def «TableProperty_inst:tableDefaultActionPropertyIR:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableDefaultActionPropertyIR) := match arg0 with | .«% % DEFAULT_ACTION '=' % ';'» field0 field1 field2 => some (tableDefaultActionPropertyIR.«% % DEFAULT_ACTION '=' % ';'» field0 field1 field2) | _ => none


def «TableProperty_inst:tableEntriesPropertyIR:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableEntriesPropertyIR) := match arg0 with | .«% % ENTRIES '=' `{ % `}» field0 field1 field2 => some (tableEntriesPropertyIR.«% % ENTRIES '=' `{ % `}» field0 field1 field2) | _ => none


def «TableProperty_inst:custom:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableCustomPropertyIR) := match arg0 with | .«% % CUSTOM % % ';'» field0 field1 field2 field3 => some (tableCustomPropertyIR.«% % CUSTOM % % ';'» field0 field1 field2 field3) | .«% % CUSTOM_CONST % % ';'» field0 field1 field2 field3 => some (tableCustomPropertyIR.«% % CUSTOM_CONST % % ';'» field0 field1 field2 field3) | _ => none


def «TableProperty_inst:custom-const:downcast:0» (arg0 : tablePropertyIR) : (_root_.Option tableCustomPropertyIR) := match arg0 with | .«% % CUSTOM % % ';'» field0 field1 field2 field3 => some (tableCustomPropertyIR.«% % CUSTOM % % ';'» field0 field1 field2 field3) | .«% % CUSTOM_CONST % % ';'» field0 field1 field2 field3 => some (tableCustomPropertyIR.«% % CUSTOM_CONST % % ';'» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_inst:constantDeclarationIR:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_inst:instantiationIR:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option instantiationIR) := match arg0 with | .«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5 => some (instantiationIR.«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5) | _ => none


def «ControlLocalDecl_inst:variableDeclarationIR:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_inst:actionDeclarationIR:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option actionDeclarationIR) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDeclarationIR.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_inst:tableDeclarationIR-no-name-annotation:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option tableDeclarationIR) := match arg0 with | .«% TABLE % % `{ % `}» field0 field1 field2 field3 => some (tableDeclarationIR.«% TABLE % % `{ % `}» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_inst:tableDeclarationIR-name-annotation:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option tableDeclarationIR) := match arg0 with | .«% TABLE % % `{ % `}» field0 field1 field2 field3 => some (tableDeclarationIR.«% TABLE % % `{ % `}» field0 field1 field2 field3) | _ => none


def «InstDecl_inst:extern:downcast:1» (arg0 : object) : (_root_.Option externObject) := match arg0 with | .«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4 => some (externObject.«EXTERN % `< % `> `{ % % % `}» field0 field1 field2 field3 field4) | _ => none


def «Decl_inst:constantDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «Decl_inst:instantiationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option instantiationIR) := match arg0 with | .«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5 => some (instantiationIR.«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5) | _ => none


def «Decl_inst:functionDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option functionDeclarationIR) := match arg0 with | .«% % %» field0 field1 field2 => some (functionDeclarationIR.«% % %» field0 field1 field2) | _ => none


def «Decl_inst:actionDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option actionDeclarationIR) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDeclarationIR.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «Decl_inst:errorDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option errorDeclarationIR) := match arg0 with | .«ERROR `{ % `}» field0 => some (errorDeclarationIR.«ERROR `{ % `}» field0) | _ => none


def «Decl_inst:matchKindDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option matchKindDeclarationIR) := match arg0 with | .«MATCH_KIND `{ % `}» field0 => some (matchKindDeclarationIR.«MATCH_KIND `{ % `}» field0) | _ => none


def «Decl_inst:externFunctionDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option externFunctionDeclarationIR) := match arg0 with | .«% EXTERN % ';'» field0 field1 => some (externFunctionDeclarationIR.«% EXTERN % ';'» field0 field1) | _ => none


def «Decl_inst:non-constructor:downcast:0» (arg0 : declarationIR) : (_root_.Option externObjectDeclarationIR) := match arg0 with | .«% EXTERN % `< % ',' `> `{ % % `}» field0 field1 field2 field3 field4 => some (externObjectDeclarationIR.«% EXTERN % `< % ',' `> `{ % % `}» field0 field1 field2 field3 field4) | _ => none


def «Decl_inst:constructor:downcast:0» (arg0 : declarationIR) : (_root_.Option externObjectDeclarationIR) := match arg0 with | .«% EXTERN % `< % ',' `> `{ % % `}» field0 field1 field2 field3 field4 => some (externObjectDeclarationIR.«% EXTERN % `< % ',' `> `{ % % `}» field0 field1 field2 field3 field4) | _ => none


def «Decl_inst:parserDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option parserDeclarationIR) := match arg0 with | .«% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» field0 field1 field2 field3 field4 field5 field6 field7 => some (parserDeclarationIR.«% PARSER % `< % ',' % `> `( % `) `( % `) `{ % % `}» field0 field1 field2 field3 field4 field5 field6 field7) | _ => none


def «Decl_inst:controlDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option controlDeclarationIR) := match arg0 with | .«% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» field0 field1 field2 field3 field4 field5 field6 field7 => some (controlDeclarationIR.«% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» field0 field1 field2 field3 field4 field5 field6 field7) | _ => none


def «Decl_inst:enumTypeDeclarationIR-non-serializable:downcast:0» (arg0 : declarationIR) : (_root_.Option enumTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (enumTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (enumTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_inst:enumTypeDeclarationIR-serializable:downcast:0» (arg0 : declarationIR) : (_root_.Option enumTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (enumTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (enumTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | _ => none

end SpecTec
