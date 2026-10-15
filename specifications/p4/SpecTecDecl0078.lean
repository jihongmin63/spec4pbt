import SpecTecDecl0077

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Decl_inst:structTypeDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option structTypeDeclarationIR) := match arg0 with | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (structTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_inst:headerTypeDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option headerTypeDeclarationIR) := match arg0 with | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (headerTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_inst:headerUnionTypeDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option headerUnionTypeDeclarationIR) := match arg0 with | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (headerUnionTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_inst:typeIR:downcast:0» (arg0 : declarationIR) : (_root_.Option typedefDeclarationIR) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «Decl_inst:typeIR:downcast:1» (arg0 : typedefIR) : (_root_.Option typeIR) := match arg0 with | .VOID => some (typeIR.VOID) | .BOOL => some (typeIR.BOOL) | .ERROR => some (typeIR.ERROR) | .MATCH_KIND => some (typeIR.MATCH_KIND) | .STRING => some (typeIR.STRING) | .INT => some (typeIR.INT) | .«INT `< % `>» field0 => some (typeIR.«INT `< % `>» field0) | .«BIT `< % `>» field0 => some (typeIR.«BIT `< % `>» field0) | .«VARBIT `< % `>» field0 => some (typeIR.«VARBIT `< % `>» field0) | ._NAME field0 => some (typeIR._NAME field0) | .TYPEDEF field0 field1 => some (typeIR.TYPEDEF field0 field1) | .TYPE field0 field1 => some (typeIR.TYPE field0 field1) | .«LIST `< % `>» field0 => some (typeIR.«LIST `< % `>» field0) | .«TUPLE `< % `>» field0 => some (typeIR.«TUPLE `< % `>» field0) | .«ARRAY % `[ % `]» field0 field1 => some (typeIR.«ARRAY % `[ % `]» field0 field1) | .«HEADER_STACK % `[ % `]» field0 field1 => some (typeIR.«HEADER_STACK % `[ % `]» field0 field1) | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | .«ENUM % `{ % `}» field0 field1 => some (typeIR.«ENUM % `{ % `}» field0 field1) | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | .«EXTERN % `< % `> %» field0 field1 field2 => some (typeIR.«EXTERN % `< % `> %» field0 field1 field2) | .«PARSER % `< % `> `( % `)» field0 field1 field2 => some (typeIR.«PARSER % `< % `> `( % `)» field0 field1 field2) | .«CONTROL % `< % `> `( % `)» field0 field1 field2 => some (typeIR.«CONTROL % `< % `> `( % `)» field0 field1 field2) | .«PACKAGE % `< % `> `{ % `}» field0 field1 field2 => some (typeIR.«PACKAGE % `< % `> `{ % `}» field0 field1 field2) | .«TABLE % `{ % `}» field0 field1 => some (typeIR.«TABLE % `{ % `}» field0 field1) | .DEFAULT => some (typeIR.DEFAULT) | .HEADER_INVALID => some (typeIR.HEADER_INVALID) | .«SEQ `< % `>» field0 => some (typeIR.«SEQ `< % `>» field0) | .«SEQ `< % ',' '...' `>» field0 => some (typeIR.«SEQ `< % ',' '...' `>» field0) | .«RECORD `{ % `}» field0 => some (typeIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (typeIR.«RECORD `{ % ',' '...' `}» field0) | .«SET `< % `>» field0 => some (typeIR.«SET `< % `>» field0) | .«TABLE_ENUM % `{ % `}» field0 field1 => some (typeIR.«TABLE_ENUM % `{ % `}» field0 field1) | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (typeIR.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none


def «Decl_inst:derivedTypeDeclarationIR-monomorphic:downcast:0» (arg0 : declarationIR) : (_root_.Option typedefDeclarationIR) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «Decl_inst:derivedTypeDeclarationIR-monomorphic:downcast:1» (arg0 : typedefIR) : (_root_.Option derivedTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (derivedTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_inst:derivedTypeDeclaration-poly:downcast:0» (arg0 : declarationIR) : (_root_.Option typedefDeclarationIR) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «Decl_inst:derivedTypeDeclaration-poly:downcast:1» (arg0 : typedefIR) : (_root_.Option derivedTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (derivedTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_inst:typedefDeclarationIR-newtype:downcast:0» (arg0 : declarationIR) : (_root_.Option typedefDeclarationIR) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclarationIR.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «Decl_inst:parserTypeDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option parserTypeDeclarationIR) := match arg0 with | .«% PARSER % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (parserTypeDeclarationIR.«% PARSER % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | _ => none


def «Decl_inst:controlTypeDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option controlTypeDeclarationIR) := match arg0 with | .«% CONTROL % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (controlTypeDeclarationIR.«% CONTROL % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | _ => none


def «Decl_inst:packageTypeDeclarationIR:downcast:0» (arg0 : declarationIR) : (_root_.Option packageTypeDeclarationIR) := match arg0 with | .«% PACKAGE % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4 => some (packageTypeDeclarationIR.«% PACKAGE % `< % ',' % `> `( % `) ';'» field0 field1 field2 field3 field4) | _ => none


def «Copy_in_arg_inst_default:initializerIR:downcast:0» (arg0 : parameterInitializerIR) : (_root_.Option initializerIR) := match arg0 with | .«'=' %» field0 => some (initializerIR.«'=' %» field0) | _ => none


def «Copy_in_arg_inst_default:constantInitializerIR:downcast:0» (arg0 : parameterInitializerIR) : (_root_.Option constantInitializerIR) := match arg0 with | .«'=' _VALUE %» field0 => some (constantInitializerIR.«'=' _VALUE %» field0) | _ => none


def «Constructor_inst:aliased:downcast:1» (arg0 : typeDefIR) : (_root_.Option typedefTypeIR) := match arg0 with | .TYPEDEF field0 field1 => some (typedefTypeIR.TYPEDEF field0 field1) | _ => none


def «Constructor_call:externConstructorDef:downcast:0» (arg0 : constructorDef) : (_root_.Option externObjectConstructorDef) := match arg0 with | .«EXTERN % `< % `> `( % `) `{ % `}» field0 field1 field2 field3 => some (externObjectConstructorDef.«EXTERN % `< % `> `( % `) `{ % `}» field0 field1 field2 field3) | _ => none


def «Constructor_call:externConstructorDef:downcast:10» (arg0 : callableDef) : (_root_.Option externMethodDef) := match arg0 with | .«EXTERN_METHOD % `< % `> `( % `) %» field0 field1 field2 field3 => some (externMethodDef.«EXTERN_METHOD % `< % `> `( % `) %» field0 field1 field2 field3) | .«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» field0 field1 field2 => some (externMethodDef.«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» field0 field1 field2) | _ => none


def «Constructor_call:parserConstructorDef:downcast:0» (arg0 : constructorDef) : (_root_.Option parserObjectConstructorDef) := match arg0 with | .«PARSER `< % `> `( % `) `( % `) `{ % % `}» field0 field1 field2 field3 field4 => some (parserObjectConstructorDef.«PARSER `< % `> `( % `) `( % `) `{ % % `}» field0 field1 field2 field3 field4) | _ => none


def «Constructor_call:controlConstructorDef:downcast:0» (arg0 : constructorDef) : (_root_.Option controlObjectConstructorDef) := match arg0 with | .«CONTROL `< % `> `( % `) `( % `) `{ % APPLY % `}» field0 field1 field2 field3 field4 => some (controlObjectConstructorDef.«CONTROL `< % `> `( % `) `( % `) `{ % APPLY % `}» field0 field1 field2 field3 field4) | _ => none


def «Constructor_call:controlConstructorDef:downcast:10» (arg0 : callableDef) : (_root_.Option actionDef) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDef.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «Constructor_call:packageConstructorDef:downcast:0» (arg0 : constructorDef) : (_root_.Option packageObjectConstructorDef) := match arg0 with | .«PACKAGE `< % `> `( % `)» field0 field1 => some (packageObjectConstructorDef.«PACKAGE `< % `> `( % `)» field0 field1) | _ => none


def «SwitchCase_inst:blockStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option blockStatementIR) := match arg0 with | .«% `{ % `}» field0 field1 => some (blockStatementIR.«% `{ % `}» field0 field1) | _ => none


def «$merge_externMethodDefEnvs:case_2:downcast:2» (arg0 : callableDef) : (_root_.Option definedFunctionDef) := match arg0 with | .«FUNCTION % `< % `> `( % `) %» field0 field1 field2 field3 => some (definedFunctionDef.«FUNCTION % `< % `> `( % `) %» field0 field1 field2 field3) | _ => none


def «ObjectDecl_inst:functionDeclarationIR:downcast:0» (arg0 : objectDeclarationIR) : (_root_.Option functionDeclarationIR) := match arg0 with | .«% % %» field0 field1 field2 => some (functionDeclarationIR.«% % %» field0 field1 field2) | _ => none


def «ObjectDecl_inst:instantiationIR:downcast:0» (arg0 : objectDeclarationIR) : (_root_.Option instantiationIR) := match arg0 with | .«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5 => some (instantiationIR.«% % % `( % `) % % ';'» field0 field1 field2 field3 field4 field5) | _ => none


def «$init_table:case_1:downcast:4:0» (arg0 : tablePropertyIR) : (_root_.Option tableActionsPropertyIR) := match arg0 with | .«ACTIONS '=' `{ % `}» field0 => some (tableActionsPropertyIR.«ACTIONS '=' `{ % `}» field0) | _ => none


def «$init_table:case_1:downcast:8:0» (arg0 : tablePropertyIR) : (_root_.Option tableDefaultActionPropertyIR) := match arg0 with | .«% % DEFAULT_ACTION '=' % ';'» field0 field1 field2 => some (tableDefaultActionPropertyIR.«% % DEFAULT_ACTION '=' % ';'» field0 field1 field2) | _ => none


def «$init_table:case_1:downcast:13:0» (arg0 : tablePropertyIR) : (_root_.Option tableCustomPropertyIR) := match arg0 with | .«% % CUSTOM % % ';'» field0 field1 field2 field3 => some (tableCustomPropertyIR.«% % CUSTOM % % ';'» field0 field1 field2 field3) | .«% % CUSTOM_CONST % % ';'» field0 field1 field2 field3 => some (tableCustomPropertyIR.«% % CUSTOM_CONST % % ';'» field0 field1 field2 field3) | _ => none


def «$init_tableKeys:case_1:downcast:3:0» (arg0 : tablePropertyIR) : (_root_.Option tableKeysPropertyIR) := match arg0 with | .«KEY '=' `{ % `}» field0 => some (tableKeysPropertyIR.«KEY '=' `{ % `}» field0) | _ => none


def «$init_tableEntries:case_1:downcast:3:0» (arg0 : tablePropertyIR) : (_root_.Option tableEntriesPropertyIR) := match arg0 with | .«% % ENTRIES '=' `{ % `}» field0 field1 field2 => some (tableEntriesPropertyIR.«% % ENTRIES '=' `{ % `}» field0 field1 field2) | _ => none


abbrev globalEvalLayer : Type := globalInstLayer

end SpecTec
