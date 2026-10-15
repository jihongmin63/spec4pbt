import SpecTecDecl0062

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «ControlLocalDecl_ok:tableDeclaration:downcast:0» (arg0 : controlLocalDeclaration) : (_root_.Option tableDeclaration) := match arg0 with | .«% TABLE % `{ % `}» field0 field1 field2 => some (tableDeclaration.«% TABLE % `{ % `}» field0 field1 field2) | _ => none


def «VarDecl_ok:initializer:downcast:0» (arg0 : initializerOpt) : (_root_.Option initializer) := match arg0 with | .«'=' %» field0 => some (initializer.«'=' %» field0) | _ => none


def «InstDecl_ok:non-objectInitializer-prefixedTypeName:downcast:0» (arg0 : type) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «InstDecl_ok:non-objectInitializer-specializedType:downcast:0» (arg0 : type) : (_root_.Option specializedType) := match arg0 with | .«% `< % `>» field0 field1 => some (specializedType.«% `< % `>» field0 field1) | _ => none


def «InstDecl_ok:objectInitializer-prefixedTypeName:downcast:0» (arg0 : type) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «InstDecl_ok:objectInitializer-specializedType:downcast:0» (arg0 : type) : (_root_.Option specializedType) := match arg0 with | .«% `< % `>» field0 field1 => some (specializedType.«% `< % `>» field0 field1) | _ => none


def «Decl_ok:constantDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option constantDeclaration) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclaration.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «Decl_ok:instantiation:downcast:0» (arg0 : declaration) : (_root_.Option instantiation) := match arg0 with | .«% % `( % `) % ';'» field0 field1 field2 field3 => some (instantiation.«% % `( % `) % ';'» field0 field1 field2 field3) | .«% % `( % `) % % ';'» field0 field1 field2 field3 field4 => some (instantiation.«% % `( % `) % % ';'» field0 field1 field2 field3 field4) | _ => none


def «Decl_ok:functionDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option functionDeclaration) := match arg0 with | .«% % %» field0 field1 field2 => some (functionDeclaration.«% % %» field0 field1 field2) | _ => none


def «Decl_ok:actionDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option actionDeclaration) := match arg0 with | .«% ACTION % `( % `) %» field0 field1 field2 field3 => some (actionDeclaration.«% ACTION % `( % `) %» field0 field1 field2 field3) | _ => none


def «Decl_ok:errorDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option errorDeclaration) := match arg0 with | .«ERROR `{ % `}» field0 => some (errorDeclaration.«ERROR `{ % `}» field0) | _ => none


def «Decl_ok:matchKindDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option matchKindDeclaration) := match arg0 with | .«MATCH_KIND `{ % % `}» field0 field1 => some (matchKindDeclaration.«MATCH_KIND `{ % % `}» field0 field1) | _ => none


def «Decl_ok:externFunctionDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option externFunctionDeclaration) := match arg0 with | .«% EXTERN % ';'» field0 field1 => some (externFunctionDeclaration.«% EXTERN % ';'» field0 field1) | _ => none


def «Decl_ok:externObjectDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option externObjectDeclaration) := match arg0 with | .«% EXTERN % % `{ % `}» field0 field1 field2 field3 => some (externObjectDeclaration.«% EXTERN % % `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_ok:parserDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option parserDeclaration) := match arg0 with | .«% PARSER % % `( % `) % `{ % % `}» field0 field1 field2 field3 field4 field5 field6 => some (parserDeclaration.«% PARSER % % `( % `) % `{ % % `}» field0 field1 field2 field3 field4 field5 field6) | _ => none


def «Decl_ok:controlDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option controlDeclaration) := match arg0 with | .«% CONTROL % % `( % `) % `{ % APPLY % `}» field0 field1 field2 field3 field4 field5 field6 => some (controlDeclaration.«% CONTROL % % `( % `) % `{ % APPLY % `}» field0 field1 field2 field3 field4 field5 field6) | _ => none


def «Decl_ok:enumTypeDeclaration-non-serializable:downcast:0» (arg0 : declaration) : (_root_.Option enumTypeDeclaration) := match arg0 with | .«% ENUM % `{ % % `}» field0 field1 field2 field3 => some (enumTypeDeclaration.«% ENUM % `{ % % `}» field0 field1 field2 field3) | .«% ENUM % % `{ % % `}» field0 field1 field2 field3 field4 => some (enumTypeDeclaration.«% ENUM % % `{ % % `}» field0 field1 field2 field3 field4) | _ => none


def «Decl_ok:enumTypeDeclaration-serializable:downcast:0» (arg0 : declaration) : (_root_.Option enumTypeDeclaration) := match arg0 with | .«% ENUM % `{ % % `}» field0 field1 field2 field3 => some (enumTypeDeclaration.«% ENUM % `{ % % `}» field0 field1 field2 field3) | .«% ENUM % % `{ % % `}» field0 field1 field2 field3 field4 => some (enumTypeDeclaration.«% ENUM % % `{ % % `}» field0 field1 field2 field3 field4) | _ => none


def «Decl_ok:structTypeDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option structTypeDeclaration) := match arg0 with | .«% STRUCT % % `{ % `}» field0 field1 field2 field3 => some (structTypeDeclaration.«% STRUCT % % `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_ok:headerTypeDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option headerTypeDeclaration) := match arg0 with | .«% HEADER % % `{ % `}» field0 field1 field2 field3 => some (headerTypeDeclaration.«% HEADER % % `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_ok:headerUnionTypeDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option headerUnionTypeDeclaration) := match arg0 with | .«% HEADER_UNION % % `{ % `}» field0 field1 field2 field3 => some (headerUnionTypeDeclaration.«% HEADER_UNION % % `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_ok:type:downcast:0» (arg0 : declaration) : (_root_.Option typedefDeclaration) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclaration.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclaration.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «Decl_ok:type:downcast:1» (arg0 : typedef) : (_root_.Option type) := match arg0 with | .BOOL => some (type.BOOL) | .ERROR => some (type.ERROR) | .MATCH_KIND => some (type.MATCH_KIND) | .STRING => some (type.STRING) | .INT => some (type.INT) | .«INT `< % `>» field0 => some (type.«INT `< % `>» field0) | .«INT `< `( % `) `>» field0 => some (type.«INT `< `( % `) `>» field0) | .BIT => some (type.BIT) | .«BIT `< % `>» field0 => some (type.«BIT `< % `>» field0) | .«BIT `< `( % `) `>» field0 => some (type.«BIT `< `( % `) `>» field0) | .«VARBIT `< % `>» field0 => some (type.«VARBIT `< % `>» field0) | .«VARBIT `< `( % `) `>» field0 => some (type.«VARBIT `< `( % `) `>» field0) | ._TID field0 => some (type._TID field0) | .«_TID '.' %» field0 => some (type.«_TID '.' %» field0) | .«% `< % `>» field0 field1 => some (type.«% `< % `>» field0 field1) | .«% `[ % `]» field0 field1 => some (type.«% `[ % `]» field0 field1) | .«LIST `< % `>» field0 => some (type.«LIST `< % `>» field0) | .«TUPLE `< % `>» field0 => some (type.«TUPLE `< % `>» field0) | _ => none


def «Decl_ok:derivedTypeDeclaration-mono:downcast:0» (arg0 : declaration) : (_root_.Option typedefDeclaration) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclaration.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclaration.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «Decl_ok:derivedTypeDeclaration-mono:downcast:1» (arg0 : typedef) : (_root_.Option derivedTypeDeclaration) := match arg0 with | .«% ENUM % `{ % % `}» field0 field1 field2 field3 => some (derivedTypeDeclaration.«% ENUM % `{ % % `}» field0 field1 field2 field3) | .«% ENUM % % `{ % % `}» field0 field1 field2 field3 field4 => some (derivedTypeDeclaration.«% ENUM % % `{ % % `}» field0 field1 field2 field3 field4) | .«% STRUCT % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclaration.«% STRUCT % % `{ % `}» field0 field1 field2 field3) | .«% HEADER % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclaration.«% HEADER % % `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclaration.«% HEADER_UNION % % `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_ok:derivedTypeDeclaration-mono:downcast:2» (arg0 : declarationIR) : (_root_.Option derivedTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (derivedTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_ok:derivedTypeDeclaration-poly:downcast:0» (arg0 : declaration) : (_root_.Option typedefDeclaration) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclaration.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclaration.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «Decl_ok:derivedTypeDeclaration-poly:downcast:1» (arg0 : typedef) : (_root_.Option derivedTypeDeclaration) := match arg0 with | .«% ENUM % `{ % % `}» field0 field1 field2 field3 => some (derivedTypeDeclaration.«% ENUM % `{ % % `}» field0 field1 field2 field3) | .«% ENUM % % `{ % % `}» field0 field1 field2 field3 field4 => some (derivedTypeDeclaration.«% ENUM % % `{ % % `}» field0 field1 field2 field3 field4) | .«% STRUCT % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclaration.«% STRUCT % % `{ % `}» field0 field1 field2 field3) | .«% HEADER % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclaration.«% HEADER % % `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclaration.«% HEADER_UNION % % `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_ok:derivedTypeDeclaration-poly:downcast:2» (arg0 : declarationIR) : (_root_.Option derivedTypeDeclarationIR) := match arg0 with | .«% ENUM % `{ % `}» field0 field1 field2 => some (derivedTypeDeclarationIR.«% ENUM % `{ % `}» field0 field1 field2) | .«% ENUM % % `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% ENUM % % `{ % `}» field0 field1 field2 field3) | .«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% STRUCT % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER % `< % `> `{ % `}» field0 field1 field2 field3) | .«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3 => some (derivedTypeDeclarationIR.«% HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 field3) | _ => none


def «Decl_ok:typedefDeclaration-newtype:downcast:0» (arg0 : declaration) : (_root_.Option typedefDeclaration) := match arg0 with | .«% TYPEDEF % % ';'» field0 field1 field2 => some (typedefDeclaration.«% TYPEDEF % % ';'» field0 field1 field2) | .«% TYPE % % ';'» field0 field1 field2 => some (typedefDeclaration.«% TYPE % % ';'» field0 field1 field2) | _ => none


def «Decl_ok:parserTypeDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option parserTypeDeclaration) := match arg0 with | .«% PARSER % % `( % `) ';'» field0 field1 field2 field3 => some (parserTypeDeclaration.«% PARSER % % `( % `) ';'» field0 field1 field2 field3) | _ => none


def «Decl_ok:controlTypeDeclaration:downcast:0» (arg0 : declaration) : (_root_.Option controlTypeDeclaration) := match arg0 with | .«% CONTROL % % `( % `) ';'» field0 field1 field2 field3 => some (controlTypeDeclaration.«% CONTROL % % `( % `) ';'» field0 field1 field2 field3) | _ => none

end SpecTec
