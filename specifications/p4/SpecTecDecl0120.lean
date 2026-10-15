import SpecTecDecl0119

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:callableDef:actionDef» : callableDef → Bool
  | .«% ACTION % `( % `) %» _ _ _ _ => true
  | _ => false


def «sub:callableDef:definedFunctionDef» : callableDef → Bool
  | .«FUNCTION % `< % `> `( % `) %» _ _ _ _ => true
  | _ => false


def «sub:callableDef:externFunctionDef» : callableDef → Bool
  | .«EXTERN_FUNCTION % `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:callableDef:externMethodDef» : callableDef → Bool
  | .«EXTERN_METHOD % `< % `> `( % `) %» _ _ _ _ => true
  | .«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:callableDef:functionDef» : callableDef → Bool
  | .«FUNCTION % `< % `> `( % `) %» _ _ _ _ => true
  | .«EXTERN_FUNCTION % `< % `> `( % `)» _ _ _ => true
  | _ => false


def «sub:callableDef:methodDef» : callableDef → Bool
  | .«EXTERN_METHOD % `< % `> `( % `) %» _ _ _ _ => true
  | .«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» _ _ _ => true
  | .«PARSER_APPLY `( % `) `{ % ';' % `}» _ _ _ => true
  | .«CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» _ _ _ _ => true
  | .«TABLE_APPLY `{ % `}» _ => true
  | _ => false


def «sub:callableTargetIR:prefixedNameIR» : callableTargetIR → Bool
  | ._BARE _ => true
  | .«'.' %» _ => true
  | _ => false


def «sub:callableTypeDefIR:actionTypeIR» : callableTypeDefIR → Bool
  | .«% ACTION % `( % `)» _ _ _ => true
  | _ => false


def «sub:callableTypeDefIR:controlApplyMethodTypeIR» : callableTypeDefIR → Bool
  | .«CONTROL_APPLY `( % `)» _ => true
  | _ => false


def «sub:callableTypeDefIR:definedFunctionTypeDefIR» : callableTypeDefIR → Bool
  | .«FUNCTION % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «sub:callableTypeDefIR:externFunctionTypeDefIR» : callableTypeDefIR → Bool
  | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «sub:callableTypeDefIR:externMethodTypeDefIR» : callableTypeDefIR → Bool
  | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «sub:callableTypeDefIR:functionTypeDefIR» : callableTypeDefIR → Bool
  | .«FUNCTION % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «sub:callableTypeDefIR:methodTypeDefIR» : callableTypeDefIR → Bool
  | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | .«PARSER_APPLY `( % `)» _ => true
  | .«CONTROL_APPLY `( % `)» _ => true
  | .«TABLE_APPLY ':' %» _ => true
  | _ => false


def «sub:callableTypeDefIR:parserApplyMethodTypeIR» : callableTypeDefIR → Bool
  | .«PARSER_APPLY `( % `)» _ => true
  | _ => false


def «sub:callableTypeIR:actionTypeIR» : callableTypeIR → Bool
  | .«% ACTION % `( % `)» _ _ _ => true
  | _ => false


def «sub:callableTypeIR:builtinMethodTypeIR» : callableTypeIR → Bool
  | .BUILTIN_IS_VALID => true
  | .BUILTIN_SET_VALID => true
  | .BUILTIN_SET_INVALID => true
  | .BUILTIN_PUSH_FRONT => true
  | .BUILTIN_POP_FRONT => true
  | .BUILTIN_SIZE_OF => true
  | _ => false


def «sub:callableTypeIR:builtinSizeMethodTypeIR» : callableTypeIR → Bool
  | .BUILTIN_SIZE_OF => true
  | _ => false


def «sub:callableTypeIR:controlApplyMethodTypeIR» : callableTypeIR → Bool
  | .«CONTROL_APPLY `( % `)» _ => true
  | _ => false


def «sub:callableTypeIR:definedFunctionTypeIR» : callableTypeIR → Bool
  | .«FUNCTION % `( % `) ':' %» _ _ _ => true
  | _ => false


def «sub:callableTypeIR:externFunctionTypeIR» : callableTypeIR → Bool
  | .«EXTERN_FUNCTION % `( % `) ':' %» _ _ _ => true
  | _ => false


def «sub:callableTypeIR:externMethodTypeIR» : callableTypeIR → Bool
  | .«EXTERN_METHOD % `( % `) ':' %» _ _ _ => true
  | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» _ _ _ => true
  | _ => false


def «sub:callableTypeIR:functionTypeIR» : callableTypeIR → Bool
  | .«FUNCTION % `( % `) ':' %» _ _ _ => true
  | .«EXTERN_FUNCTION % `( % `) ':' %» _ _ _ => true
  | _ => false


def «sub:callableTypeIR:parserApplyMethodTypeIR» : callableTypeIR → Bool
  | .«PARSER_APPLY `( % `)» _ => true
  | _ => false


def «sub:callableTypeIR:tableApplyMethodTypeIR» : callableTypeIR → Bool
  | .«TABLE_APPLY ':' %» _ => true
  | _ => false


def «sub:callee:actionCallee» : callee → Bool
  | .«ACTION % '.' % `( % '#' % `) %» _ _ _ _ _ => true
  | _ => false


def «sub:callee:builtinIsValidMethodCallee» : callee → Bool
  | .BUILTIN_IS_VALID _ => true
  | _ => false


def «sub:callee:builtinPopFrontMethodCallee» : callee → Bool
  | .BUILTIN_POP_FRONT _ => true
  | _ => false


def «sub:callee:builtinPushFrontMethodCallee» : callee → Bool
  | .BUILTIN_PUSH_FRONT _ => true
  | _ => false


def «sub:callee:builtinSetInvalidMethodCallee» : callee → Bool
  | .BUILTIN_SET_INVALID _ => true
  | _ => false


def «sub:callee:builtinSetValidMethodCallee» : callee → Bool
  | .BUILTIN_SET_VALID _ => true
  | _ => false


def «sub:callee:builtinSizeMethodCallee» : callee → Bool
  | .BUILTIN_SIZE_OF _ _ => true
  | _ => false

end SpecTec
