import SpecTecDecl0112

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:expressionList:_EMPTY» : expressionList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:externConstructorOrMethodPrototypeList:% %» : externConstructorOrMethodPrototypeList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:externConstructorOrMethodPrototypeList:_EMPTY» : externConstructorOrMethodPrototypeList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:externMethodDef:EXTERN_METHOD % `< % `> `( % `) %» : externMethodDef → Bool
  | .«EXTERN_METHOD % `< % `> `( % `) %» _ _ _ _ => true
  | _ => false


def «exec:match:externMethodLocalKind:EXTERN_METHOD ':' %» : externMethodLocalKind → Bool
  | .«EXTERN_METHOD ':' %» _ => true
  | _ => false


def «exec:match:externMethodLocalKind:EXTERN_METHOD ABSTRACT ':' %» : externMethodLocalKind → Bool
  | .«EXTERN_METHOD ABSTRACT ':' %» _ => true
  | _ => false


def «exec:match:externMethodPrototype:% % ';'» : externMethodPrototype → Bool
  | .«% % ';'» _ _ => true
  | _ => false


def «exec:match:externMethodPrototype:% ABSTRACT % ';'» : externMethodPrototype → Bool
  | .«% ABSTRACT % ';'» _ _ => true
  | _ => false


def «exec:match:externMethodPrototypeIR:% % ';'» : externMethodPrototypeIR → Bool
  | .«% % ';'» _ _ => true
  | _ => false


def «exec:match:externMethodPrototypeIR:% ABSTRACT % ';'» : externMethodPrototypeIR → Bool
  | .«% ABSTRACT % ';'» _ _ => true
  | _ => false


def «exec:match:externMethodTypeDefIR:EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» : externMethodTypeDefIR → Bool
  | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «exec:match:externMethodTypeDefIR:EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» : externMethodTypeDefIR → Bool
  | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» _ _ _ _ _ => true
  | _ => false


def «exec:match:externMethodTypeIR:EXTERN_METHOD % `( % `) ':' %» : externMethodTypeIR → Bool
  | .«EXTERN_METHOD % `( % `) ':' %» _ _ _ => true
  | _ => false


def «exec:match:externMethodTypeIR:EXTERN_METHOD ABSTRACT % `( % `) ':' %» : externMethodTypeIR → Bool
  | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» _ _ _ => true
  | _ => false


def «exec:match:flow:RET» : flow → Bool
  | .RET => true
  | _ => false


def «exec:match:forCollectionExpression:% '..' %» : forCollectionExpression → Bool
  | .«% '..' %» _ _ => true
  | _ => false


def «exec:match:forCollectionExpressionIR:% '..' %» : forCollectionExpressionIR → Bool
  | .«% '..' %» _ _ => true
  | _ => false


def «exec:match:forInitStatement:% % % %» : forInitStatement → Bool
  | .«% % % %» _ _ _ _ => true
  | _ => false


def «exec:match:forInitStatementIR:% % % %» : forInitStatementIR → Bool
  | .«% % % %» _ _ _ _ => true
  | _ => false


def «exec:match:forInitStatementList:_EMPTY» : forInitStatementList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:forInitStatementListNonEmpty:% ',' %» : forInitStatementListNonEmpty → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:forStatement:% FOR `( % % % IN % `) %» : forStatement → Bool
  | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => true
  | _ => false


def «exec:match:forStatement:% FOR `( % % IN % `) %» : forStatement → Bool
  | .«% FOR `( % % IN % `) %» _ _ _ _ _ => true
  | _ => false


def «exec:match:forStatement:% FOR `( % ';' % ';' % `) %» : forStatement → Bool
  | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => true
  | _ => false


def «exec:match:forStatementIR:% FOR `( % % % IN % `) %» : forStatementIR → Bool
  | .«% FOR `( % % % IN % `) %» _ _ _ _ _ _ => true
  | _ => false


def «exec:match:forStatementIR:% FOR `( % % IN % `) %» : forStatementIR → Bool
  | .«% FOR `( % % IN % `) %» _ _ _ _ _ => true
  | _ => false


def «exec:match:forStatementIR:% FOR `( % ';' % ';' % `) %» : forStatementIR → Bool
  | .«% FOR `( % ';' % ';' % `) %» _ _ _ _ _ => true
  | _ => false


def «exec:match:forUpdateStatement:% % %» : forUpdateStatement → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «exec:match:forUpdateStatement:% `( % `)» : forUpdateStatement → Bool
  | .«% `( % `)» _ _ => true
  | _ => false


def «exec:match:forUpdateStatement:% `< % `> `( % `)» : forUpdateStatement → Bool
  | .«% `< % `> `( % `)» _ _ _ => true
  | _ => false


def «exec:match:forUpdateStatementIR:% % %» : forUpdateStatementIR → Bool
  | .«% % %» _ _ _ => true
  | _ => false


def «exec:match:forUpdateStatementIR:% `< % `> `( % `)» : forUpdateStatementIR → Bool
  | .«% `< % `> `( % `)» _ _ _ => true
  | _ => false

end SpecTec
