import SpecTecDecl0109

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:annotation:'@' % `( % `)» : annotation → Bool
  | .«'@' % `( % `)» _ _ => true
  | _ => false


def «exec:match:annotationBody:% %» : annotationBody → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:annotationBody:_EMPTY» : annotationBody → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:annotationList:_EMPTY» : annotationList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:annotationListNonEmpty:% %» : annotationListNonEmpty → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:argument:% '=' %» : argument → Bool
  | .«% '=' %» _ _ => true
  | _ => false


def «exec:match:argument:% '=' '_'» : argument → Bool
  | .«% '=' '_'» _ => true
  | _ => false


def «exec:match:argumentIR:% '=' %» : argumentIR → Bool
  | .«% '=' %» _ _ => true
  | _ => false


def «exec:match:argumentIR:% '=' '_'» : argumentIR → Bool
  | .«% '=' '_'» _ => true
  | _ => false


def «exec:match:argumentIR:'_'» : argumentIR → Bool
  | .«'_'» => true
  | _ => false


def «exec:match:argumentList:_EMPTY» : argumentList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:argumentListNonEmpty:% ',' %» : argumentListNonEmpty → Bool
  | .«% ',' %» _ _ => true
  | _ => false


def «exec:match:assignop:'%='» : assignop → Bool
  | .«'%='» => true
  | _ => false


def «exec:match:assignop:'&='» : assignop → Bool
  | .«'&='» => true
  | _ => false


def «exec:match:assignop:'*='» : assignop → Bool
  | .«'*='» => true
  | _ => false


def «exec:match:assignop:'+='» : assignop → Bool
  | .«'+='» => true
  | _ => false


def «exec:match:assignop:'-='» : assignop → Bool
  | .«'-='» => true
  | _ => false


def «exec:match:assignop:'/='» : assignop → Bool
  | .«'/='» => true
  | _ => false


def «exec:match:assignop:'<<='» : assignop → Bool
  | .«'<<='» => true
  | _ => false


def «exec:match:assignop:'>>='» : assignop → Bool
  | .«'>>='» => true
  | _ => false


def «exec:match:assignop:'^='» : assignop → Bool
  | .«'^='» => true
  | _ => false


def «exec:match:assignop:'|+|='» : assignop → Bool
  | .«'|+|='» => true
  | _ => false


def «exec:match:assignop:'|-|='» : assignop → Bool
  | .«'|-|='» => true
  | _ => false


def «exec:match:assignop:'|='» : assignop → Bool
  | .«'|='» => true
  | _ => false


def «exec:match:baseType:BIT `< % `>» : baseType → Bool
  | .«BIT `< % `>» _ => true
  | _ => false


def «exec:match:baseType:BIT `< `( % `) `>» : baseType → Bool
  | .«BIT `< `( % `) `>» _ => true
  | _ => false


def «exec:match:baseType:BOOL» : baseType → Bool
  | .BOOL => true
  | _ => false


def «exec:match:baseType:ERROR» : baseType → Bool
  | .ERROR => true
  | _ => false


def «exec:match:baseType:INT» : baseType → Bool
  | .INT => true
  | _ => false


def «exec:match:baseType:INT `< % `>» : baseType → Bool
  | .«INT `< % `>» _ => true
  | _ => false


def «exec:match:baseType:INT `< `( % `) `>» : baseType → Bool
  | .«INT `< `( % `) `>» _ => true
  | _ => false


def «exec:match:baseType:MATCH_KIND» : baseType → Bool
  | .MATCH_KIND => true
  | _ => false

end SpecTec
