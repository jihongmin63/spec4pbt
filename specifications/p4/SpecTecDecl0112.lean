import SpecTecDecl0111

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «exec:match:callTargetMatch:MATCH» : callTargetMatch → Bool
  | .MATCH _ _ => true
  | _ => false


def «exec:match:callableTargetIR:% '.' %» : callableTargetIR → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «exec:match:callableTargetIR:TYPE % '.' %» : callableTargetIR → Bool
  | .«TYPE % '.' %» _ _ => true
  | _ => false


def «exec:match:callableTargetIR:`( % `)» : callableTargetIR → Bool
  | .«`( % `)» _ => true
  | _ => false


def «exec:match:castResult:FAIL» : castResult → Bool
  | .FAIL => true
  | _ => false


def «exec:match:castResult:OK» : castResult → Bool
  | .OK _ => true
  | _ => false


def «exec:match:conditionalStatement:IF `( % `) %» : conditionalStatement → Bool
  | .«IF `( % `) %» _ _ => true
  | _ => false


def «exec:match:conditionalStatement:IF `( % `) % ELSE %» : conditionalStatement → Bool
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «exec:match:conditionalStatementIR:IF `( % `) %» : conditionalStatementIR → Bool
  | .«IF `( % `) %» _ _ => true
  | _ => false


def «exec:match:conditionalStatementIR:IF `( % `) % ELSE %» : conditionalStatementIR → Bool
  | .«IF `( % `) % ELSE %» _ _ _ => true
  | _ => false


def «exec:match:constOpt:_EMPTY» : constOpt → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:constructorParameterListOpt:_EMPTY» : constructorParameterListOpt → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:constructorParameterListOpt:`( % `)» : constructorParameterListOpt → Bool
  | .«`( % `)» _ => true
  | _ => false


def «exec:match:controlLocalDeclarationList:% %» : controlLocalDeclarationList → Bool
  | .«% %» _ _ => true
  | _ => false


def «exec:match:controlLocalDeclarationList:_EMPTY» : controlLocalDeclarationList → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:ctk:CTK» : ctk → Bool
  | .CTK => true
  | _ => false


def «exec:match:ctk:DYN» : ctk → Bool
  | .DYN => true
  | _ => false


def «exec:match:ctk:LCTK» : ctk → Bool
  | .LCTK => true
  | _ => false


def «exec:match:cursor:BLOCK» : cursor → Bool
  | .BLOCK => true
  | _ => false


def «exec:match:cursor:GLOBAL» : cursor → Bool
  | .GLOBAL => true
  | _ => false


def «exec:match:cursor:LOCAL» : cursor → Bool
  | .LOCAL => true
  | _ => false


def «exec:match:direction:IN» : direction → Bool
  | .IN => true
  | _ => false


def «exec:match:direction:INOUT» : direction → Bool
  | .INOUT => true
  | _ => false


def «exec:match:direction:OUT» : direction → Bool
  | .OUT => true
  | _ => false


def «exec:match:direction:_EMPTY» : direction → Bool
  | ._EMPTY => true
  | _ => false


def «exec:match:enumTypeDeclaration:% ENUM % % `{ % % `}» : enumTypeDeclaration → Bool
  | .«% ENUM % % `{ % % `}» _ _ _ _ _ => true
  | _ => false


def «exec:match:enumTypeDeclaration:% ENUM % `{ % % `}» : enumTypeDeclaration → Bool
  | .«% ENUM % `{ % % `}» _ _ _ _ => true
  | _ => false


def «exec:match:enumTypeDeclarationIR:% ENUM % % `{ % `}» : enumTypeDeclarationIR → Bool
  | .«% ENUM % % `{ % `}» _ _ _ _ => true
  | _ => false


def «exec:match:enumTypeDeclarationIR:% ENUM % `{ % `}» : enumTypeDeclarationIR → Bool
  | .«% ENUM % `{ % `}» _ _ _ => true
  | _ => false


def «exec:match:enumValue:% '.' %» : enumValue → Bool
  | .«% '.' %» _ _ => true
  | _ => false


def «exec:match:enumValue:% '.' % '.' %» : enumValue → Bool
  | .«% '.' % '.' %» _ _ _ => true
  | _ => false


def «exec:match:expressionList:% ',' %» : expressionList → Bool
  | .«% ',' %» _ _ => true
  | _ => false

end SpecTec
