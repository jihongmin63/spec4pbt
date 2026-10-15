import SpecTecDecl0434

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def BlockElementStmts_ok (arg0 : typingContext) (arg1 : (_root_.List blockElementStatement)) (arg2 : typingContext) (arg3 : (_root_.List blockElementStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List blockElementStatementIR)), SpecTecCall.BlockElementStmts_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.BlockElementStmts_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.BlockElementStmts_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.BlockElementStmts_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.BlockElementStmts_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.BlockElementStmts_ok] unexpandRelationNotation
end Notation.BlockElementStmts_ok


noncomputable def ParserStmt_ok (arg0 : typingContext) (arg1 : parserStatement) (arg2 : typingContext) (arg3 : parserStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × parserStatementIR), SpecTecCall.ParserStmt_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ParserStmt_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserStmt_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserStmt_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserStmt_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserStmt_ok] unexpandRelationNotation
end Notation.ParserStmt_ok


noncomputable def ParserBlockElementStmt_ok (arg0 : typingContext) (arg1 : parserBlockElementStatement) (arg2 : typingContext) (arg3 : parserBlockElementStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × parserBlockElementStatementIR), SpecTecCall.ParserBlockElementStmt_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ParserBlockElementStmt_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlockElementStmt_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserBlockElementStmt_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlockElementStmt_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlockElementStmt_ok] unexpandRelationNotation
end Notation.ParserBlockElementStmt_ok


noncomputable def ParserBlockElementStmtList_ok (arg0 : typingContext) (arg1 : parserBlockElementStatementList) (arg2 : typingContext) (arg3 : (_root_.List parserBlockElementStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List parserBlockElementStatementIR)), SpecTecCall.ParserBlockElementStmtList_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ParserBlockElementStmtList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlockElementStmtList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserBlockElementStmtList_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlockElementStmtList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlockElementStmtList_ok] unexpandRelationNotation
end Notation.ParserBlockElementStmtList_ok


noncomputable def ParserBlock_ok (arg0 : typingContext) (arg1 : parserBlockStatement) (arg2 : typingContext) (arg3 : parserBlockStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × parserBlockStatementIR), SpecTecCall.ParserBlock_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ParserBlock_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlock_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserBlock_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlock_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlock_ok] unexpandRelationNotation
end Notation.ParserBlock_ok


noncomputable def ParserBlockElementStmts_ok (arg0 : typingContext) (arg1 : (_root_.List parserBlockElementStatement)) (arg2 : typingContext) (arg3 : (_root_.List parserBlockElementStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List parserBlockElementStatementIR)), SpecTecCall.ParserBlockElementStmts_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ParserBlockElementStmts_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserBlockElementStmts_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserBlockElementStmts_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserBlockElementStmts_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserBlockElementStmts_ok] unexpandRelationNotation
end Notation.ParserBlockElementStmts_ok


noncomputable def FuncDecl_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : functionDeclaration) (arg3 : typingContext) (arg4 : functionDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × functionDeclarationIR), SpecTecCall.FuncDecl_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.FuncDecl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.FuncDecl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.FuncDecl_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.FuncDecl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.FuncDecl_ok] unexpandRelationNotation
end Notation.FuncDecl_ok


noncomputable def ActionDecl_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : actionDeclaration) (arg3 : typingContext) (arg4 : actionDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × actionDeclarationIR), SpecTecCall.ActionDecl_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.ActionDecl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ActionDecl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.ActionDecl_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ActionDecl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ActionDecl_ok] unexpandRelationNotation
end Notation.ActionDecl_ok


noncomputable def InstDecl_non_objectInitializer_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : annotationList) (arg3 : prefixedTypeName) (arg4 : typeArgumentList) (arg5 : argumentList) (arg6 : name) (arg7 : typingContext) (arg8 : instantiationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × instantiationIR), SpecTecCall.InstDecl_non_objectInitializer_ok arg0 arg1 arg2 arg3 arg4 arg5 arg6⟩) 0 (.success (.of ((arg7, arg8)))) finalSupply

namespace Notation.InstDecl_non_objectInitializer_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[9]⟩, ⟨stx[11]⟩, ⟨stx[14]⟩, ⟨stx[15]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.InstDecl_non_objectInitializer_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8) =>
      pure (.node .none `SpecTec.Notation.InstDecl_non_objectInitializer_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, Lean.mkAtom "<", x4, Lean.mkAtom ">", Lean.mkAtom "(", x5, Lean.mkAtom ")", x6, Lean.mkAtom ";", Lean.mkAtom ":", x7, x8])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:51 " < " term:51 " > " " ( " term:51 " ) " term:51 " ; " " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.InstDecl_non_objectInitializer_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.InstDecl_non_objectInitializer_ok] unexpandRelationNotation
end Notation.InstDecl_non_objectInitializer_ok


noncomputable def InstDecl_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : instantiation) (arg3 : typingContext) (arg4 : instantiationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × instantiationIR), SpecTecCall.InstDecl_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.InstDecl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.InstDecl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.InstDecl_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.InstDecl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.InstDecl_ok] unexpandRelationNotation
end Notation.InstDecl_ok


noncomputable def ObjectDecl_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : typeFrame) (arg3 : externMethodTypeDefEnv) (arg4 : objectDeclaration) (arg5 : typeFrame) (arg6 : externMethodTypeDefEnv) (arg7 : objectDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeFrame × (externMethodTypeDefEnv × objectDeclarationIR)), SpecTecCall.ObjectDecl_ok arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, (arg6, arg7))))) finalSupply

namespace Notation.ObjectDecl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ObjectDecl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.ObjectDecl_ok.relationNotation
        #[x0, x1, x2, x3, Lean.mkAtom "|-", x4, Lean.mkAtom ":", x5, x6, x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ObjectDecl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ObjectDecl_ok] unexpandRelationNotation
end Notation.ObjectDecl_ok


noncomputable def ObjectDecls_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : typeFrame) (arg3 : externMethodTypeDefEnv) (arg4 : (_root_.List objectDeclaration)) (arg5 : typeFrame) (arg6 : externMethodTypeDefEnv) (arg7 : objectDeclarationListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeFrame × (externMethodTypeDefEnv × objectDeclarationListIR)), SpecTecCall.ObjectDecls_ok arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, (arg6, arg7))))) finalSupply

namespace Notation.ObjectDecls_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ObjectDecls_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.ObjectDecls_ok.relationNotation
        #[x0, x1, x2, x3, Lean.mkAtom "|-", x4, Lean.mkAtom ":", x5, x6, x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ObjectDecls_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ObjectDecls_ok] unexpandRelationNotation
end Notation.ObjectDecls_ok


noncomputable def ObjectDeclList_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : objectDeclarationList) (arg3 : typeFrame) (arg4 : externMethodTypeDefEnv) (arg5 : objectDeclarationListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeFrame × (externMethodTypeDefEnv × objectDeclarationListIR)), SpecTecCall.ObjectDeclList_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ObjectDeclList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ObjectDeclList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ObjectDeclList_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ObjectDeclList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ObjectDeclList_ok] unexpandRelationNotation
end Notation.ObjectDeclList_ok


noncomputable def InstDecl_objectInitializer_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : annotationList) (arg3 : prefixedTypeName) (arg4 : typeArgumentList) (arg5 : argumentList) (arg6 : name) (arg7 : objectDeclarationList) (arg8 : typingContext) (arg9 : instantiationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × instantiationIR), SpecTecCall.InstDecl_objectInitializer_ok arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7⟩) 0 (.success (.of ((arg8, arg9)))) finalSupply

namespace Notation.InstDecl_objectInitializer_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[9]⟩, ⟨stx[11]⟩, ⟨stx[14]⟩, ⟨stx[18]⟩, ⟨stx[19]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.InstDecl_objectInitializer_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9) =>
      pure (.node .none `SpecTec.Notation.InstDecl_objectInitializer_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, Lean.mkAtom "<", x4, Lean.mkAtom ">", Lean.mkAtom "(", x5, Lean.mkAtom ")", x6, Lean.mkAtom "=", Lean.mkAtom "{", x7, Lean.mkAtom "}", Lean.mkAtom ";", Lean.mkAtom ":", x8, x9])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:51 " < " term:51 " > " " ( " term:51 " ) " term:51 " = " " { " term:51 " } " " ; " " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.InstDecl_objectInitializer_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.InstDecl_objectInitializer_ok] unexpandRelationNotation
end Notation.InstDecl_objectInitializer_ok


noncomputable def ParserLocalDecl_ok (arg0 : typingContext) (arg1 : parserLocalDeclaration) (arg2 : typingContext) (arg3 : parserLocalDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × parserLocalDeclarationIR), SpecTecCall.ParserLocalDecl_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ParserLocalDecl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserLocalDecl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserLocalDecl_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserLocalDecl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserLocalDecl_ok] unexpandRelationNotation
end Notation.ParserLocalDecl_ok


noncomputable def Enum_serializable_field_ok (arg0 : typingContext) (arg1 : nameIR) (arg2 : typeIR) (arg3 : namedExpression) (arg4 : typingContext) (arg5 : namedValueIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × namedValueIR), SpecTecCall.Enum_serializable_field_ok arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.Enum_serializable_field_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Enum_serializable_field_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Enum_serializable_field_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Enum_serializable_field_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Enum_serializable_field_ok] unexpandRelationNotation
end Notation.Enum_serializable_field_ok


noncomputable def Enum_serializable_fields_ok (arg0 : typingContext) (arg1 : nameIR) (arg2 : typeIR) (arg3 : (_root_.List namedExpression)) (arg4 : typingContext) (arg5 : (_root_.List namedValueIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List namedValueIR)), SpecTecCall.Enum_serializable_fields_ok arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.Enum_serializable_fields_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Enum_serializable_fields_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Enum_serializable_fields_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Enum_serializable_fields_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Enum_serializable_fields_ok] unexpandRelationNotation
end Notation.Enum_serializable_fields_ok


noncomputable def Enum_serializable_fieldList_ok (arg0 : typingContext) (arg1 : nameIR) (arg2 : typeIR) (arg3 : namedExpressionList) (arg4 : typingContext) (arg5 : (_root_.List namedValueIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List namedValueIR)), SpecTecCall.Enum_serializable_fieldList_ok arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.Enum_serializable_fieldList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Enum_serializable_fieldList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Enum_serializable_fieldList_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Enum_serializable_fieldList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Enum_serializable_fieldList_ok] unexpandRelationNotation
end Notation.Enum_serializable_fieldList_ok


noncomputable def SelectCase_keyset_simple_ok (arg0 : typingContext) (arg1 : typeIR) (arg2 : simpleKeysetExpression) (arg3 : simpleKeysetExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨simpleKeysetExpressionIR, SpecTecCall.SelectCase_keyset_simple_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.SelectCase_keyset_simple_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SelectCase_keyset_simple_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.SelectCase_keyset_simple_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.SelectCase_keyset_simple_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SelectCase_keyset_simple_ok] unexpandRelationNotation
end Notation.SelectCase_keyset_simple_ok


noncomputable def «SelectCase_keyset_ok:list:iter:2» (arg0 : typingContext) (arg1 : (_root_.List simpleKeysetExpression)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List simpleKeysetExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List simpleKeysetExpressionIR), SpecTecCall.«SelectCase_keyset_ok:list:iter:2» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def SelectCase_keyset_ok (arg0 : typingContext) (arg1 : (_root_.List typeIR)) (arg2 : keysetExpression) (arg3 : keysetExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨keysetExpressionIR, SpecTecCall.SelectCase_keyset_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.SelectCase_keyset_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SelectCase_keyset_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.SelectCase_keyset_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.SelectCase_keyset_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SelectCase_keyset_ok] unexpandRelationNotation
end Notation.SelectCase_keyset_ok


noncomputable def SelectCase_ok (arg0 : typingContext) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : selectCase) (arg4 : selectCaseIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨selectCaseIR, SpecTecCall.SelectCase_ok arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply

namespace Notation.SelectCase_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SelectCase_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.SelectCase_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.SelectCase_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SelectCase_ok] unexpandRelationNotation
end Notation.SelectCase_ok


noncomputable def «ParserSelect_ok:rule:iter:9» (arg0 : typingContext) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List selectCase)) (arg4 : (_root_.List selectCaseIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List selectCaseIR), SpecTecCall.«ParserSelect_ok:rule:iter:9» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def ParserSelect_ok (arg0 : typingContext) (arg1 : (_root_.List nameIR)) (arg2 : selectExpression) (arg3 : selectExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨selectExpressionIR, SpecTecCall.ParserSelect_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ParserSelect_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserSelect_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserSelect_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ParserSelect_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserSelect_ok] unexpandRelationNotation
end Notation.ParserSelect_ok


noncomputable def ParserTransition_ok (arg0 : typingContext) (arg1 : (_root_.List nameIR)) (arg2 : transitionStatement) (arg3 : transitionStatementIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨transitionStatementIR, SpecTecCall.ParserTransition_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ParserTransition_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserTransition_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserTransition_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ParserTransition_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserTransition_ok] unexpandRelationNotation
end Notation.ParserTransition_ok


noncomputable def ParserState_ok (arg0 : typingContext) (arg1 : (_root_.List nameIR)) (arg2 : parserState) (arg3 : parserStateIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨parserStateIR, SpecTecCall.ParserState_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ParserState_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserState_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserState_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ParserState_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserState_ok] unexpandRelationNotation
end Notation.ParserState_ok


noncomputable def «ParserStateList_ok:rule:iter:5» (arg0 : typingContext) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List parserState)) (arg3 : (_root_.List parserStateIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parserStateIR), SpecTecCall.«ParserStateList_ok:rule:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def ParserStateList_ok (arg0 : typingContext) (arg1 : parserStateList) (arg2 : (_root_.List parserStateIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parserStateIR), SpecTecCall.ParserStateList_ok arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.ParserStateList_ok
scoped notation:50 x0:51 " |- " x1:51 " : " x2:51 => _root_.SpecTec.ParserStateList_ok x0 x1 x2
end Notation.ParserStateList_ok


noncomputable def ParserLocalDecls_ok (arg0 : typingContext) (arg1 : (_root_.List parserLocalDeclaration)) (arg2 : typingContext) (arg3 : (_root_.List parserLocalDeclarationIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List parserLocalDeclarationIR)), SpecTecCall.ParserLocalDecls_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ParserLocalDecls_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserLocalDecls_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserLocalDecls_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserLocalDecls_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserLocalDecls_ok] unexpandRelationNotation
end Notation.ParserLocalDecls_ok


noncomputable def ParserLocalDeclList_ok (arg0 : typingContext) (arg1 : parserLocalDeclarationList) (arg2 : typingContext) (arg3 : (_root_.List parserLocalDeclarationIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × (_root_.List parserLocalDeclarationIR)), SpecTecCall.ParserLocalDeclList_ok arg0 arg1⟩) 0 (.success (.of ((arg2, arg3)))) finalSupply

namespace Notation.ParserLocalDeclList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserLocalDeclList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ParserLocalDeclList_ok.relationNotation
        #[x0, Lean.mkAtom "|-", x1, Lean.mkAtom ":", x2, x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserLocalDeclList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserLocalDeclList_ok] unexpandRelationNotation
end Notation.ParserLocalDeclList_ok


noncomputable def TableEntry_keyset_simple_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : matchKey) (arg3 : simpleKeysetExpression) (arg4 : tableEntryState) (arg5 : simpleKeysetExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableEntryState × simpleKeysetExpressionIR), SpecTecCall.TableEntry_keyset_simple_ok arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, arg5)))) finalSupply

namespace Notation.TableEntry_keyset_simple_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableEntry_keyset_simple_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.TableEntry_keyset_simple_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom "@", x3, Lean.mkAtom ":", x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg " @ " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableEntry_keyset_simple_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableEntry_keyset_simple_ok] unexpandRelationNotation
end Notation.TableEntry_keyset_simple_ok


noncomputable def TableEntry_keysets_simple_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : tableEntryState) (arg3 : (_root_.List matchKey)) (arg4 : (_root_.List simpleKeysetExpression)) (arg5 : tableEntryState) (arg6 : (_root_.List simpleKeysetExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableEntryState × (_root_.List simpleKeysetExpressionIR)), SpecTecCall.TableEntry_keysets_simple_ok arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, arg6)))) finalSupply

namespace Notation.TableEntry_keysets_simple_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableEntry_keysets_simple_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.TableEntry_keysets_simple_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom "@", x4, Lean.mkAtom ":", x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:arg " @ " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableEntry_keysets_simple_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableEntry_keysets_simple_ok] unexpandRelationNotation
end Notation.TableEntry_keysets_simple_ok

end SpecTec
