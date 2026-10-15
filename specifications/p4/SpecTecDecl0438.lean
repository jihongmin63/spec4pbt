import SpecTecDecl0437

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def ParserSelect_eval (arg0 : evalContext) (arg1 : arch) (arg2 : selectExpressionIR) (arg3 : evalContext) (arg4 : arch) (arg5 : transitionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × transitionResult)), SpecTecCall.ParserSelect_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserSelect_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserSelect_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserSelect_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserSelect_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserSelect_eval] unexpandRelationNotation
end Notation.ParserSelect_eval


noncomputable def ParserTransition_eval (arg0 : evalContext) (arg1 : arch) (arg2 : transitionStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : transitionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × transitionResult)), SpecTecCall.ParserTransition_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserTransition_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserTransition_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserTransition_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserTransition_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserTransition_eval] unexpandRelationNotation
end Notation.ParserTransition_eval


noncomputable def ParserState_eval (arg0 : evalContext) (arg1 : arch) (arg2 : parserStateIR) (arg3 : evalContext) (arg4 : arch) (arg5 : transitionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × transitionResult)), SpecTecCall.ParserState_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserState_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserState_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserState_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserState_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserState_eval] unexpandRelationNotation
end Notation.ParserState_eval


noncomputable def ParserState_trans (arg0 : evalContext) (arg1 : arch) (arg2 : nameIR) (arg3 : evalContext) (arg4 : arch) (arg5 : transitionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × transitionResult)), SpecTecCall.ParserState_trans arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserState_trans
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserState_trans arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserState_trans.relationNotation
        #[x0, x1, Lean.mkAtom "|-", Lean.mkAtom "TRANSITION", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " " TRANSITION " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserState_trans.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserState_trans] unexpandRelationNotation
end Notation.ParserState_trans


noncomputable def ParserLocalDecl_eval (arg0 : evalContext) (arg1 : arch) (arg2 : parserLocalDeclarationIR) (arg3 : evalContext) (arg4 : arch) (arg5 : parserDeclarationResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × parserDeclarationResult)), SpecTecCall.ParserLocalDecl_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserLocalDecl_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserLocalDecl_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserLocalDecl_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserLocalDecl_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserLocalDecl_eval] unexpandRelationNotation
end Notation.ParserLocalDecl_eval


noncomputable def ParserLocalDecls_eval (arg0 : evalContext) (arg1 : arch) (arg2 : (_root_.List parserLocalDeclarationIR)) (arg3 : evalContext) (arg4 : arch) (arg5 : parserDeclarationResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × parserDeclarationResult)), SpecTecCall.ParserLocalDecls_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ParserLocalDecls_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ParserLocalDecls_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ParserLocalDecls_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ParserLocalDecls_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ParserLocalDecls_eval] unexpandRelationNotation
end Notation.ParserLocalDecls_eval


noncomputable def Table_eval (arg0 : evalContext) (arg1 : arch) (arg2 : typeId) (arg3 : tableObjectProperty) (arg4 : evalContext) (arg5 : arch) (arg6 : tableResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × tableResult)), SpecTecCall.Table_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Table_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Table_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Table_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Table_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Table_eval] unexpandRelationNotation
end Notation.Table_eval


noncomputable def ControlBody_eval (arg0 : evalContext) (arg1 : arch) (arg2 : controlBodyIR) (arg3 : evalContext) (arg4 : arch) (arg5 : controlBodyResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × controlBodyResult)), SpecTecCall.ControlBody_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ControlBody_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ControlBody_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ControlBody_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ControlBody_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ControlBody_eval] unexpandRelationNotation
end Notation.ControlBody_eval


noncomputable def ControlLocalDecl_eval (arg0 : evalContext) (arg1 : arch) (arg2 : controlLocalDeclarationIR) (arg3 : evalContext) (arg4 : arch) (arg5 : controlLocalDeclarationResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × controlLocalDeclarationResult)), SpecTecCall.ControlLocalDecl_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ControlLocalDecl_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ControlLocalDecl_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ControlLocalDecl_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ControlLocalDecl_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ControlLocalDecl_eval] unexpandRelationNotation
end Notation.ControlLocalDecl_eval


noncomputable def ControlLocalDecls_eval (arg0 : evalContext) (arg1 : arch) (arg2 : (_root_.List controlLocalDeclarationIR)) (arg3 : evalContext) (arg4 : arch) (arg5 : controlLocalDeclarationResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × controlLocalDeclarationResult)), SpecTecCall.ControlLocalDecls_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ControlLocalDecls_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ControlLocalDecls_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ControlLocalDecls_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ControlLocalDecls_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ControlLocalDecls_eval] unexpandRelationNotation
end Notation.ControlLocalDecls_eval


noncomputable def VarDecl_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : variableDeclarationIR) (arg4 : evalContext) (arg5 : arch) (arg6 : declarationResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × declarationResult)), SpecTecCall.VarDecl_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.VarDecl_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.VarDecl_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.VarDecl_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.VarDecl_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.VarDecl_eval] unexpandRelationNotation
end Notation.VarDecl_eval


noncomputable def Callee_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : callableTargetIR) (arg4 : argumentListIR) (arg5 : evalContext) (arg6 : arch) (arg7 : calleeResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × calleeResult)), SpecTecCall.Callee_eval arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, (arg6, arg7))))) finalSupply

namespace Notation.Callee_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[9]⟩, ⟨stx[12]⟩, ⟨stx[13]⟩, ⟨stx[14]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Callee_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.Callee_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom "<", Lean.mkAtom "_", Lean.mkAtom ">", Lean.mkAtom "(", x4, Lean.mkAtom ")", Lean.mkAtom ":", x5, x6, x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " < " " _ " " > " " ( " term:51 " ) " " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Callee_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Callee_eval] unexpandRelationNotation
end Notation.Callee_eval


noncomputable def Copy_in_arg (arg0 : arch) (arg1 : cursor) (arg2 : evalContext) (arg3 : parameterIR) (arg4 : cursor) (arg5 : evalContext) (arg6 : argumentIR) (arg7 : arch) (arg8 : evalContext) (arg9 : evalContext) (arg10 : copyInArgumentResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(arch × (evalContext × (evalContext × copyInArgumentResult))), SpecTecCall.Copy_in_arg arg0 arg1 arg2 arg3 arg4 arg5 arg6⟩) 0 (.success (.of ((arg7, (arg8, (arg9, arg10)))))) finalSupply

namespace Notation.Copy_in_arg
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[10]⟩, ⟨stx[11]⟩, ⟨stx[12]⟩, ⟨stx[14]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_in_arg arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 $x10) =>
      pure (.node .none `SpecTec.Notation.Copy_in_arg.relationNotation
        #[x0, Lean.mkAtom "|-", x1, x2, x3, Lean.mkAtom "@", x4, x5, x6, Lean.mkAtom "~>", x7, x8, x9, Lean.mkAtom "#", x10])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_in_arg.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_in_arg] unexpandRelationNotation
end Notation.Copy_in_arg


noncomputable def Copy_in (arg0 : cursor) (arg1 : arch) (arg2 : cursor) (arg3 : evalContext) (arg4 : parameterListIR) (arg5 : cursor) (arg6 : evalContext) (arg7 : argumentListIR) (arg8 : arch) (arg9 : evalContext) (arg10 : evalContext) (arg11 : copyInResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(arch × (evalContext × (evalContext × copyInResult))), SpecTecCall.Copy_in arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7⟩) 0 (.success (.of ((arg8, (arg9, (arg10, arg11)))))) finalSupply

namespace Notation.Copy_in
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩, ⟨stx[11]⟩, ⟨stx[12]⟩, ⟨stx[13]⟩, ⟨stx[15]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Copy_in arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 $x10 $x11) =>
      pure (.node .none `SpecTec.Notation.Copy_in.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4, Lean.mkAtom "@", x5, x6, x7, Lean.mkAtom "~>", x8, x9, x10, Lean.mkAtom "#", x11])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:arg " @ " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " ~> " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.Copy_in.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Copy_in] unexpandRelationNotation
end Notation.Copy_in


noncomputable def Call_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : callee) (arg4 : typeArgumentListIR) (arg5 : argumentListIR) (arg6 : evalContext) (arg7 : arch) (arg8 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.Call_eval arg0 arg1 arg2 arg3 arg4 arg5⟩) 0 (.success (.of ((arg6, (arg7, arg8))))) finalSupply

namespace Notation.Call_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[7]⟩, ⟨stx[10]⟩, ⟨stx[13]⟩, ⟨stx[14]⟩, ⟨stx[15]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Call_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8) =>
      pure (.node .none `SpecTec.Notation.Call_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom "@", Lean.mkAtom "<", x4, Lean.mkAtom ">", Lean.mkAtom "(", x5, Lean.mkAtom ")", Lean.mkAtom ":", x6, x7, x8])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:arg " @ " " < " term:51 " > " " ( " term:51 " ) " " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Call_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Call_eval] unexpandRelationNotation
end Notation.Call_eval


noncomputable def Eval_keyset_simple (arg0 : evalContext) (arg1 : arch) (arg2 : simpleKeysetExpressionIR) (arg3 : evalContext) (arg4 : arch) (arg5 : simpleKeysetExpressionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × simpleKeysetExpressionResult)), SpecTecCall.Eval_keyset_simple arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.Eval_keyset_simple
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Eval_keyset_simple arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Eval_keyset_simple.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Eval_keyset_simple.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Eval_keyset_simple] unexpandRelationNotation
end Notation.Eval_keyset_simple


noncomputable def Eval_keysets_simple (arg0 : evalContext) (arg1 : arch) (arg2 : simpleKeysetExpressionListIR) (arg3 : evalContext) (arg4 : arch) (arg5 : keysetExpressionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × keysetExpressionResult)), SpecTecCall.Eval_keysets_simple arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.Eval_keysets_simple
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Eval_keysets_simple arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Eval_keysets_simple.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Eval_keysets_simple.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Eval_keysets_simple] unexpandRelationNotation
end Notation.Eval_keysets_simple


noncomputable def ForUpdateStmt_eval (arg0 : evalContext) (arg1 : arch) (arg2 : forUpdateStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.ForUpdateStmt_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ForUpdateStmt_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForUpdateStmt_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ForUpdateStmt_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForUpdateStmt_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForUpdateStmt_eval] unexpandRelationNotation
end Notation.ForUpdateStmt_eval


noncomputable def ForUpdateStmts_eval (arg0 : evalContext) (arg1 : arch) (arg2 : forUpdateStatementListIR) (arg3 : evalContext) (arg4 : arch) (arg5 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.ForUpdateStmts_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ForUpdateStmts_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForUpdateStmts_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ForUpdateStmts_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForUpdateStmts_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForUpdateStmts_eval] unexpandRelationNotation
end Notation.ForUpdateStmts_eval


noncomputable def ForInitStmt_eval (arg0 : evalContext) (arg1 : arch) (arg2 : forInitStatementIR) (arg3 : evalContext) (arg4 : arch) (arg5 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.ForInitStmt_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ForInitStmt_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForInitStmt_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ForInitStmt_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForInitStmt_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForInitStmt_eval] unexpandRelationNotation
end Notation.ForInitStmt_eval


noncomputable def ForInitStmts_eval (arg0 : evalContext) (arg1 : arch) (arg2 : forInitStatementListIR) (arg3 : evalContext) (arg4 : arch) (arg5 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.ForInitStmts_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ForInitStmts_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForInitStmts_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ForInitStmts_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForInitStmts_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForInitStmts_eval] unexpandRelationNotation
end Notation.ForInitStmts_eval


noncomputable def ForThreeClauseStmt_eval (arg0 : evalContext) (arg1 : arch) (arg2 : typedExpressionIR) (arg3 : statementIR) (arg4 : forUpdateStatementListIR) (arg5 : evalContext) (arg6 : arch) (arg7 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.ForThreeClauseStmt_eval arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, (arg6, arg7))))) finalSupply

namespace Notation.ForThreeClauseStmt_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForThreeClauseStmt_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.ForThreeClauseStmt_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4, Lean.mkAtom ":", x5, x6, x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForThreeClauseStmt_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForThreeClauseStmt_eval] unexpandRelationNotation
end Notation.ForThreeClauseStmt_eval


noncomputable def ForCollectionExpr_eval (arg0 : evalContext) (arg1 : arch) (arg2 : forCollectionExpressionIR) (arg3 : evalContext) (arg4 : arch) (arg5 : expressionListResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × expressionListResult)), SpecTecCall.ForCollectionExpr_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.ForCollectionExpr_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForCollectionExpr_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.ForCollectionExpr_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForCollectionExpr_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForCollectionExpr_eval] unexpandRelationNotation
end Notation.ForCollectionExpr_eval


noncomputable def ForInStmt_eval (arg0 : evalContext) (arg1 : arch) (arg2 : nameIR) (arg3 : (_root_.List value)) (arg4 : statementIR) (arg5 : evalContext) (arg6 : arch) (arg7 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.ForInStmt_eval arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, (arg6, arg7))))) finalSupply

namespace Notation.ForInStmt_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ForInStmt_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.ForInStmt_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4, Lean.mkAtom ":", x5, x6, x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.ForInStmt_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ForInStmt_eval] unexpandRelationNotation
end Notation.ForInStmt_eval


noncomputable def Switch_table_eval (arg0 : evalContext) (arg1 : arch) (arg2 : id) (arg3 : (_root_.List switchCaseIR)) (arg4 : evalContext) (arg5 : arch) (arg6 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.Switch_table_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Switch_table_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[5]⟩, ⟨stx[8]⟩, ⟨stx[11]⟩, ⟨stx[12]⟩, ⟨stx[13]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Switch_table_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Switch_table_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", Lean.mkAtom "SWITCH", Lean.mkAtom "(", x2, Lean.mkAtom ")", Lean.mkAtom "{", x3, Lean.mkAtom "}", Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " " SWITCH " " ( " term:51 " ) " " { " term:51 " } " " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Switch_table_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Switch_table_eval] unexpandRelationNotation
end Notation.Switch_table_eval


noncomputable def Switch_general_eval (arg0 : evalContext) (arg1 : arch) (arg2 : value) (arg3 : (_root_.List switchCaseIR)) (arg4 : evalContext) (arg5 : arch) (arg6 : statementResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × statementResult)), SpecTecCall.Switch_general_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.Switch_general_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[5]⟩, ⟨stx[8]⟩, ⟨stx[11]⟩, ⟨stx[12]⟩, ⟨stx[13]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Switch_general_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.Switch_general_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", Lean.mkAtom "SWITCH", Lean.mkAtom "(", x2, Lean.mkAtom ")", Lean.mkAtom "{", x3, Lean.mkAtom "}", Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " " SWITCH " " ( " term:51 " ) " " { " term:51 " } " " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.Switch_general_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Switch_general_eval] unexpandRelationNotation
end Notation.Switch_general_eval


noncomputable def SwitchLabel_general_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : switchLabelIR) (arg4 : evalContext) (arg5 : arch) (arg6 : expressionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × expressionResult)), SpecTecCall.SwitchLabel_general_eval arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.SwitchLabel_general_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchLabel_general_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.SwitchLabel_general_eval.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchLabel_general_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchLabel_general_eval] unexpandRelationNotation
end Notation.SwitchLabel_general_eval


noncomputable def SwitchCases_general_eval (arg0 : cursor) (arg1 : evalContext) (arg2 : arch) (arg3 : value) (arg4 : switchCaseListIR) (arg5 : evalContext) (arg6 : arch) (arg7 : (_root_.Option blockStatementIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × (_root_.Option blockStatementIR))), SpecTecCall.SwitchCases_general_eval arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of ((arg5, (arg6, arg7))))) finalSupply

namespace Notation.SwitchCases_general_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩, ⟨stx[9]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SwitchCases_general_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) =>
      pure (.node .none `SpecTec.Notation.SwitchCases_general_eval.relationNotation
        #[x0, x1, x2, x3, Lean.mkAtom "|-", x4, Lean.mkAtom ":", x5, x6, x7])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SwitchCases_general_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SwitchCases_general_eval] unexpandRelationNotation
end Notation.SwitchCases_general_eval


noncomputable def SelectCase_match (arg0 : evalContext) (arg1 : arch) (arg2 : (_root_.List value)) (arg3 : selectCaseIR) (arg4 : evalContext) (arg5 : arch) (arg6 : selectCaseMatchResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × selectCaseMatchResult)), SpecTecCall.SelectCase_match arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.SelectCase_match
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SelectCase_match arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.SelectCase_match.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SelectCase_match.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SelectCase_match] unexpandRelationNotation
end Notation.SelectCase_match


noncomputable def SelectCases_match (arg0 : evalContext) (arg1 : arch) (arg2 : (_root_.List value)) (arg3 : selectCaseListIR) (arg4 : evalContext) (arg5 : arch) (arg6 : selectCaseMatchResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × selectCaseMatchResult)), SpecTecCall.SelectCases_match arg0 arg1 arg2 arg3⟩) 0 (.success (.of ((arg4, (arg5, arg6))))) finalSupply

namespace Notation.SelectCases_match
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.SelectCases_match arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6) =>
      pure (.node .none `SpecTec.Notation.SelectCases_match.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom ":", x4, x5, x6])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.SelectCases_match.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.SelectCases_match] unexpandRelationNotation
end Notation.SelectCases_match


noncomputable def TableKey_eval (arg0 : evalContext) (arg1 : arch) (arg2 : tableKeyIR) (arg3 : evalContext) (arg4 : arch) (arg5 : tableKeyResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × tableKeyResult)), SpecTecCall.TableKey_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.TableKey_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableKey_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.TableKey_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableKey_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableKey_eval] unexpandRelationNotation
end Notation.TableKey_eval


noncomputable def TableKeys_eval (arg0 : evalContext) (arg1 : arch) (arg2 : tableKeyListIR) (arg3 : evalContext) (arg4 : arch) (arg5 : tableKeysResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × tableKeysResult)), SpecTecCall.TableKeys_eval arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.TableKeys_eval
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableKeys_eval arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.TableKeys_eval.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4, x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableKeys_eval.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableKeys_eval] unexpandRelationNotation
end Notation.TableKeys_eval

end SpecTec
