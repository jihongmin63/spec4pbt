import SpecTecDecl0432

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def Argument_eval_lctk (arg0 : cursor) (arg1 : typingContext) (arg2 : argumentIR) (arg3 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.Argument_eval_lctk arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.Argument_eval_lctk
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Argument_eval_lctk arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Argument_eval_lctk.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom "~>", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " ~> " term:51 : term
attribute [scoped macro SpecTec.Notation.Argument_eval_lctk.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Argument_eval_lctk] unexpandRelationNotation
end Notation.Argument_eval_lctk


noncomputable def Type_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : typeOrVoid) (arg3 : typeIR) (arg4 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeIR × (_root_.List typeId)), SpecTecCall.Type_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.Type_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Type_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Type_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, Lean.mkAtom "#", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.Type_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Type_ok] unexpandRelationNotation
end Notation.Type_ok


noncomputable def TypeArgument_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : typeArgument) (arg3 : typeArgumentIR) (arg4 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeArgumentIR × (_root_.List typeId)), SpecTecCall.TypeArgument_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TypeArgument_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TypeArgument_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TypeArgument_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, Lean.mkAtom "#", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.TypeArgument_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TypeArgument_ok] unexpandRelationNotation
end Notation.TypeArgument_ok


noncomputable def TypeArguments_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List typeArgument)) (arg3 : typeArgumentListIR) (arg4 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeArgumentListIR × (_root_.List typeId)), SpecTecCall.TypeArguments_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TypeArguments_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TypeArguments_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TypeArguments_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, Lean.mkAtom "#", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.TypeArguments_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TypeArguments_ok] unexpandRelationNotation
end Notation.TypeArguments_ok


noncomputable def TypeArgumentList_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : typeArgumentList) (arg3 : typeArgumentListIR) (arg4 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeArgumentListIR × (_root_.List typeId)), SpecTecCall.TypeArgumentList_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TypeArgumentList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TypeArgumentList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TypeArgumentList_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, Lean.mkAtom "#", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.TypeArgumentList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TypeArgumentList_ok] unexpandRelationNotation
end Notation.TypeArgumentList_ok


noncomputable def Expr_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : expression) (arg3 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.Expr_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.Expr_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Expr_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Expr_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Expr_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Expr_ok] unexpandRelationNotation
end Notation.Expr_ok


noncomputable def «Expr_ok:non-default:iter:3» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List expression)) (arg3 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«Expr_ok:non-default:iter:3» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Expr_ok:default:iter:4» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List expression)) (arg3 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«Expr_ok:default:iter:4» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Expr_ok:multiple-non-default:iter:8» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List expression)) (arg3 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«Expr_ok:multiple-non-default:iter:8» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Expr_ok:multiple-default:iter:8» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List expression)) (arg3 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«Expr_ok:multiple-default:iter:8» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def Argument_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : argument) (arg3 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.Argument_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.Argument_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Argument_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Argument_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Argument_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Argument_ok] unexpandRelationNotation
end Notation.Argument_ok


noncomputable def ArgumentList_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : argumentList) (arg3 : argumentListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentListIR, SpecTecCall.ArgumentList_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.ArgumentList_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.ArgumentList_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.ArgumentList_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.ArgumentList_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.ArgumentList_ok] unexpandRelationNotation
end Notation.ArgumentList_ok


noncomputable def «ArgumentList_ok:rule:iter:1» (arg0 : cursor) (arg1 : typingContext) (arg2 : (_root_.List argument)) (arg3 : (_root_.List argumentIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List argumentIR), SpecTecCall.«ArgumentList_ok:rule:iter:1» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def Lvalue_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : lvalue) (arg3 : typedLvalueIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedLvalueIR, SpecTecCall.Lvalue_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.Lvalue_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Lvalue_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.Lvalue_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Lvalue_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Lvalue_ok] unexpandRelationNotation
end Notation.Lvalue_ok


noncomputable def Call_convention_expr_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : actctxt) (arg3 : parameterIR) (arg4 : typedExpressionIR) (arg5 : typedExpressionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionIR, SpecTecCall.Call_convention_expr_ok arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of (arg5))) finalSupply

namespace Notation.Call_convention_expr_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Call_convention_expr_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Call_convention_expr_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom "@", x4, Lean.mkAtom ":", x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:arg " @ " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Call_convention_expr_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Call_convention_expr_ok] unexpandRelationNotation
end Notation.Call_convention_expr_ok


noncomputable def Call_convention_arg_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : actctxt) (arg3 : parameterIR) (arg4 : argumentIR) (arg5 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.Call_convention_arg_ok arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of (arg5))) finalSupply

namespace Notation.Call_convention_arg_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Call_convention_arg_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Call_convention_arg_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom "@", x4, Lean.mkAtom ":", x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:arg " @ " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Call_convention_arg_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Call_convention_arg_ok] unexpandRelationNotation
end Notation.Call_convention_arg_ok


noncomputable def Call_convention_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : actctxt) (arg3 : (_root_.List parameterIR)) (arg4 : argumentListIR) (arg5 : argumentListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentListIR, SpecTecCall.Call_convention_ok arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of (arg5))) finalSupply

namespace Notation.Call_convention_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Call_convention_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5) =>
      pure (.node .none `SpecTec.Notation.Call_convention_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom "@", x4, Lean.mkAtom ":", x5])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:arg " @ " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.Call_convention_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Call_convention_ok] unexpandRelationNotation
end Notation.Call_convention_ok


noncomputable def CallableTarget_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : callableTarget) (arg3 : callableTargetIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨callableTargetIR, SpecTecCall.CallableTarget_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.CallableTarget_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.CallableTarget_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.CallableTarget_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.CallableTarget_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.CallableTarget_ok] unexpandRelationNotation
end Notation.CallableTarget_ok


noncomputable def Call_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : callableTypeIR) (arg3 : typeArgumentListIR) (arg4 : (_root_.List typeId)) (arg5 : argumentListIR) (arg6 : (_root_.List id)) (arg7 : (_root_.List id)) (arg8 : typeIR) (arg9 : typeArgumentListIR) (arg10 : argumentListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeIR × (typeArgumentListIR × argumentListIR)), SpecTecCall.Call_ok arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7⟩) 0 (.success (.of ((arg8, (arg9, arg10))))) finalSupply

namespace Notation.Call_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩, ⟨stx[10]⟩, ⟨stx[12]⟩, ⟨stx[14]⟩, ⟨stx[17]⟩, ⟨stx[19]⟩, ⟨stx[22]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Call_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 $x10) =>
      pure (.node .none `SpecTec.Notation.Call_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom "<", x3, Lean.mkAtom "#", x4, Lean.mkAtom ">", Lean.mkAtom "(", x5, Lean.mkAtom "#", x6, Lean.mkAtom "#", x7, Lean.mkAtom ")", Lean.mkAtom ":", x8, Lean.mkAtom "<", x9, Lean.mkAtom ">", Lean.mkAtom "(", x10, Lean.mkAtom ")"])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " < " term:51 " # " term:51 " > " " ( " term:51 " # " term:51 " # " term:51 " ) " " : " term:51 " < " term:51 " > " " ( " term:51 " ) " : term
attribute [scoped macro SpecTec.Notation.Call_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Call_ok] unexpandRelationNotation
end Notation.Call_ok


noncomputable def Inst_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : instctxt) (arg3 : constructorTypeIR) (arg4 : typeArgumentListIR) (arg5 : (_root_.List typeId)) (arg6 : argumentListIR) (arg7 : (_root_.List id)) (arg8 : (_root_.List id)) (arg9 : typeIR) (arg10 : typeArgumentListIR) (arg11 : argumentListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typeIR × (typeArgumentListIR × argumentListIR)), SpecTecCall.Inst_ok arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8⟩) 0 (.success (.of ((arg9, (arg10, arg11))))) finalSupply

namespace Notation.Inst_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[2]⟩, ⟨stx[4]⟩, ⟨stx[6]⟩, ⟨stx[8]⟩, ⟨stx[11]⟩, ⟨stx[13]⟩, ⟨stx[15]⟩, ⟨stx[18]⟩, ⟨stx[20]⟩, ⟨stx[23]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Inst_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 $x10 $x11) =>
      pure (.node .none `SpecTec.Notation.Inst_ok.relationNotation
        #[x0, x1, x2, Lean.mkAtom "|-", x3, Lean.mkAtom "<", x4, Lean.mkAtom "#", x5, Lean.mkAtom ">", Lean.mkAtom "(", x6, Lean.mkAtom "#", x7, Lean.mkAtom "#", x8, Lean.mkAtom ")", Lean.mkAtom ":", x9, Lean.mkAtom "<", x10, Lean.mkAtom ">", Lean.mkAtom "(", x11, Lean.mkAtom ")"])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:arg ppSpace colGt term:51 " |- " term:51 " < " term:51 " # " term:51 " > " " ( " term:51 " # " term:51 " # " term:51 " ) " " : " term:51 " < " term:51 " > " " ( " term:51 " ) " : term
attribute [scoped macro SpecTec.Notation.Inst_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Inst_ok] unexpandRelationNotation
end Notation.Inst_ok


noncomputable def Parameter_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : parameter) (arg3 : parameterIR) (arg4 : (_root_.List typeId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(parameterIR × (_root_.List typeId)), SpecTecCall.Parameter_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.Parameter_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[7]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.Parameter_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.Parameter_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, Lean.mkAtom "#", x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 " # " term:51 : term
attribute [scoped macro SpecTec.Notation.Parameter_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.Parameter_ok] unexpandRelationNotation
end Notation.Parameter_ok


noncomputable def «ParserSelect_ok:rule:iter:1» (arg0 : typingContext) (arg1 : (_root_.List expression)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«ParserSelect_ok:rule:iter:1» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def TableKey_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : tableKey) (arg3 : tableContext) (arg4 : tableKeyIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableContext × tableKeyIR), SpecTecCall.TableKey_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableKey_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableKey_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableKey_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableKey_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableKey_ok] unexpandRelationNotation
end Notation.TableKey_ok


noncomputable def TableKeys_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : (_root_.List tableKey)) (arg3 : tableContext) (arg4 : tableKeyListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableContext × tableKeyListIR), SpecTecCall.TableKeys_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableKeys_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableKeys_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableKeys_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableKeys_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableKeys_ok] unexpandRelationNotation
end Notation.TableKeys_ok


noncomputable def Call_action_partial_ok (arg0 : typingContext) (arg1 : (_root_.List parameterIR)) (arg2 : argumentListIR) (arg3 : (_root_.List parameterIR)) (arg4 : (_root_.List parameterIR)) (arg5 : argumentListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List parameterIR) × ((_root_.List parameterIR) × argumentListIR)), SpecTecCall.Call_action_partial_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.Call_action_partial_ok
scoped notation:50 x0:51 " |- " x1:arg " @ " x2:51 " : " x3:51 " , " x4:arg " @ " x5:51 => _root_.SpecTec.Call_action_partial_ok x0 x1 x2 x3 x4 x5
end Notation.Call_action_partial_ok


noncomputable def TableAction_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : tableAction) (arg3 : tableContext) (arg4 : tableActionIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableContext × tableActionIR), SpecTecCall.TableAction_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableAction_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableAction_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableAction_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableAction_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableAction_ok] unexpandRelationNotation
end Notation.TableAction_ok


noncomputable def TableActions_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : (_root_.List tableAction)) (arg3 : tableContext) (arg4 : tableActionListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(tableContext × tableActionListIR), SpecTecCall.TableActions_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.TableActions_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableActions_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.TableActions_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.TableActions_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableActions_ok] unexpandRelationNotation
end Notation.TableActions_ok


noncomputable def Call_action_default_ok (arg0 : typingContext) (arg1 : (_root_.List parameterIR)) (arg2 : argumentListIR) (arg3 : (_root_.List parameterIR)) (arg4 : (_root_.List parameterIR)) (arg5 : argumentListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List parameterIR) × ((_root_.List parameterIR) × argumentListIR)), SpecTecCall.Call_action_default_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, (arg4, arg5))))) finalSupply

namespace Notation.Call_action_default_ok
scoped notation:50 x0:51 " |- " x1:arg " @ " x2:51 " : " x3:51 " , " x4:arg " @ " x5:51 => _root_.SpecTec.Call_action_default_ok x0 x1 x2 x3 x4 x5
end Notation.Call_action_default_ok


noncomputable def TableDefaultAction_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : initializer) (arg3 : tableActionReferenceIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableActionReferenceIR, SpecTecCall.TableDefaultAction_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.TableDefaultAction_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableDefaultAction_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.TableDefaultAction_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.TableDefaultAction_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableDefaultAction_ok] unexpandRelationNotation
end Notation.TableDefaultAction_ok


noncomputable def TableEntry_action_ok (arg0 : typingContext) (arg1 : tableContext) (arg2 : tableActionReference) (arg3 : tableActionReferenceIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableActionReferenceIR, SpecTecCall.TableEntry_action_ok arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.TableEntry_action_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.TableEntry_action_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.TableEntry_action_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.TableEntry_action_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.TableEntry_action_ok] unexpandRelationNotation
end Notation.TableEntry_action_ok


noncomputable def TableEntry_priority_ok (arg0 : typingContext) (arg1 : tableEntryPriority) (arg2 : tableEntryPriorityIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryPriorityIR, SpecTecCall.TableEntry_priority_ok arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.TableEntry_priority_ok
scoped notation:50 x0:51 " |- " x1:51 " : " x2:51 => _root_.SpecTec.TableEntry_priority_ok x0 x1 x2
end Notation.TableEntry_priority_ok


noncomputable def VarDecl_ok (arg0 : cursor) (arg1 : typingContext) (arg2 : variableDeclaration) (arg3 : typingContext) (arg4 : variableDeclarationIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(typingContext × variableDeclarationIR), SpecTecCall.VarDecl_ok arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.VarDecl_ok
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.VarDecl_ok arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.VarDecl_ok.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.VarDecl_ok.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.VarDecl_ok] unexpandRelationNotation
end Notation.VarDecl_ok

end SpecTec
