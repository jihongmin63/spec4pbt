import SpecTecDecl0439

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def PSA_ingress (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.PSA_ingress arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.PSA_ingress
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress] unexpandRelationNotation
end Notation.PSA_ingress


noncomputable def PSA_ingress_deparser (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.PSA_ingress_deparser arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.PSA_ingress_deparser
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_ingress_deparser arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_ingress_deparser.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_ingress_deparser.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_ingress_deparser] unexpandRelationNotation
end Notation.PSA_ingress_deparser


noncomputable def PSA_egress_init_packet_in (arg0 : evalContext) (arg1 : arch) (arg2 : objectState) (arg3 : evalContext) (arg4 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.PSA_egress_init_packet_in arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.PSA_egress_init_packet_in
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_init_packet_in arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_init_packet_in.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_init_packet_in.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_init_packet_in] unexpandRelationNotation
end Notation.PSA_egress_init_packet_in


noncomputable def PSA_egress_init_packet_out (arg0 : evalContext) (arg1 : arch) (arg2 : objectState) (arg3 : evalContext) (arg4 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × arch), SpecTecCall.PSA_egress_init_packet_out arg0 arg1 arg2⟩) 0 (.success (.of ((arg3, arg4)))) finalSupply

namespace Notation.PSA_egress_init_packet_out
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩, ⟨stx[6]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_init_packet_out arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_init_packet_out.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_init_packet_out.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_init_packet_out] unexpandRelationNotation
end Notation.PSA_egress_init_packet_out


noncomputable def PSA_egress_init_globals (arg0 : evalContext) (arg1 : arch) (arg2 : _root_.Int) (arg3 : evalContext) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨evalContext, SpecTecCall.PSA_egress_init_globals arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply

namespace Notation.PSA_egress_init_globals
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_init_globals arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_init_globals.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, Lean.mkAtom ":", x3])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:51 " : " term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_init_globals.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_init_globals] unexpandRelationNotation
end Notation.PSA_egress_init_globals


noncomputable def PSA_egress_parser (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : transitionResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × transitionResult)), SpecTecCall.PSA_egress_parser arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.PSA_egress_parser
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_parser arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_parser.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_parser.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_parser] unexpandRelationNotation
end Notation.PSA_egress_parser


noncomputable def PSA_egress (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.PSA_egress arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.PSA_egress
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_egress.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress] unexpandRelationNotation
end Notation.PSA_egress


noncomputable def PSA_egress_deparser (arg0 : evalContext) (arg1 : arch) (arg2 : evalContext) (arg3 : arch) (arg4 : callResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(evalContext × (arch × callResult)), SpecTecCall.PSA_egress_deparser arg0 arg1⟩) 0 (.success (.of ((arg2, (arg3, arg4))))) finalSupply

namespace Notation.PSA_egress_deparser
meta def expandRelationNotation : Lean.Macro := fun stx => do
  let arguments : Array (Lean.TSyntax `term) :=
    #[⟨stx[0]⟩, ⟨stx[1]⟩, ⟨stx[3]⟩, ⟨stx[4]⟩, ⟨stx[5]⟩]
  return (Lean.Syntax.mkCApp ``_root_.SpecTec.PSA_egress_deparser arguments).raw

def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander
  | `($f $x0 $x1 $x2 $x3 $x4) =>
      pure (.node .none `SpecTec.Notation.PSA_egress_deparser.relationNotation
        #[x0, x1, Lean.mkAtom "|-", x2, x3, x4])
  | _ => throw ()

scoped syntax:50 (name := relationNotation)
  term:arg ppSpace colGt term:51 " |- " term:arg ppSpace colGt term:arg ppSpace colGt term:51 : term
attribute [scoped macro SpecTec.Notation.PSA_egress_deparser.relationNotation] expandRelationNotation
attribute [scoped app_unexpander _root_.SpecTec.PSA_egress_deparser] unexpandRelationNotation
end Notation.PSA_egress_deparser

end SpecTec
