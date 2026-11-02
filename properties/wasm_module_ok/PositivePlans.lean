/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import properties.wasm_module_ok.PositiveCalls
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace properties.wasm_module_ok.PositiveRuntime
open SpecTec SpecTecExecution
instance emptySetDecidable {X : Type} (s : SpecTec.set X) :
    Decidable (SpecTec.set.«`{ % `}» [] = s) := by
  cases s with
  | «`{ % `}» xs =>
    cases xs with
    | nil => exact isTrue rfl
    | cons x xs => exact isFalse (by intro h; cases h)


def «$min_:clause:0» (input0 : _root_.Nat) (input1 : _root_.Nat) : ExecutablePlan Call _root_.Nat :=
  (let i : SpecTec.i := input0; (let j : SpecTec.j := input1; (.bind (.guard ((i ≤ j))) (fun (_ : Unit) => (.pure ((i : _root_.Nat)))))))

def «$min_:clause:1» (input0 : _root_.Nat) (input1 : _root_.Nat) : ExecutablePlan Call _root_.Nat :=
  (let i : SpecTec.i := input0; (let j : SpecTec.j := input1; (.pure ((j : _root_.Nat)))))

def «$min__clauses» (input0 : _root_.Nat) (input1 : _root_.Nat) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Nat) :=
  [fun (_ : _root_.Unit) => («$min_:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$min_:clause:1»  input0 input1)]

def «$rev_:clause:0» (X : Type) (input0 : (_root_.List X)) : ExecutablePlan Call (_root_.List X) :=
  (let «X*» : (_root_.List X) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List X)) : (_root_.List X)))))))

def «$rev_:clause:1» (X : Type) (input0 : (_root_.List X)) : ExecutablePlan Call (_root_.List X) :=
  (let «X*» : (_root_.List X) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «X*» with | «exec:2» :: «exec:1» => (let X_h : X := «exec:2»; (let «X_t*» : (_root_.List X) := «exec:1»; (.bind (.call (Call.«$rev_» X «X_t*»)) (fun («exec:3» : (_root_.List X)) => (let «eval:0» : (_root_.List X) := «exec:3»; (.pure (((«eval:0» ++ ([X_h] : (_root_.List X))) : (_root_.List X))))))))) | [] => .unmatch))))

def «$rev__clauses» (X : Type) (input0 : (_root_.List X)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List X)) :=
  [fun (_ : _root_.Unit) => («$rev_:clause:0» X input0), fun (_ : _root_.Unit) => («$rev_:clause:1» X input0)]

def «$make_:clause:0» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) : ExecutablePlan Call (_root_.List X_T) :=
  (let X : X_T := input0; (let n : SpecTec.n := input1; (.bind (.guard ((0 : _root_.Nat) = n)) (fun (_ : Unit) => (.pure ((([] : (_root_.List X_T)) : (_root_.List X_T))))))))

def «$make_:clause:1» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) : ExecutablePlan Call (_root_.List X_T) :=
  (let X : X_T := input0; (let n : SpecTec.n := input1; (.bind (.guard ((n > (0 : _root_.Nat)))) (fun (_ : Unit) => (let int : _root_.Int := ((_root_.Int.ofNat n) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:1» => (let «eval:0» : SpecTec.n := «exec:1»; (let n' : SpecTec.n := «eval:0»; (.bind (.call (Call.«$make_» X_T X n')) (fun («exec:2» : (_root_.List X_T)) => (let «eval:1» : (_root_.List X_T) := «exec:2»; (.pure (((«eval:1» ++ ([X] : (_root_.List X_T))) : (_root_.List X_T))))))))) | none => .unmatch))))))))

def «$make__clauses» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List X_T)) :=
  [fun (_ : _root_.Unit) => («$make_:clause:0» X_T input0 input1), fun (_ : _root_.Unit) => («$make_:clause:1» X_T input0 input1)]

def «$empty_set:clause:0» (K : Type)  : ExecutablePlan Call (set K) :=
  (.pure (((@set.«`{ % `}» K ([] : (_root_.List K))) : (set K))))

def «$empty_set_clauses» (K : Type) : List (ExecutablePlan.Clause Call _root_.Unit (set K)) :=
  [fun (_ : _root_.Unit) => («$empty_set:clause:0» K )]

def «$in_set:clause:0» (K_T : Type) [_root_.DecidableEq K_T] (input0 : K_T) (input1 : (set K_T)) : ExecutablePlan Call _root_.Bool :=
  (let K : K_T := input0; (match input1 with | .«`{ % `}» «exec:1» => (let «K'*» : (_root_.List K_T) := «exec:1»; (.pure (((_root_.Decidable.decide (K ∈ «K'*»)) : _root_.Bool))))))

def «$in_set_clauses» (K_T : Type) [_root_.DecidableEq K_T] (input0 : K_T) (input1 : (set K_T)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$in_set:clause:0» K_T input0 input1)]

def «$map_set:clause:0» (X : Type) (Y : Type) [specTecCompare_0 : _root_.SpecTecCompareKey Y] (input0 : (X → (Call Y))) (input1 : (set X)) : ExecutablePlan Call (set Y) :=
  (let «$f» : (X → (Call Y)) := input0; (let «set<X>» : (set X) := input1; (.bind (.guard ((@set.«`{ % `}» X ([] : (_root_.List X))) = «set<X>»)) (fun (_ : Unit) => (.pure (((@set.«`{ % `}» Y ([] : (_root_.List Y))) : (set Y))))))))

def «$map_set:clause:1» (X : Type) (Y : Type) [specTecCompare_0 : _root_.SpecTecCompareKey Y] (input0 : (X → (Call Y))) (input1 : (set X)) : ExecutablePlan Call (set Y) :=
  (let «$f» : (X → (Call Y)) := input0; (match input1 with | .«`{ % `}» «exec:1» => (let «X*» : (_root_.List X) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «X*» with | «exec:3» :: «exec:2» => (let X_h : X := «exec:3»; (let «X_t*» : (_root_.List X) := «exec:2»; (.bind (.call («$f» X_h)) (fun («exec:4» : Y) => (let «eval:0» : Y := «exec:4»; (.bind (.call (Call.«$map_set» X Y (specTecCompare_0 := (inferInstance : _root_.SpecTecCompareKey Y)) «$f» (@set.«`{ % `}» X «X_t*»))) (fun («exec:5» : (set Y)) => (let «eval:1» : (set Y) := «exec:5»; (.pure (((@«$union_set» Y (inferInstance : _root_.SpecTecCompareKey Y) (@set.«`{ % `}» Y ([«eval:0»] : (_root_.List Y))) «eval:1») : (set Y)))))))))))) | [] => .unmatch))))))

def «$map_set_clauses» (X : Type) (Y : Type) [specTecCompare_0 : _root_.SpecTecCompareKey Y] (input0 : (X → (Call Y))) (input1 : (set X)) : List (ExecutablePlan.Clause Call _root_.Unit (set Y)) :=
  [fun (_ : _root_.Unit) => («$map_set:clause:0» X Y input0 input1), fun (_ : _root_.Unit) => («$map_set:clause:1» X Y input0 input1)]

def «$range:clause:0» (input0 : _root_.Nat) : ExecutablePlan Call (_root_.List _root_.Nat) :=
  (let nat : _root_.Nat := input0; (.bind (.guard ((0 : _root_.Nat) = nat)) (fun (_ : Unit) => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))))))

def «$range:clause:1» (input0 : _root_.Nat) : ExecutablePlan Call (_root_.List _root_.Nat) :=
  (let n : SpecTec.n := input0; (.bind (.guard ((n > (0 : _root_.Nat)))) (fun (_ : Unit) => (let int : _root_.Int := ((_root_.Int.ofNat n) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:1» => (let «eval:0» : SpecTec.n := «exec:1»; (let n' : SpecTec.n := «eval:0»; (.bind (.call (Call.«$range» n')) (fun («exec:2» : (_root_.List _root_.Nat)) => (let «eval:1» : (_root_.List _root_.Nat) := «exec:2»; (.pure (((«eval:1» ++ ([n'] : (_root_.List SpecTec.n))) : (_root_.List _root_.Nat))))))))) | none => .unmatch)))))))

def «$range_clauses» (input0 : _root_.Nat) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List _root_.Nat)) :=
  [fun (_ : _root_.Unit) => («$range:clause:0»  input0), fun (_ : _root_.Unit) => («$range:clause:1»  input0)]

def «$rolldt':clause:0» (input0 : _root_.Nat) (input1 : rectype) : ExecutablePlan Call (_root_.List deftype) :=
  (let i : SpecTec.i := input0; (let rect : rectype := input1; (match rect with | .RecT «exec:1» => (let «st*» : (_root_.List subtype) := «exec:1»; (.bind (.guard ((i < (_root_.List.length «st*»)))) (fun (_ : Unit) => (.bind (.call (Call.«$rolldt'» (i + (1 : _root_.Nat)) rect)) (fun («exec:2» : (_root_.List deftype)) => (let «eval:0» : (_root_.List deftype) := «exec:2»; (.pure ((((@deftype.DefT rect i) :: «eval:0») : (_root_.List deftype)))))))))))))

def «$rolldt':clause:1» (input0 : _root_.Nat) (input1 : rectype) : ExecutablePlan Call (_root_.List deftype) :=
  (let i : SpecTec.i := input0; (let rect : rectype := input1; (.pure ((([] : (_root_.List deftype)) : (_root_.List deftype))))))

def «$rolldt'_clauses» (input0 : _root_.Nat) (input1 : rectype) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List deftype)) :=
  [fun (_ : _root_.Unit) => («$rolldt':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$rolldt':clause:1»  input0 input1)]

def «$min_addrtype:clause:0» (input0 : addrtype) (input1 : addrtype) : ExecutablePlan Call addrtype :=
  (let at_1 : addrtype := input0; (let at_2 : addrtype := input1; (.bind (.guard (((at_1 = (@addrtype.I64AT)) ∧ (at_2 = (@addrtype.I64AT))))) (fun (_ : Unit) => (.pure (((@addrtype.I64AT) : addrtype)))))))

def «$min_addrtype:clause:1» (input0 : addrtype) (input1 : addrtype) : ExecutablePlan Call addrtype :=
  (let at_1 : addrtype := input0; (let at_2 : addrtype := input1; (.pure (((@addrtype.I32AT) : addrtype)))))

def «$min_addrtype_clauses» (input0 : addrtype) (input1 : addrtype) : List (ExecutablePlan.Clause Call _root_.Unit addrtype) :=
  [fun (_ : _root_.Unit) => («$min_addrtype:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$min_addrtype:clause:1»  input0 input1)]

def «$num_size:clause:0» (input0 : numtype) : ExecutablePlan Call _root_.Int :=
  (let nt : numtype := input0; (.bind (.guard (((nt = (@numtype.I32T)) ∨ (nt = (@numtype.F32T))))) (fun (_ : Unit) => (.pure (((_root_.Int.ofNat (4 : _root_.Nat)) : _root_.Int))))))

def «$num_size:clause:1» (input0 : numtype) : ExecutablePlan Call _root_.Int :=
  (let nt : numtype := input0; (.bind (.guard (((nt = (@numtype.I64T)) ∨ (nt = (@numtype.F64T))))) (fun (_ : Unit) => (.pure (((_root_.Int.ofNat (8 : _root_.Nat)) : _root_.Int))))))

def «$num_size_clauses» (input0 : numtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Int) :=
  [fun (_ : _root_.Unit) => («$num_size:clause:0»  input0), fun (_ : _root_.Unit) => («$num_size:clause:1»  input0)]

def «$vec_size:clause:0» (input0 : vectype) : ExecutablePlan Call _root_.Int :=
  (let vt : vectype := input0; (.bind (.guard ((@vectype.V128T) = vt)) (fun (_ : Unit) => (.pure (((_root_.Int.ofNat (16 : _root_.Nat)) : _root_.Int))))))

def «$vec_size_clauses» (input0 : vectype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Int) :=
  [fun (_ : _root_.Unit) => («$vec_size:clause:0»  input0)]

def «$type_vecop:clause:0» (A : Type) (input0 : (vecop A)) : ExecutablePlan Call vectype :=
  (match input0 with | .V128 «exec:1» => (let _A : A := «exec:1»; (.pure (((@vectype.V128T) : vectype)))))

def «$type_vecop_clauses» (A : Type) (input0 : (vecop A)) : List (ExecutablePlan.Clause Call _root_.Unit vectype) :=
  [fun (_ : _root_.Unit) => («$type_vecop:clause:0» A input0)]

def «$free_empty:clause:0»  : ExecutablePlan Call free :=
  (.bind (.call (Call.«$empty_set» typeidx)) (fun («exec:1» : (set typeidx)) => (let «eval:0» : (set typeidx) := «exec:1»; (.bind (.call (Call.«$empty_set» globalidx)) (fun («exec:2» : (set globalidx)) => (let «eval:1» : (set globalidx) := «exec:2»; (.bind (.call (Call.«$empty_set» tableidx)) (fun («exec:3» : (set tableidx)) => (let «eval:2» : (set tableidx) := «exec:3»; (.bind (.call (Call.«$empty_set» memidx)) (fun («exec:4» : (set memidx)) => (let «eval:3» : (set memidx) := «exec:4»; (.bind (.call (Call.«$empty_set» tagidx)) (fun («exec:5» : (set tagidx)) => (let «eval:4» : (set tagidx) := «exec:5»; (.bind (.call (Call.«$empty_set» funcidx)) (fun («exec:6» : (set funcidx)) => (let «eval:5» : (set funcidx) := «exec:6»; (.bind (.call (Call.«$empty_set» elemidx)) (fun («exec:7» : (set elemidx)) => (let «eval:6» : (set elemidx) := «exec:7»; (.bind (.call (Call.«$empty_set» dataidx)) (fun («exec:8» : (set dataidx)) => (let «eval:7» : (set dataidx) := «exec:8»; (.bind (.call (Call.«$empty_set» localidx)) (fun («exec:9» : (set localidx)) => (let «eval:8» : (set localidx) := «exec:9»; (.bind (.call (Call.«$empty_set» labelidx)) (fun («exec:10» : (set labelidx)) => (let «eval:9» : (set labelidx) := «exec:10»; (.pure ((({ TYPES := «eval:0», GLOBALS := «eval:1», TABLES := «eval:2», MEMS := «eval:3», TAGS := «eval:4», FUNCS := «eval:5», ELEMS := «eval:6», DATAS := «eval:7», LOCALS := «eval:8», LABELS := «eval:9» } : free) : free)))))))))))))))))))))))))))))))))

def «$free_empty_clauses» : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_empty:clause:0»  )]

def «$fold_left:clause:0» (X_T : Type) (Y : Type) (input0 : (X_T → Y → (Call X_T))) (input1 : X_T) (input2 : (_root_.List Y)) : ExecutablePlan Call X_T :=
  (let «$f» : (X_T → Y → (Call X_T)) := input0; (let X : X_T := input1; (let «Y*» : (_root_.List Y) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «Y*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((X : X_T))))))))

def «$fold_left:clause:1» (X_T : Type) (Y : Type) (input0 : (X_T → Y → (Call X_T))) (input1 : X_T) (input2 : (_root_.List Y)) : ExecutablePlan Call X_T :=
  (let «$f» : (X_T → Y → (Call X_T)) := input0; (let X : X_T := input1; (let «Y*» : (_root_.List Y) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «Y*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «Y*» with | «exec:2» :: «exec:1» => (let Y_h : Y := «exec:2»; (let «Y_t*» : (_root_.List Y) := «exec:1»; (.bind (.call («$f» X Y_h)) (fun («exec:3» : X_T) => (let «eval:0» : X_T := «exec:3»; (.bind (.call (Call.«$fold_left» X_T Y «$f» «eval:0» «Y_t*»)) (fun («exec:4» : X_T) => (let «eval:1» : X_T := «exec:4»; (.pure ((«eval:1» : X_T))))))))))) | [] => .unmatch))))))

def «$fold_left_clauses» (X_T : Type) (Y : Type) (input0 : (X_T → Y → (Call X_T))) (input1 : X_T) (input2 : (_root_.List Y)) : List (ExecutablePlan.Clause Call _root_.Unit X_T) :=
  [fun (_ : _root_.Unit) => («$fold_left:clause:0» X_T Y input0 input1 input2), fun (_ : _root_.Unit) => («$fold_left:clause:1» X_T Y input0 input1 input2)]

def «$free_union:clause:0» (input0 : free) (input1 : free) : ExecutablePlan Call free :=
  (let free_1 : free := input0; (let free_2 : free := input1; (.pure ((({ TYPES := (@«$union_set» typeidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.TYPES free_1) (free.TYPES free_2)), GLOBALS := (@«$union_set» globalidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.GLOBALS free_1) (free.GLOBALS free_2)), TABLES := (@«$union_set» tableidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.TABLES free_1) (free.TABLES free_2)), MEMS := (@«$union_set» memidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.MEMS free_1) (free.MEMS free_2)), TAGS := (@«$union_set» tagidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.TAGS free_1) (free.TAGS free_2)), FUNCS := (@«$union_set» funcidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.FUNCS free_1) (free.FUNCS free_2)), ELEMS := (@«$union_set» elemidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.ELEMS free_1) (free.ELEMS free_2)), DATAS := (@«$union_set» dataidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.DATAS free_1) (free.DATAS free_2)), LOCALS := (@«$union_set» localidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.LOCALS free_1) (free.LOCALS free_2)), LABELS := (@«$union_set» labelidx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (free.LABELS free_1) (free.LABELS free_2)) } : free) : free)))))

def «$free_union_clauses» (input0 : free) (input1 : free) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_union:clause:0»  input0 input1)]

def «$free_unions:clause:0» (input0 : (_root_.List free)) : ExecutablePlan Call free :=
  (let «free*» : (_root_.List free) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «free*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_unions:clause:1» (input0 : (_root_.List SpecTec.free)) : ExecutablePlan Call free :=
  (let «free''*» : (_root_.List SpecTec.free) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «free''*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «free''*» with | «exec:2» :: «exec:1» => (let free_h : SpecTec.free := «exec:2»; (let «free_t*» : (_root_.List SpecTec.free) := «exec:1»; (.bind (.call (Call.«$free_unions» «free_t*»)) (fun («exec:3» : SpecTec.free) => (let «eval:0» : SpecTec.free := «exec:3»; (let free' : SpecTec.free := «eval:0»; (.bind (.call (Call.«$free_union» free_h free')) (fun («exec:4» : SpecTec.free) => (let «eval:1» : SpecTec.free := «exec:4»; (let free : SpecTec.free := «eval:1»; (.pure ((free : SpecTec.free))))))))))))) | [] => .unmatch))))

def «$free_unions_clauses» (input0 : (_root_.List free)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_unions:clause:0»  input0), fun (_ : _root_.Unit) => («$free_unions:clause:1»  input0)]

def «$add_minus_one:clause:0» (input0 : idx) : ExecutablePlan Call idx :=
  (let x : idx := input0; (let int : _root_.Int := ((_root_.Int.ofNat x) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:1» => (let «eval:0» : idx := «exec:1»; (let x' : idx := «eval:0»; (.pure ((x' : idx))))) | none => .unmatch)))))

def «$add_minus_one_clauses» (input0 : idx) : List (ExecutablePlan.Clause Call _root_.Unit idx) :=
  [fun (_ : _root_.Unit) => («$add_minus_one:clause:0»  input0)]

def «$free_idx:clause:0» (input0 : idx) : ExecutablePlan Call (set idx) :=
  (let x : idx := input0; (.pure (((@set.«`{ % `}» idx ([x] : (_root_.List idx))) : (set idx)))))

def «$free_idx_clauses» (input0 : idx) : List (ExecutablePlan.Clause Call _root_.Unit (set idx)) :=
  [fun (_ : _root_.Unit) => («$free_idx:clause:0»  input0)]

def «$free_shift:clause:0» (input0 : (set idx)) : ExecutablePlan Call (set idx) :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (match (@«$diff_set» idx (inferInstance : _root_.SpecTecCompareKey _root_.Nat) (@set.«`{ % `}» idx «x*») (@set.«`{ % `}» idx ([(0 : _root_.Nat)] : (_root_.List _root_.Nat)))) with | .«`{ % `}» «exec:2» => (let «x'*» : (_root_.List idx) := «exec:2»; (.bind (.call (Call.«$map_set» idx idx (specTecCompare_0 := (inferInstance : _root_.SpecTecCompareKey _root_.Nat)) Call.«$add_minus_one» (@set.«`{ % `}» idx «x'*»))) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (match «eval:0» with | .«`{ % `}» «exec:4» => (let «x''*» : (_root_.List idx) := «exec:4»; (.pure (((@set.«`{ % `}» idx «x''*») : (set idx)))))))))))))

def «$free_shift_clauses» (input0 : (set idx)) : List (ExecutablePlan.Clause Call _root_.Unit (set idx)) :=
  [fun (_ : _root_.Unit) => («$free_shift:clause:0»  input0)]

def «$free_list:clause:0» (X : Type) (input0 : (X → (Call free))) (input1 : (_root_.List X)) : ExecutablePlan Call free :=
  (let «$free_» : (X → (Call free)) := input0; (let «X*» : (_root_.List X) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free))))))))))

def «$free_list:clause:1» (X : Type) (input0 : (X → (Call free))) (input1 : (_root_.List X)) : ExecutablePlan Call free :=
  (let «$free_» : (X → (Call free)) := input0; (let «X*» : (_root_.List X) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «X*» with | «exec:2» :: «exec:1» => (let X_h : X := «exec:2»; (let «X_t*» : (_root_.List X) := «exec:1»; (.bind (.call («$free_» X_h)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.bind (.call (Call.«$free_list» X «$free_» «X_t*»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$fold_left» free free Call.«$free_union» «eval:0» ([«eval:1»] : (_root_.List free)))) (fun («exec:5» : free) => (let «eval:2» : free := «exec:5»; (.pure ((«eval:2» : free)))))))))))))) | [] => .unmatch)))))

def «$free_list_clauses» (X : Type) (input0 : (X → (Call free))) (input1 : (_root_.List X)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_list:clause:0» X input0 input1), fun (_ : _root_.Unit) => («$free_list:clause:1» X input0 input1)]

def «$free_opt:clause:0» (X_T : Type) (input0 : (X_T → (Call free))) (input1 : (_root_.Option X_T)) : ExecutablePlan Call free :=
  (let «$free_» : (X_T → (Call free)) := input0; (let X? : (_root_.Option X_T) := input1; (.bind (.guard (((_root_.Option.isNone X?) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free))))))))))

def «$free_opt:clause:1» (X_T : Type) (input0 : (X_T → (Call free))) (input1 : (_root_.Option X_T)) : ExecutablePlan Call free :=
  (let «$free_» : (X_T → (Call free)) := input0; (let X'? : (_root_.Option X_T) := input1; (.bind (.guard (((_root_.Option.isSome X'?) = true))) (fun (_ : Unit) => (match X'? with | some «exec:1» => (let X : X_T := «exec:1»; (.bind (.call («$free_» X)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | none => .unmatch)))))

def «$free_opt_clauses» (X_T : Type) (input0 : (X_T → (Call free))) (input1 : (_root_.Option X_T)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_opt:clause:0» X_T input0 input1), fun (_ : _root_.Unit) => («$free_opt:clause:1» X_T input0 input1)]

def «$free_packtype:clause:0» (input0 : packtype) : ExecutablePlan Call free :=
  (let pt : packtype := input0; (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_packtype_clauses» (input0 : packtype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_packtype:clause:0»  input0)]

def «$free_numtype:clause:0» (input0 : numtype) : ExecutablePlan Call free :=
  (let nt : numtype := input0; (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_numtype_clauses» (input0 : numtype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_numtype:clause:0»  input0)]

def «$free_vectype:clause:0» (input0 : vectype) : ExecutablePlan Call free :=
  (let vt : vectype := input0; (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_vectype_clauses» (input0 : vectype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_vectype:clause:0»  input0)]

def «$update_types:clause:0» (input0 : (set typeidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with TYPES := (@set.«`{ % `}» typeidx «x*») } : free) : free))))))))

def «$update_types_clauses» (input0 : (set typeidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_types:clause:0»  input0)]

def «$update_globals:clause:0» (input0 : (set globalidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with GLOBALS := (@set.«`{ % `}» globalidx «x*») } : free) : free))))))))

def «$update_globals_clauses» (input0 : (set globalidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_globals:clause:0»  input0)]

def «$update_tables:clause:0» (input0 : (set tableidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with TABLES := (@set.«`{ % `}» tableidx «x*») } : free) : free))))))))

def «$update_tables_clauses» (input0 : (set tableidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_tables:clause:0»  input0)]

def «$update_mems:clause:0» (input0 : (set memidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with MEMS := (@set.«`{ % `}» memidx «x*») } : free) : free))))))))

def «$update_mems_clauses» (input0 : (set memidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_mems:clause:0»  input0)]

def «$update_tags:clause:0» (input0 : (set tagidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with TAGS := (@set.«`{ % `}» tagidx «x*») } : free) : free))))))))

def «$update_tags_clauses» (input0 : (set tagidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_tags:clause:0»  input0)]

def «$update_funcs:clause:0» (input0 : (set funcidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with FUNCS := (@set.«`{ % `}» funcidx «x*») } : free) : free))))))))

def «$update_funcs_clauses» (input0 : (set funcidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_funcs:clause:0»  input0)]

def «$free_start:clause:0» (input0 : SpecTec.start) : ExecutablePlan Call free :=
  (let start : SpecTec.start := input0; (.bind (.call (Call.«$update_funcs» (@set.«`{ % `}» funcidx ([(SpecTec.start.SFUNC start)] : (_root_.List funcidx))))) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_start_clauses» (input0 : start) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_start:clause:0»  input0)]

def «$update_elems:clause:0» (input0 : (set elemidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with ELEMS := (@set.«`{ % `}» elemidx «x*») } : free) : free))))))))

def «$update_elems_clauses» (input0 : (set elemidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_elems:clause:0»  input0)]

def «$update_datas:clause:0» (input0 : (set dataidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with DATAS := (@set.«`{ % `}» dataidx «x*») } : free) : free))))))))

def «$update_datas_clauses» (input0 : (set dataidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_datas:clause:0»  input0)]

def «$update_locals:clause:0» (input0 : (set localidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with LOCALS := (@set.«`{ % `}» localidx «x*») } : free) : free))))))))

def «$update_locals_clauses» (input0 : (set localidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_locals:clause:0»  input0)]

def «$update_labels:clause:0» (input0 : (set labelidx)) : ExecutablePlan Call free :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((({ «eval:0» with LABELS := (@set.«`{ % `}» labelidx «x*») } : free) : free))))))))

def «$update_labels_clauses» (input0 : (set labelidx)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_labels:clause:0»  input0)]

def «$update_label:clause:0» (input0 : idx) : ExecutablePlan Call free :=
  (let x : idx := input0; (.bind (.call (Call.«$free_idx» x)) (fun («exec:1» : (set idx)) => (let «eval:0» : (set idx) := «exec:1»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:2» : free) => (let «eval:1» : free := «exec:2»; (.pure ((«eval:1» : free))))))))))

def «$update_label_clauses» (input0 : idx) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$update_label:clause:0»  input0)]

def «$free_memtype:clause:0» (input0 : memtype) : ExecutablePlan Call free :=
  (match input0 with | .MemoryT «exec:1» «exec:2» => (let _at : addrtype := «exec:1»; (let _lim : limits := «exec:2»; (.bind (.call (Call.«$free_empty»)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.pure ((«eval:0» : free)))))))))

def «$free_memtype_clauses» (input0 : memtype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_memtype:clause:0»  input0)]

def «$free_mem:clause:0» (input0 : memory) : ExecutablePlan Call free :=
  (let mt : memtype := (input0).MTYPE; (.bind (.call (Call.«$free_memtype» mt)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_mem_clauses» (input0 : memory) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_mem:clause:0»  input0)]

def «$match_numtype:clause:0» (input0 : (_root_.List deftype)) (input1 : numtype) (input2 : numtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let nt_1 : numtype := input1; (let nt_2 : numtype := input2; (.bind (.guard (nt_2 = nt_1)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))

def «$match_numtype:clause:1» (input0 : (_root_.List deftype)) (input1 : numtype) (input2 : numtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let nt_1 : numtype := input1; (let nt_2 : numtype := input2; (.pure ((false : _root_.Bool))))))

def «$match_numtype_clauses» (input0 : (_root_.List deftype)) (input1 : numtype) (input2 : numtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_numtype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_numtype:clause:1»  input0 input1 input2)]

def «$match_vectype:clause:0» (input0 : (_root_.List deftype)) (input1 : vectype) (input2 : vectype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let vt_1 : vectype := input1; (let vt_2 : vectype := input2; (.pure (((_root_.Decidable.decide (vt_1 = vt_2)) : _root_.Bool))))))

def «$match_vectype_clauses» (input0 : (_root_.List deftype)) (input1 : vectype) (input2 : vectype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_vectype:clause:0»  input0 input1 input2)]

def «$match_packtype:clause:0» (input0 : (_root_.List deftype)) (input1 : packtype) (input2 : packtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let pt_1 : packtype := input1; (let pt_2 : packtype := input2; (.pure (((_root_.Decidable.decide (pt_1 = pt_2)) : _root_.Bool))))))

def «$match_packtype_clauses» (input0 : (_root_.List deftype)) (input1 : packtype) (input2 : packtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_packtype:clause:0»  input0 input1 input2)]

def «$empty_context:clause:0»  : ExecutablePlan Call context :=
  (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((({ TYPES := ([] : (_root_.List deftype)), FUNCS := ([] : (_root_.List deftype)), TABLES := ([] : (_root_.List tabletype)), MEMS := ([] : (_root_.List memtype)), TAGS := ([] : (_root_.List tagtype)), GLOBALS := ([] : (_root_.List globaltype)), ELEMS := ([] : (_root_.List elemtype)), DATAS := ([] : (_root_.List datatype)), LOCALS := ([] : (_root_.List localtype)), RESULTS := ([] : (_root_.List valtype)), LABELS := ([] : (_root_.List resulttype)), REFS := «eval:0» } : context) : context))))))

def «$empty_context_clauses» : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («$empty_context:clause:0»  )]

def «$stack:clause:0» (input0 : SpecTec.resulttype) : ExecutablePlan Call (ellipses × resulttype) :=
  (let resulttype : SpecTec.resulttype := input0; (.pure ((((@ellipses.NoEllipses), resulttype) : (ellipses × SpecTec.resulttype)))))

def «$stack_clauses» (input0 : resulttype) : List (ExecutablePlan.Clause Call _root_.Unit (ellipses × resulttype)) :=
  [fun (_ : _root_.Unit) => («$stack:clause:0»  input0)]

def «$peek:clause:0» (input0 : _root_.Nat) (input1 : inferresulttype) : ExecutablePlan Call valtype :=
  (let n : SpecTec.n := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t*» : (_root_.List valtype) := (input1).2; (.bind (.guard ((n < (_root_.List.length «t*»)))) (fun (_ : Unit) => (.bind (.call (Call.«$rev_» valtype «t*»)) (fun («exec:1» : (_root_.List valtype)) => (let «eval:0» : (_root_.List valtype) := «exec:1»; (.bind (.guard ((n < (_root_.List.length «eval:0»)))) (fun (_ : Unit) => (.bind (.call (Call.«$rev_» valtype «t*»)) (fun («exec:2» : (_root_.List valtype)) => (let «eval:1» : (_root_.List valtype) := «exec:2»; (match («eval:1»[n]?) with | some «exec:3» => (let «eval:2» : valtype := «exec:3»; (.pure ((«eval:2» : valtype)))) | none => .unmatch))))))))))))))

def «$peek:clause:1» (input0 : _root_.Nat) (input1 : inferresulttype) : ExecutablePlan Call valtype :=
  (let n : SpecTec.n := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t*» : (_root_.List valtype) := (input1).2; (.pure (((@valtype.BotT) : valtype))))))

def «$peek_clauses» (input0 : _root_.Nat) (input1 : inferresulttype) : List (ExecutablePlan.Clause Call _root_.Unit valtype) :=
  [fun (_ : _root_.Unit) => («$peek:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$peek:clause:1»  input0 input1)]

def «$local:clause:0» (input0 : context) (input1 : typeidx) : ExecutablePlan Call localtype :=
  (let C : context := input0; (let x : idx := input1; (.bind (.guard ((x < (_root_.List.length (context.LOCALS C))))) (fun (_ : Unit) => (match ((context.LOCALS C)[x]?) with | some «exec:1» => (let «eval:0» : localtype := «exec:1»; (.pure ((«eval:0» : localtype)))) | none => .unmatch)))))

def «$local_clauses» (input0 : context) (input1 : typeidx) : List (ExecutablePlan.Clause Call _root_.Unit localtype) :=
  [fun (_ : _root_.Unit) => («$local:clause:0»  input0 input1)]

def «$init_local:clause:0» (input0 : context) (input1 : typeidx) : ExecutablePlan Call context :=
  (let C : context := input0; (let x : idx := input1; (.bind (.call (Call.«$local» C x)) (fun («exec:1» : localtype) => (let «eval:0» : localtype := «exec:1»; (match «eval:0» with | .LocalT «exec:2» «exec:3» => (let init : SpecTec.init := «exec:2»; (let t : valtype := «exec:3»; (.bind (ExecutablePlan.require ((x < (_root_.List.length (context.LOCALS C)))) "update index out of bounds") (fun (_ : Unit) => (.pure ((({ C with LOCALS := (_root_.List.set (context.LOCALS C) x (@localtype.LocalT (@SpecTec.init.Set) t)) } : context) : context)))))))))))))

def «$init_local_clauses» (input0 : context) (input1 : typeidx) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («$init_local:clause:0»  input0 input1)]

def «$init_locals:clause:0» (input0 : context) (input1 : (_root_.List typeidx)) : ExecutablePlan Call context :=
  (let C : context := input0; (let «ti*» : (_root_.List typeidx) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ti*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C : context)))))))

def «$init_locals:clause:1» (input0 : context) (input1 : (_root_.List typeidx)) : ExecutablePlan Call context :=
  (let C : context := input0; (let «idx*» : (_root_.List idx) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «idx*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «idx*» with | «exec:2» :: «exec:1» => (let x_1 : idx := «exec:2»; (let «x*» : (_root_.List idx) := «exec:1»; (.bind (.call (Call.«$init_local» C x_1)) (fun («exec:3» : context) => (let «eval:0» : context := «exec:3»; (.bind (.call (Call.«$init_locals» «eval:0» «x*»)) (fun («exec:4» : context) => (let «eval:1» : context := «exec:4»; (.pure ((«eval:1» : context))))))))))) | [] => .unmatch)))))

def «$init_locals_clauses» (input0 : context) (input1 : (_root_.List typeidx)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («$init_locals:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$init_locals:clause:1»  input0 input1)]

def «$init_valtypes:clause:0» (input0 : inferresulttype) (input1 : _root_.Nat) (input2 : _root_.Nat) : ExecutablePlan Call (_root_.List valtype) :=
  (let irt : inferresulttype := input0; (let i : SpecTec.i := input1; (let n : SpecTec.n := input2; (.bind (.guard ((i < n))) (fun (_ : Unit) => (let int : _root_.Int := ((_root_.Int.ofNat n) - (_root_.Int.ofNat i)); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:1» => (let «eval:0» : SpecTec.n := «exec:1»; (let n' : SpecTec.n := «eval:0»; (.bind (.call (Call.«$peek» n' irt)) (fun («exec:2» : valtype) => (let «eval:1» : valtype := «exec:2»; (let t : valtype := «eval:1»; (.bind (.call (Call.«$init_valtypes» irt (i + (1 : _root_.Nat)) n)) (fun («exec:3» : (_root_.List valtype)) => (let «eval:2» : (_root_.List valtype) := «exec:3»; (.pure (((t :: «eval:2») : (_root_.List valtype))))))))))))) | none => .unmatch)))))))))

def «$init_valtypes:clause:1» (input0 : inferresulttype) (input1 : _root_.Nat) (input2 : _root_.Nat) : ExecutablePlan Call (_root_.List valtype) :=
  (let irt : inferresulttype := input0; (let i : SpecTec.i := input1; (let n : SpecTec.n := input2; (.pure ((([] : (_root_.List valtype)) : (_root_.List valtype)))))))

def «$init_valtypes_clauses» (input0 : inferresulttype) (input1 : _root_.Nat) (input2 : _root_.Nat) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List valtype)) :=
  [fun (_ : _root_.Unit) => («$init_valtypes:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$init_valtypes:clause:1»  input0 input1 input2)]

def «Numtype_ok:clause:0» (input0 : context) (input1 : SpecTec.numtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let numtype : SpecTec.numtype := input1; (.pure (((_root_.Unit.unit) : _root_.Unit)))))

def Numtype_ok_clauses (input0 : context) (input1 : numtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Numtype_ok:clause:0»  input0 input1)]

def «Vectype_ok:clause:0» (input0 : context) (input1 : SpecTec.vectype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let vectype : SpecTec.vectype := input1; (.pure (((_root_.Unit.unit) : _root_.Unit)))))

def Vectype_ok_clauses (input0 : context) (input1 : vectype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Vectype_ok:clause:0»  input0 input1)]

def «Limits_ok:clause:0» (input0 : context) (input1 : SpecTec.range) (input2 : limits) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let range : SpecTec.range := input1; (let u64 : SpecTec.u64 := (input2).MIN; (let u64'? : (_root_.Option SpecTec.u64) := (input2).MAX; (.bind (.guard (((_root_.Option.isNone u64'?) = true))) (fun (_ : Unit) => (.bind (.guard ((u64 ≤ range))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))

def «Limits_ok:clause:1» (input0 : context) (input1 : SpecTec.range) (input2 : limits) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let range : SpecTec.range := input1; (let u64 : SpecTec.u64 := (input2).MIN; (let u64''? : (_root_.Option SpecTec.u64) := (input2).MAX; (.bind (.guard (((_root_.Option.isSome u64''?) = true))) (fun (_ : Unit) => (match u64''? with | some «exec:1» => (let u64' : SpecTec.u64 := «exec:1»; (.bind (.guard ((((u64 ≤ range) ∧ (u64' ≤ range)) ∧ (u64 ≤ u64')))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | none => .unmatch)))))))

def Limits_ok_clauses (input0 : context) (input1 : range) (input2 : limits) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Limits_ok:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Limits_ok:clause:1»  input0 input1 input2)]

def «Instr_ok:br_table:iter:3:clause:0» (input0 : context) (input1 : (_root_.List idx)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))

def «Instr_ok:br_table:iter:3:clause:1» (input0 : context) (input1 : (_root_.List idx)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let x : idx := «exec:2»; (let «tail:0» : (_root_.List idx) := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (.bind (.call (Call.«Instr_ok:br_table:iter:3» C_0 «tail:0»)) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))

def «Instr_ok:br_table:iter:3_clauses» (input0 : context) (input1 : (_root_.List idx)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Instr_ok:br_table:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Instr_ok:br_table:iter:3:clause:1»  input0 input1)]

def «$check_lane_index:clause:0» (input0 : (_root_.List _root_.Nat)) : ExecutablePlan Call _root_.Bool :=
  (let «nat*» : (_root_.List _root_.Nat) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «nat*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))

def «$check_lane_index:clause:1» (input0 : (_root_.List _root_.Nat)) : ExecutablePlan Call _root_.Bool :=
  (let «i'*» : (_root_.List i) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «i'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «i'*» with | «exec:2» :: «exec:1» => (let i_1 : i := «exec:2»; (let «i*» : (_root_.List i) := «exec:1»; (.bind (.guard ((i_1 < (32 : _root_.Nat)))) (fun (_ : Unit) => (.bind (.call (Call.«$check_lane_index» «i*»)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | [] => .unmatch))))

def «$check_lane_index:clause:2» (input0 : (_root_.List _root_.Nat)) : ExecutablePlan Call _root_.Bool :=
  (let «_nat*» : (_root_.List _root_.Nat) := input0; (.pure ((false : _root_.Bool))))

def «$check_lane_index_clauses» (input0 : (_root_.List _root_.Nat)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$check_lane_index:clause:0»  input0), fun (_ : _root_.Unit) => («$check_lane_index:clause:1»  input0), fun (_ : _root_.Unit) => («$check_lane_index:clause:2»  input0)]

def «Funcbody_ok:rule:iter:2:clause:0» (input0 : (_root_.List valtype)) : ExecutablePlan Call (_root_.List localtype) :=
  (match input0 with | [] => (.pure ((([] : (_root_.List localtype)) : (_root_.List localtype)))) | _ :: _ => .unmatch)

def «Funcbody_ok:rule:iter:2:clause:1» (input0 : (_root_.List valtype)) : ExecutablePlan Call (_root_.List localtype) :=
  (match input0 with | «exec:2» :: «exec:1» => (let t_1 : valtype := «exec:2»; (let «tail:0» : (_root_.List valtype) := «exec:1»; (let localtype' : localtype := (@localtype.LocalT (@init.Set) t_1); (.bind (.call (Call.«Funcbody_ok:rule:iter:2» «tail:0»)) (fun («exec:3» : (_root_.List localtype)) => (let «tail:1» : (_root_.List localtype) := «exec:3»; (.pure (((localtype' :: «tail:1») : (_root_.List localtype)))))))))) | [] => .unmatch)

def «Funcbody_ok:rule:iter:2_clauses» (input0 : (_root_.List valtype)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List localtype)) :=
  [fun (_ : _root_.Unit) => («Funcbody_ok:rule:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Funcbody_ok:rule:iter:2:clause:1»  input0)]

def «$numtype_of_addrtype:clause:0» (input0 : addrtype) : ExecutablePlan Call numtype :=
  (let «at» : addrtype := input0; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.pure (((@numtype.I32T) : numtype))))))

def «$numtype_of_addrtype:clause:1» (input0 : addrtype) : ExecutablePlan Call numtype :=
  (let «at» : addrtype := input0; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure (((@numtype.I64T) : numtype))))))

def «$numtype_of_addrtype_clauses» (input0 : addrtype) : List (ExecutablePlan.Clause Call _root_.Unit numtype) :=
  [fun (_ : _root_.Unit) => («$numtype_of_addrtype:clause:0»  input0), fun (_ : _root_.Unit) => («$numtype_of_addrtype:clause:1»  input0)]

def «Memtype_ok:clause:0» (input0 : context) (input1 : memtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .MemoryT «exec:1» «exec:2» => (let «at» : addrtype := «exec:1»; (let lim : limits := «exec:2»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.call (Call.Limits_ok C_0 (65536 : _root_.Nat) lim)) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))

def «Memtype_ok:clause:1» (input0 : context) (input1 : memtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .MemoryT «exec:1» «exec:2» => (let «at» : addrtype := «exec:1»; (let lim : limits := «exec:2»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.bind (.call (Call.Limits_ok C_0 (281474976710656 : _root_.Nat) lim)) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))

def Memtype_ok_clauses (input0 : context) (input1 : memtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Memtype_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Memtype_ok:clause:1»  input0 input1)]

def «Vstoreop_ok:clause:0» (input0 : context) (input1 : vstoreop_) : ExecutablePlan Call vectype :=
  (let C_0 : context := input0; (let vt : vectype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let void : SpecTec.void := (input1).PACK; (.bind (.call (Call.«$vec_size» vt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let int_3 : _root_.Int := «eval:0»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : memtype := «exec:2»; (match «eval:1» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.guard ((u64 < (4294967296 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((vt : vectype))))))))))) | none => .unmatch))))))))))))))

def «Vstoreop_ok:clause:1» (input0 : context) (input1 : vstoreop_) : ExecutablePlan Call vectype :=
  (let C_0 : context := input0; (let vt : vectype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let void : SpecTec.void := (input1).PACK; (.bind (.call (Call.«$vec_size» vt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let int_3 : _root_.Int := «eval:0»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : memtype := «exec:2»; (match «eval:1» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure ((vt : vectype))))))))) | none => .unmatch))))))))))))))

def Vstoreop_ok_clauses (input0 : context) (input1 : vstoreop_) : List (ExecutablePlan.Clause Call _root_.Unit vectype) :=
  [fun (_ : _root_.Unit) => («Vstoreop_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Vstoreop_ok:clause:1»  input0 input1)]

def «Mem_ok:clause:0» (input0 : context) (input1 : memory) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let mt : memtype := (input1).MTYPE; (.bind (.call (Call.Memtype_ok C_0 mt)) (fun («exec:1» : _root_.Unit) => (let C_1 : context := ({ C_0 with MEMS := ((context.MEMS C_0) ++ ([mt] : (_root_.List memtype))) } : context); (.pure ((C_1 : context))))))))

def Mem_ok_clauses (input0 : context) (input1 : memory) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Mem_ok:clause:0»  input0 input1)]

def «Mems_ok:clause:0» (input0 : context) (input1 : (_root_.List memory)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «memory'*» : (_root_.List memory) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «memory'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «memory'*» with | «exec:2» :: «exec:1» => (let memory_1 : memory := «exec:2»; (let «memory*» : (_root_.List memory) := «exec:1»; (.bind (.call (Call.Mem_ok C_0 memory_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Mems_ok C_1 «memory*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Mems_ok:clause:1» (input0 : context) (input1 : (_root_.List memory)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «memory*» : (_root_.List memory) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «memory*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Mems_ok_clauses (input0 : context) (input1 : (_root_.List memory)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Mems_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Mems_ok:clause:1»  input0 input1)]

def «$free_catch:clause:0» (input0 : SpecTec.«catch») : ExecutablePlan Call free :=
  (let «catch» : SpecTec.«catch» := input0; (.bind (.guard (((«exec:match:catch:Catch» «catch») = true))) (fun (_ : Unit) => (match «catch» with | .Catch «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_tags» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_labels» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_catch:clause:1» (input0 : SpecTec.«catch») : ExecutablePlan Call free :=
  (let «catch» : SpecTec.«catch» := input0; (.bind (.guard (((«exec:match:catch:CatchRef» «catch») = true))) (fun (_ : Unit) => (match «catch» with | .CatchRef «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_tags» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_labels» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_catch:clause:2» (input0 : SpecTec.«catch») : ExecutablePlan Call free :=
  (let «catch» : SpecTec.«catch» := input0; (.bind (.guard (((«exec:match:catch:CatchAll» «catch») = true))) (fun (_ : Unit) => (match «catch» with | .CatchAll «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_catch:clause:3» (input0 : SpecTec.«catch») : ExecutablePlan Call free :=
  (let «catch» : SpecTec.«catch» := input0; (.bind (.guard (((«exec:match:catch:CatchAllRef» «catch») = true))) (fun (_ : Unit) => (match «catch» with | .CatchAllRef «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_catch_clauses» (input0 : «catch») : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_catch:clause:0»  input0), fun (_ : _root_.Unit) => («$free_catch:clause:1»  input0), fun (_ : _root_.Unit) => («$free_catch:clause:2»  input0), fun (_ : _root_.Unit) => («$free_catch:clause:3»  input0)]

def «$push:clause:0» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) : ExecutablePlan Call (ellipses × resulttype) :=
  (let C : context := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t_1*» : (_root_.List valtype) := (input1).2; (let ellipses' : SpecTec.ellipses := (input2).1; (let «t_2*» : (_root_.List valtype) := (input2).2; (.bind (.guard (((«exec:match:ellipses:NoEllipses» ellipses) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ellipses:NoEllipses» ellipses') = true))) (fun (_ : Unit) => (.pure ((((@SpecTec.ellipses.NoEllipses), («t_2*» ++ «t_1*»)) : (SpecTec.ellipses × resulttype)))))))))))))

def «$push:clause:1» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) : ExecutablePlan Call (ellipses × resulttype) :=
  (let C : context := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t_1*» : (_root_.List valtype) := (input1).2; (let ellipses' : SpecTec.ellipses := (input2).1; (let «t_2*» : (_root_.List valtype) := (input2).2; (.bind (.guard (((«exec:match:ellipses:NoEllipses» ellipses) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ellipses:Ellipses» ellipses') = true))) (fun (_ : Unit) => (.pure ((((@SpecTec.ellipses.Ellipses), («t_2*» ++ «t_1*»)) : (SpecTec.ellipses × resulttype)))))))))))))

def «$push:clause:2» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) : ExecutablePlan Call (ellipses × resulttype) :=
  (let C : context := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t_1*» : (_root_.List valtype) := (input1).2; (let ellipses_2 : SpecTec.ellipses := (input2).1; (let «valtype*» : (_root_.List valtype) := (input2).2; (.bind (.guard (((«exec:match:ellipses:Ellipses» ellipses) = true))) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «valtype*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((@SpecTec.ellipses.Ellipses), «t_1*») : (SpecTec.ellipses × resulttype)))))))))))))

def «$push_clauses» (input0 : context) (input1 : (ellipses × resulttype)) (input2 : (ellipses × resulttype)) : List (ExecutablePlan.Clause Call _root_.Unit (ellipses × resulttype)) :=
  [fun (_ : _root_.Unit) => («$push:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$push:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$push:clause:2»  input0 input1 input2)]

def «$free_exportdesc:clause:0» (input0 : SpecTec.exportdesc) : ExecutablePlan Call free :=
  (let exportdesc : SpecTec.exportdesc := input0; (.bind (.guard (((«exec:match:exportdesc:FuncExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .FuncExport «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_funcs» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_exportdesc:clause:1» (input0 : SpecTec.exportdesc) : ExecutablePlan Call free :=
  (let exportdesc : SpecTec.exportdesc := input0; (.bind (.guard (((«exec:match:exportdesc:TableExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .TableExport «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_exportdesc:clause:2» (input0 : SpecTec.exportdesc) : ExecutablePlan Call free :=
  (let exportdesc : SpecTec.exportdesc := input0; (.bind (.guard (((«exec:match:exportdesc:MemExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .MemExport «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_exportdesc:clause:3» (input0 : SpecTec.exportdesc) : ExecutablePlan Call free :=
  (let exportdesc : SpecTec.exportdesc := input0; (.bind (.guard (((«exec:match:exportdesc:GlobalExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .GlobalExport «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_globals» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_exportdesc:clause:4» (input0 : SpecTec.exportdesc) : ExecutablePlan Call free :=
  (let exportdesc : SpecTec.exportdesc := input0; (.bind (.guard (((«exec:match:exportdesc:TagExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .TagExport «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tags» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_exportdesc_clauses» (input0 : exportdesc) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_exportdesc:clause:0»  input0), fun (_ : _root_.Unit) => («$free_exportdesc:clause:1»  input0), fun (_ : _root_.Unit) => («$free_exportdesc:clause:2»  input0), fun (_ : _root_.Unit) => («$free_exportdesc:clause:3»  input0), fun (_ : _root_.Unit) => («$free_exportdesc:clause:4»  input0)]

def «$free_export:clause:0» (input0 : SpecTec.«export») : ExecutablePlan Call free :=
  (let «export» : SpecTec.«export» := input0; (.bind (.call (Call.«$free_exportdesc» (SpecTec.«export».EDESC «export»))) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_export_clauses» (input0 : «export») : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_export:clause:0»  input0)]

def «Export_ok:clause:0» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») : ExecutablePlan Call nameset :=
  (let C_0 : context := input0; (let nameset : SpecTec.nameset := input1; (let name : SpecTec.name := (input2).NAME; (let exportdesc : SpecTec.exportdesc := (input2).EDESC; (.bind (.guard (((«exec:match:exportdesc:FuncExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .FuncExport «exec:1» => (let x : idx := «exec:1»; (.bind (.guard (((x ≥ (0 : _root_.Nat)) ∧ (x < (_root_.List.length (context.FUNCS C_0)))))) (fun (_ : Unit) => (.bind (.call (Call.«$in_set» SpecTec.name name nameset)) (fun («exec:2» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure (((@«$union_set» SpecTec.name ({ key := fun values => .node 8 (values.map (fun value => (@_root_.SpecTecCompareKey.key _root_.Nat (inferInstance : _root_.SpecTecCompareKey _root_.Nat) value))) } : _root_.SpecTecCompareKey (_root_.List _root_.Nat)) nameset (@set.«`{ % `}» SpecTec.name ([name] : (_root_.List SpecTec.name)))) : SpecTec.nameset))))))))))) | _ => .unmatch)))))))

def «Export_ok:clause:1» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») : ExecutablePlan Call nameset :=
  (let C_0 : context := input0; (let nameset : SpecTec.nameset := input1; (let name : SpecTec.name := (input2).NAME; (let exportdesc : SpecTec.exportdesc := (input2).EDESC; (.bind (.guard (((«exec:match:exportdesc:GlobalExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .GlobalExport «exec:1» => (let x : idx := «exec:1»; (.bind (.guard (((x ≥ (0 : _root_.Nat)) ∧ (x < (_root_.List.length (context.GLOBALS C_0)))))) (fun (_ : Unit) => (.bind (.call (Call.«$in_set» SpecTec.name name nameset)) (fun («exec:2» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure (((@«$union_set» SpecTec.name ({ key := fun values => .node 8 (values.map (fun value => (@_root_.SpecTecCompareKey.key _root_.Nat (inferInstance : _root_.SpecTecCompareKey _root_.Nat) value))) } : _root_.SpecTecCompareKey (_root_.List _root_.Nat)) nameset (@set.«`{ % `}» SpecTec.name ([name] : (_root_.List SpecTec.name)))) : SpecTec.nameset))))))))))) | _ => .unmatch)))))))

def «Export_ok:clause:2» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») : ExecutablePlan Call nameset :=
  (let C_0 : context := input0; (let nameset : SpecTec.nameset := input1; (let name : SpecTec.name := (input2).NAME; (let exportdesc : SpecTec.exportdesc := (input2).EDESC; (.bind (.guard (((«exec:match:exportdesc:TableExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .TableExport «exec:1» => (let x : idx := «exec:1»; (.bind (.guard (((x ≥ (0 : _root_.Nat)) ∧ (x < (_root_.List.length (context.TABLES C_0)))))) (fun (_ : Unit) => (.bind (.call (Call.«$in_set» SpecTec.name name nameset)) (fun («exec:2» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure (((@«$union_set» SpecTec.name ({ key := fun values => .node 8 (values.map (fun value => (@_root_.SpecTecCompareKey.key _root_.Nat (inferInstance : _root_.SpecTecCompareKey _root_.Nat) value))) } : _root_.SpecTecCompareKey (_root_.List _root_.Nat)) nameset (@set.«`{ % `}» SpecTec.name ([name] : (_root_.List SpecTec.name)))) : SpecTec.nameset))))))))))) | _ => .unmatch)))))))

def «Export_ok:clause:3» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») : ExecutablePlan Call nameset :=
  (let C_0 : context := input0; (let nameset : SpecTec.nameset := input1; (let name : SpecTec.name := (input2).NAME; (let exportdesc : SpecTec.exportdesc := (input2).EDESC; (.bind (.guard (((«exec:match:exportdesc:MemExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .MemExport «exec:1» => (let x : idx := «exec:1»; (.bind (.guard (((x ≥ (0 : _root_.Nat)) ∧ (x < (_root_.List.length (context.MEMS C_0)))))) (fun (_ : Unit) => (.bind (.call (Call.«$in_set» SpecTec.name name nameset)) (fun («exec:2» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure (((@«$union_set» SpecTec.name ({ key := fun values => .node 8 (values.map (fun value => (@_root_.SpecTecCompareKey.key _root_.Nat (inferInstance : _root_.SpecTecCompareKey _root_.Nat) value))) } : _root_.SpecTecCompareKey (_root_.List _root_.Nat)) nameset (@set.«`{ % `}» SpecTec.name ([name] : (_root_.List SpecTec.name)))) : SpecTec.nameset))))))))))) | _ => .unmatch)))))))

def «Export_ok:clause:4» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») : ExecutablePlan Call nameset :=
  (let C_0 : context := input0; (let nameset : SpecTec.nameset := input1; (let name : SpecTec.name := (input2).NAME; (let exportdesc : SpecTec.exportdesc := (input2).EDESC; (.bind (.guard (((«exec:match:exportdesc:TagExport» exportdesc) = true))) (fun (_ : Unit) => (match exportdesc with | .TagExport «exec:1» => (let x : idx := «exec:1»; (.bind (.guard (((x ≥ (0 : _root_.Nat)) ∧ (x < (_root_.List.length (context.TAGS C_0)))))) (fun (_ : Unit) => (.bind (.call (Call.«$in_set» SpecTec.name name nameset)) (fun («exec:2» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure (((@«$union_set» SpecTec.name ({ key := fun values => .node 8 (values.map (fun value => (@_root_.SpecTecCompareKey.key _root_.Nat (inferInstance : _root_.SpecTecCompareKey _root_.Nat) value))) } : _root_.SpecTecCompareKey (_root_.List _root_.Nat)) nameset (@set.«`{ % `}» SpecTec.name ([name] : (_root_.List SpecTec.name)))) : SpecTec.nameset))))))))))) | _ => .unmatch)))))))

def Export_ok_clauses (input0 : context) (input1 : nameset) (input2 : «export») : List (ExecutablePlan.Clause Call _root_.Unit nameset) :=
  [fun (_ : _root_.Unit) => («Export_ok:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Export_ok:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («Export_ok:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («Export_ok:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («Export_ok:clause:4»  input0 input1 input2)]

def «Exports_ok:clause:0» (input0 : context) (input1 : nameset) (input2 : (_root_.List «export»)) : ExecutablePlan Call nameset :=
  (let C_0 : context := input0; (let nameset_0 : nameset := input1; (let «ex*» : (_root_.List «export») := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ex*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ex*» with | «exec:2» :: «exec:1» => (let export_1 : «export» := «exec:2»; (let «export*» : (_root_.List «export») := «exec:1»; (.bind (.call (Call.Export_ok C_0 nameset_0 export_1)) (fun («exec:3» : nameset) => (let nameset_1 : nameset := «exec:3»; (.bind (.call (Call.Exports_ok C_0 nameset_1 «export*»)) (fun («exec:4» : nameset) => (let nameset_2 : nameset := «exec:4»; (.pure ((nameset_2 : nameset))))))))))) | [] => .unmatch))))))

def «Exports_ok:clause:1» (input0 : context) (input1 : nameset) (input2 : (_root_.List «export»)) : ExecutablePlan Call nameset :=
  (let C_0 : context := input0; (let nameset_0 : nameset := input1; (let «ex*» : (_root_.List «export») := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ex*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((nameset_0 : nameset))))))))

def Exports_ok_clauses (input0 : context) (input1 : nameset) (input2 : (_root_.List «export»)) : List (ExecutablePlan.Clause Call _root_.Unit nameset) :=
  [fun (_ : _root_.Unit) => («Exports_ok:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Exports_ok:clause:1»  input0 input1 input2)]

def «$type_externop:clause:0» (input0 : externop_) : ExecutablePlan Call (heaptype × heaptype) :=
  (let eop : externop_ := input0; (.bind (.guard (((«exec:match:externop_:Internalize» eop) = true))) (fun (_ : Unit) => (.pure ((((@heaptype.ExternHT), (@heaptype.AnyHT)) : (heaptype × heaptype)))))))

def «$type_externop:clause:1» (input0 : externop_) : ExecutablePlan Call (heaptype × heaptype) :=
  (let eop : externop_ := input0; (.bind (.guard (((«exec:match:externop_:Externalize» eop) = true))) (fun (_ : Unit) => (.pure ((((@heaptype.AnyHT), (@heaptype.ExternHT)) : (heaptype × heaptype)))))))

def «$type_externop_clauses» (input0 : externop_) : List (ExecutablePlan.Clause Call _root_.Unit (heaptype × heaptype)) :=
  [fun (_ : _root_.Unit) => («$type_externop:clause:0»  input0), fun (_ : _root_.Unit) => («$type_externop:clause:1»  input0)]

def «$is_const:clause:0» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard ((instr ∈ ([(@SpecTec.instr.BINOP (@op.I32 ibinop ibinop fbinop fbinop (@ibinop.IAdd))), (@SpecTec.instr.BINOP (@op.I32 ibinop ibinop fbinop fbinop (@ibinop.ISub))), (@SpecTec.instr.BINOP (@op.I32 ibinop ibinop fbinop fbinop (@ibinop.IMul))), (@SpecTec.instr.BINOP (@op.I64 ibinop ibinop fbinop fbinop (@ibinop.IAdd))), (@SpecTec.instr.BINOP (@op.I64 ibinop ibinop fbinop fbinop (@ibinop.ISub))), (@SpecTec.instr.BINOP (@op.I64 ibinop ibinop fbinop fbinop (@ibinop.IMul)))] : (_root_.List SpecTec.instr))))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))

def «$is_const:clause:1» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:CONST» instr) = true))) (fun (_ : Unit) => (match instr with | .CONST «exec:1» => (let _num : num_ := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))))

def «$is_const:clause:2» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:VEC.CONST» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.CONST» «exec:1» => (let _vec : vec_ := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))))

def «$is_const:clause:3» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:REF.NULL» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.NULL» «exec:1» => (let _ht : heaptype := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))))

def «$is_const:clause:4» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:REF.FUNC» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.FUNC» «exec:1» => (let _funcidx : funcidx := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))))

def «$is_const:clause:5» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:REF.I31» instr) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))

def «$is_const:clause:6» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:STRUCT.NEW» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.NEW» «exec:1» «exec:2» => (let _ti : typeidx := «exec:1»; (let _iop : initop_ := «exec:2»; (.pure ((true : _root_.Bool))))) | _ => .unmatch)))))

def «$is_const:clause:7» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:ARRAY.NEW» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW» «exec:1» «exec:2» => (let _ti : typeidx := «exec:1»; (let _iop : initop_ := «exec:2»; (.pure ((true : _root_.Bool))))) | _ => .unmatch)))))

def «$is_const:clause:8» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:ARRAY.NEW_FIXED» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW_FIXED» «exec:1» «exec:2» => (let _ti : typeidx := «exec:1»; (let _u32 : u32 := «exec:2»; (.pure ((true : _root_.Bool))))) | _ => .unmatch)))))

def «$is_const:clause:9» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:EXTERN.CONVERT» instr) = true))) (fun (_ : Unit) => (match instr with | .«EXTERN.CONVERT» «exec:1» => (let _eop : externop_ := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))))

def «$is_const:clause:10» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.bind (.guard (((«exec:match:instr:GLOBAL.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«GLOBAL.GET» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.GLOBALS C))))) (fun (_ : Unit) => (match ((context.GLOBALS C)[x]?) with | some «exec:2» => (let «eval:0» : globaltype := «exec:2»; (match «eval:0» with | .GlobalT «exec:3» «exec:4» => (let «mut» : SpecTec.«mut» := «exec:3»; (let t : valtype := «exec:4»; (.bind (.guard ((@SpecTec.«mut».Cons) = «mut»)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))) | none => .unmatch)))) | _ => .unmatch)))))

def «$is_const:clause:11» (input0 : context) (input1 : SpecTec.instr) : ExecutablePlan Call _root_.Bool :=
  (let C : context := input0; (let instr : SpecTec.instr := input1; (.pure ((false : _root_.Bool)))))

def «$is_const_clauses» (input0 : context) (input1 : instr) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$is_const:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:5»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:6»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:7»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:8»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:9»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:10»  input0 input1), fun (_ : _root_.Unit) => («$is_const:clause:11»  input0 input1)]

def «Const_ok:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List instr)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))

def «Const_ok:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List SpecTec.instr)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let instr : SpecTec.instr := «exec:2»; (let «tail:0» : (_root_.List SpecTec.instr) := «exec:1»; (.bind (.call (Call.«$is_const» C_0 instr)) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call (Call.«Const_ok:rule:iter:0» C_0 «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch))

def «Const_ok:rule:iter:0_clauses» (input0 : context) (input1 : (_root_.List instr)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Const_ok:rule:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Const_ok:rule:iter:0:clause:1»  input0 input1)]

def «$type_lane:clause:0» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) : ExecutablePlan Call numtype :=
  (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := input0; (.bind (.guard (((«exec:match:laneop:I8x16» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I8x16 «exec:1» => (let _A : A := «exec:1»; (.pure (((@numtype.I32T) : numtype)))) | _ => .unmatch))))

def «$type_lane:clause:1» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) : ExecutablePlan Call numtype :=
  (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := input0; (.bind (.guard (((«exec:match:laneop:I16x8» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I16x8 «exec:1» => (let _B : B := «exec:1»; (.pure (((@numtype.I32T) : numtype)))) | _ => .unmatch))))

def «$type_lane:clause:2» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) : ExecutablePlan Call numtype :=
  (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := input0; (.bind (.guard (((«exec:match:laneop:I32x4» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I32x4 «exec:1» => (let _C : C := «exec:1»; (.pure (((@numtype.I32T) : numtype)))) | _ => .unmatch))))

def «$type_lane:clause:3» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) : ExecutablePlan Call numtype :=
  (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := input0; (.bind (.guard (((«exec:match:laneop:I64x2» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I64x2 «exec:1» => (let _D : D := «exec:1»; (.pure (((@numtype.I64T) : numtype)))) | _ => .unmatch))))

def «$type_lane:clause:4» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) : ExecutablePlan Call numtype :=
  (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := input0; (.bind (.guard (((«exec:match:laneop:F32x4» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .F32x4 «exec:1» => (let _E : E := «exec:1»; (.pure (((@numtype.F32T) : numtype)))) | _ => .unmatch))))

def «$type_lane:clause:5» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) : ExecutablePlan Call numtype :=
  (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := input0; (.bind (.guard (((«exec:match:laneop:F64x2» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .F64x2 «exec:1» => (let _F : F := «exec:1»; (.pure (((@numtype.F64T) : numtype)))) | _ => .unmatch))))

def «$type_lane_clauses» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) : List (ExecutablePlan.Clause Call _root_.Unit numtype) :=
  [fun (_ : _root_.Unit) => («$type_lane:clause:0» A B C D E F input0), fun (_ : _root_.Unit) => («$type_lane:clause:1» A B C D E F input0), fun (_ : _root_.Unit) => («$type_lane:clause:2» A B C D E F input0), fun (_ : _root_.Unit) => («$type_lane:clause:3» A B C D E F input0), fun (_ : _root_.Unit) => («$type_lane:clause:4» A B C D E F input0), fun (_ : _root_.Unit) => («$type_lane:clause:5» A B C D E F input0)]

def «$type_vec_lane:clause:0» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) : ExecutablePlan Call numtype :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A_T B_T C_T D_T E_T F_T) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I8x16» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I8x16 «exec:2» => (let A : A_T := «exec:2»; (.bind (.call (Call.«$type_lane» A_T B_T C_T D_T E_T F_T (@laneop.I8x16 A_T B_T C_T D_T E_T F_T A))) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (.pure ((«eval:0» : numtype))))))) | _ => .unmatch)))))

def «$type_vec_lane:clause:1» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) : ExecutablePlan Call numtype :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A_T B_T C_T D_T E_T F_T) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I16x8» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I16x8 «exec:2» => (let B : B_T := «exec:2»; (.bind (.call (Call.«$type_lane» A_T B_T C_T D_T E_T F_T (@laneop.I16x8 A_T B_T C_T D_T E_T F_T B))) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (.pure ((«eval:0» : numtype))))))) | _ => .unmatch)))))

def «$type_vec_lane:clause:2» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) : ExecutablePlan Call numtype :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A_T B_T C_T D_T E_T F_T) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I32x4» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I32x4 «exec:2» => (let C : C_T := «exec:2»; (.bind (.call (Call.«$type_lane» A_T B_T C_T D_T E_T F_T (@laneop.I32x4 A_T B_T C_T D_T E_T F_T C))) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (.pure ((«eval:0» : numtype))))))) | _ => .unmatch)))))

def «$type_vec_lane:clause:3» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) : ExecutablePlan Call numtype :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A_T B_T C_T D_T E_T F_T) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I64x2» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I64x2 «exec:2» => (let D : D_T := «exec:2»; (.bind (.call (Call.«$type_lane» A_T B_T C_T D_T E_T F_T (@laneop.I64x2 A_T B_T C_T D_T E_T F_T D))) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (.pure ((«eval:0» : numtype))))))) | _ => .unmatch)))))

def «$type_vec_lane:clause:4» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) : ExecutablePlan Call numtype :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A_T B_T C_T D_T E_T F_T) := «exec:1»; (.bind (.guard (((«exec:match:laneop:F32x4» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .F32x4 «exec:2» => (let E : E_T := «exec:2»; (.bind (.call (Call.«$type_lane» A_T B_T C_T D_T E_T F_T (@laneop.F32x4 A_T B_T C_T D_T E_T F_T E))) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (.pure ((«eval:0» : numtype))))))) | _ => .unmatch)))))

def «$type_vec_lane:clause:5» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) : ExecutablePlan Call numtype :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A_T B_T C_T D_T E_T F_T) := «exec:1»; (.bind (.guard (((«exec:match:laneop:F64x2» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .F64x2 «exec:2» => (let F : F_T := «exec:2»; (.bind (.call (Call.«$type_lane» A_T B_T C_T D_T E_T F_T (@laneop.F64x2 A_T B_T C_T D_T E_T F_T F))) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (.pure ((«eval:0» : numtype))))))) | _ => .unmatch)))))

def «$type_vec_lane_clauses» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) : List (ExecutablePlan.Clause Call _root_.Unit numtype) :=
  [fun (_ : _root_.Unit) => («$type_vec_lane:clause:0» A_T B_T C_T D_T E_T F_T input0), fun (_ : _root_.Unit) => («$type_vec_lane:clause:1» A_T B_T C_T D_T E_T F_T input0), fun (_ : _root_.Unit) => («$type_vec_lane:clause:2» A_T B_T C_T D_T E_T F_T input0), fun (_ : _root_.Unit) => («$type_vec_lane:clause:3» A_T B_T C_T D_T E_T F_T input0), fun (_ : _root_.Unit) => («$type_vec_lane:clause:4» A_T B_T C_T D_T E_T F_T input0), fun (_ : _root_.Unit) => («$type_vec_lane:clause:5» A_T B_T C_T D_T E_T F_T input0)]

def «$lane_extractop:clause:0» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» : (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I8x16» «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>») = true))) (fun (_ : Unit) => (match «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» with | .I8x16 «exec:2» => (match «exec:2» with | .Extract «exec:3» => (let i : SpecTec.i := («exec:3»).1; (let _extension : extension := («exec:3»).2; (.pure (((_root_.Int.ofNat i) : _root_.Int)))))) | _ => .unmatch)))))

def «$lane_extractop:clause:1» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» : (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I16x8» «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>») = true))) (fun (_ : Unit) => (match «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» with | .I16x8 «exec:2» => (match «exec:2» with | .Extract «exec:3» => (let i : SpecTec.i := («exec:3»).1; (let _extension : extension := («exec:3»).2; (.pure (((_root_.Int.ofNat i) : _root_.Int)))))) | _ => .unmatch)))))

def «$lane_extractop:clause:2» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» : (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I32x4» «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>») = true))) (fun (_ : Unit) => (match «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» with | .I32x4 «exec:2» => (match «exec:2» with | .Extract «exec:3» => (let i : SpecTec.i := («exec:3»).1; (let _void : void := («exec:3»).2; (.pure (((_root_.Int.ofNat i) : _root_.Int)))))) | _ => .unmatch)))))

def «$lane_extractop:clause:3» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» : (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I64x2» «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>») = true))) (fun (_ : Unit) => (match «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» with | .I64x2 «exec:2» => (match «exec:2» with | .Extract «exec:3» => (let i : SpecTec.i := («exec:3»).1; (let _void : void := («exec:3»).2; (.pure (((_root_.Int.ofNat i) : _root_.Int)))))) | _ => .unmatch)))))

def «$lane_extractop:clause:4» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» : (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)) := «exec:1»; (.bind (.guard (((«exec:match:laneop:F32x4» «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>») = true))) (fun (_ : Unit) => (match «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» with | .F32x4 «exec:2» => (match «exec:2» with | .Extract «exec:3» => (let i : SpecTec.i := («exec:3»).1; (let _void : void := («exec:3»).2; (.pure (((_root_.Int.ofNat i) : _root_.Int)))))) | _ => .unmatch)))))

def «$lane_extractop:clause:5» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» : (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)) := «exec:1»; (.bind (.guard (((«exec:match:laneop:F64x2» «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>») = true))) (fun (_ : Unit) => (match «laneop<vnextractop<extension>, vnextractop<extension>, vnextractop<void>, vnextractop<void>, vnextractop<void>, vnextractop<void>>» with | .F64x2 «exec:2» => (match «exec:2» with | .Extract «exec:3» => (let i : SpecTec.i := («exec:3»).1; (let _void : void := («exec:3»).2; (.pure (((_root_.Int.ofNat i) : _root_.Int)))))) | _ => .unmatch)))))

def «$lane_extractop_clauses» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Int) :=
  [fun (_ : _root_.Unit) => («$lane_extractop:clause:0»  input0), fun (_ : _root_.Unit) => («$lane_extractop:clause:1»  input0), fun (_ : _root_.Unit) => («$lane_extractop:clause:2»  input0), fun (_ : _root_.Unit) => («$lane_extractop:clause:3»  input0), fun (_ : _root_.Unit) => («$lane_extractop:clause:4»  input0), fun (_ : _root_.Unit) => («$lane_extractop:clause:5»  input0)]

def «$lane_replaceop:clause:0» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» : (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I8x16» «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>») = true))) (fun (_ : Unit) => (match «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» with | .I8x16 «exec:2» => (match «exec:2» with | .Replace «exec:3» => (let i : SpecTec.i := «exec:3»; (.pure (((_root_.Int.ofNat i) : _root_.Int))))) | _ => .unmatch)))))

def «$lane_replaceop:clause:1» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» : (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I16x8» «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>») = true))) (fun (_ : Unit) => (match «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» with | .I16x8 «exec:2» => (match «exec:2» with | .Replace «exec:3» => (let i : SpecTec.i := «exec:3»; (.pure (((_root_.Int.ofNat i) : _root_.Int))))) | _ => .unmatch)))))

def «$lane_replaceop:clause:2» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» : (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I32x4» «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>») = true))) (fun (_ : Unit) => (match «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» with | .I32x4 «exec:2» => (match «exec:2» with | .Replace «exec:3» => (let i : SpecTec.i := «exec:3»; (.pure (((_root_.Int.ofNat i) : _root_.Int))))) | _ => .unmatch)))))

def «$lane_replaceop:clause:3» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» : (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I64x2» «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>») = true))) (fun (_ : Unit) => (match «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» with | .I64x2 «exec:2» => (match «exec:2» with | .Replace «exec:3» => (let i : SpecTec.i := «exec:3»; (.pure (((_root_.Int.ofNat i) : _root_.Int))))) | _ => .unmatch)))))

def «$lane_replaceop:clause:4» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» : (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop) := «exec:1»; (.bind (.guard (((«exec:match:laneop:F32x4» «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>») = true))) (fun (_ : Unit) => (match «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» with | .F32x4 «exec:2» => (match «exec:2» with | .Replace «exec:3» => (let i : SpecTec.i := «exec:3»; (.pure (((_root_.Int.ofNat i) : _root_.Int))))) | _ => .unmatch)))))

def «$lane_replaceop:clause:5» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» : (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop) := «exec:1»; (.bind (.guard (((«exec:match:laneop:F64x2» «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>») = true))) (fun (_ : Unit) => (match «laneop<vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop, vnreplaceop>» with | .F64x2 «exec:2» => (match «exec:2» with | .Replace «exec:3» => (let i : SpecTec.i := «exec:3»; (.pure (((_root_.Int.ofNat i) : _root_.Int))))) | _ => .unmatch)))))

def «$lane_replaceop_clauses» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Int) :=
  [fun (_ : _root_.Unit) => («$lane_replaceop:clause:0»  input0), fun (_ : _root_.Unit) => («$lane_replaceop:clause:1»  input0), fun (_ : _root_.Unit) => («$lane_replaceop:clause:2»  input0), fun (_ : _root_.Unit) => («$lane_replaceop:clause:3»  input0), fun (_ : _root_.Unit) => («$lane_replaceop:clause:4»  input0), fun (_ : _root_.Unit) => («$lane_replaceop:clause:5»  input0)]

def «$num_lanes:clause:0» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I8x16» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I8x16 «exec:2» => (let _A : A := «exec:2»; (.pure (((_root_.Int.ofNat (16 : _root_.Nat)) : _root_.Int)))) | _ => .unmatch)))))

def «$num_lanes:clause:1» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I16x8» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I16x8 «exec:2» => (let _B : B := «exec:2»; (.pure (((_root_.Int.ofNat (8 : _root_.Nat)) : _root_.Int)))) | _ => .unmatch)))))

def «$num_lanes:clause:2» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I32x4» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I32x4 «exec:2» => (let _C : C := «exec:2»; (.pure (((_root_.Int.ofNat (4 : _root_.Nat)) : _root_.Int)))) | _ => .unmatch)))))

def «$num_lanes:clause:3» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I64x2» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .I64x2 «exec:2» => (let _D : D := «exec:2»; (.pure (((_root_.Int.ofNat (2 : _root_.Nat)) : _root_.Int)))) | _ => .unmatch)))))

def «$num_lanes:clause:4» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := «exec:1»; (.bind (.guard (((«exec:match:laneop:F32x4» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .F32x4 «exec:2» => (let _E : E := «exec:2»; (.pure (((_root_.Int.ofNat (4 : _root_.Nat)) : _root_.Int)))) | _ => .unmatch)))))

def «$num_lanes:clause:5» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) : ExecutablePlan Call _root_.Int :=
  (match input0 with | .V128 «exec:1» => (let «laneop<A, B, C, D, E, F>» : (laneop A B C D E F) := «exec:1»; (.bind (.guard (((«exec:match:laneop:F64x2» «laneop<A, B, C, D, E, F>») = true))) (fun (_ : Unit) => (match «laneop<A, B, C, D, E, F>» with | .F64x2 «exec:2» => (let _F : F := «exec:2»; (.pure (((_root_.Int.ofNat (2 : _root_.Nat)) : _root_.Int)))) | _ => .unmatch)))))

def «$num_lanes_clauses» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Int) :=
  [fun (_ : _root_.Unit) => («$num_lanes:clause:0» A B C D E F input0), fun (_ : _root_.Unit) => («$num_lanes:clause:1» A B C D E F input0), fun (_ : _root_.Unit) => («$num_lanes:clause:2» A B C D E F input0), fun (_ : _root_.Unit) => («$num_lanes:clause:3» A B C D E F input0), fun (_ : _root_.Unit) => («$num_lanes:clause:4» A B C D E F input0), fun (_ : _root_.Unit) => («$num_lanes:clause:5» A B C D E F input0)]

def «$diff_reftype:clause:0» (input0 : reftype) (input1 : reftype) : ExecutablePlan Call reftype :=
  (match input0 with | .«% %» «exec:1» «exec:2» => (let null_1 : SpecTec.null := «exec:1»; (let ht_1 : heaptype := «exec:2»; (match input1 with | .«% %» «exec:3» «exec:4» => (let null : SpecTec.null := «exec:3»; (let ht_2 : heaptype := «exec:4»; (.bind (.guard (((«exec:match:null:Null» null) = true))) (fun (_ : Unit) => (.pure (((@reftype.«% %» (@SpecTec.null.NoNull) ht_1) : reftype)))))))))))

def «$diff_reftype:clause:1» (input0 : reftype) (input1 : reftype) : ExecutablePlan Call reftype :=
  (match input0 with | .«% %» «exec:1» «exec:2» => (let null_1 : SpecTec.null := «exec:1»; (let ht_1 : heaptype := «exec:2»; (match input1 with | .«% %» «exec:3» «exec:4» => (let null : SpecTec.null := «exec:3»; (let ht_2 : heaptype := «exec:4»; (.bind (.guard (((«exec:match:null:NoNull» null) = true))) (fun (_ : Unit) => (.pure (((@reftype.«% %» null_1 ht_1) : reftype)))))))))))

def «$diff_reftype_clauses» (input0 : reftype) (input1 : reftype) : List (ExecutablePlan.Clause Call _root_.Unit reftype) :=
  [fun (_ : _root_.Unit) => («$diff_reftype:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$diff_reftype:clause:1»  input0 input1)]

def «$match_null:clause:0» (input0 : SpecTec.null) (input1 : SpecTec.null) : ExecutablePlan Call _root_.Bool :=
  (let null : SpecTec.null := input0; (let null' : SpecTec.null := input1; (.bind (.guard (((«exec:match:null:NoNull» null) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:null:Null» null') = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))

def «$match_null:clause:1» (input0 : null) (input1 : null) : ExecutablePlan Call _root_.Bool :=
  (let null_1 : null := input0; (let null_2 : null := input1; (.bind (.guard (null_2 = null_1)) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))

def «$match_null:clause:2» (input0 : null) (input1 : null) : ExecutablePlan Call _root_.Bool :=
  (let null_1 : null := input0; (let null_2 : null := input1; (.pure ((false : _root_.Bool)))))

def «$match_null_clauses» (input0 : null) (input1 : null) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_null:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$match_null:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$match_null:clause:2»  input0 input1)]

def «$type_num:clause:0» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) : ExecutablePlan Call numtype :=
  (let «op<A, B, C, D>» : (op A_T B_T C_T D_T) := input0; (.bind (.guard (((«exec:match:op:I32» «op<A, B, C, D>») = true))) (fun (_ : Unit) => (match «op<A, B, C, D>» with | .I32 «exec:1» => (let A : A_T := «exec:1»; (.pure (((@numtype.I32T) : numtype)))) | _ => .unmatch))))

def «$type_num:clause:1» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) : ExecutablePlan Call numtype :=
  (let «op<A, B, C, D>» : (op A_T B_T C_T D_T) := input0; (.bind (.guard (((«exec:match:op:I64» «op<A, B, C, D>») = true))) (fun (_ : Unit) => (match «op<A, B, C, D>» with | .I64 «exec:1» => (let B : B_T := «exec:1»; (.pure (((@numtype.I64T) : numtype)))) | _ => .unmatch))))

def «$type_num:clause:2» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) : ExecutablePlan Call numtype :=
  (let «op<A, B, C, D>» : (op A_T B_T C_T D_T) := input0; (.bind (.guard (((«exec:match:op:F32» «op<A, B, C, D>») = true))) (fun (_ : Unit) => (match «op<A, B, C, D>» with | .F32 «exec:1» => (let C : C_T := «exec:1»; (.pure (((@numtype.F32T) : numtype)))) | _ => .unmatch))))

def «$type_num:clause:3» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) : ExecutablePlan Call numtype :=
  (let «op<A, B, C, D>» : (op A_T B_T C_T D_T) := input0; (.bind (.guard (((«exec:match:op:F64» «op<A, B, C, D>») = true))) (fun (_ : Unit) => (match «op<A, B, C, D>» with | .F64 «exec:1» => (let D : D_T := «exec:1»; (.pure (((@numtype.F64T) : numtype)))) | _ => .unmatch))))

def «$type_num_clauses» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) : List (ExecutablePlan.Clause Call _root_.Unit numtype) :=
  [fun (_ : _root_.Unit) => («$type_num:clause:0» A_T B_T C_T D_T input0), fun (_ : _root_.Unit) => («$type_num:clause:1» A_T B_T C_T D_T input0), fun (_ : _root_.Unit) => («$type_num:clause:2» A_T B_T C_T D_T input0), fun (_ : _root_.Unit) => («$type_num:clause:3» A_T B_T C_T D_T input0)]

def «$type_cvtop:clause:0» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op SpecTec.icvtop SpecTec.icvtop fcvtop fcvtop) := input0; (.bind (.guard (((«exec:match:op:I32» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .I32 «exec:1» => (let icvtop : SpecTec.icvtop := «exec:1»; (.bind (.guard ((icvtop ∈ ([(@SpecTec.icvtop.WrapI64)] : (_root_.List SpecTec.icvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.I64T), (@numtype.I32T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:1» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op SpecTec.icvtop SpecTec.icvtop fcvtop fcvtop) := input0; (.bind (.guard (((«exec:match:op:I32» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .I32 «exec:1» => (let icvtop : SpecTec.icvtop := «exec:1»; (.bind (.guard ((icvtop ∈ ([(@SpecTec.icvtop.TruncSF32), (@SpecTec.icvtop.TruncUF32), (@SpecTec.icvtop.TruncSatSF32), (@SpecTec.icvtop.TruncSatUF32), (@SpecTec.icvtop.ReinterpretFloat)] : (_root_.List SpecTec.icvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.F32T), (@numtype.I32T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:2» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op SpecTec.icvtop SpecTec.icvtop fcvtop fcvtop) := input0; (.bind (.guard (((«exec:match:op:I32» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .I32 «exec:1» => (let icvtop : SpecTec.icvtop := «exec:1»; (.bind (.guard ((icvtop ∈ ([(@SpecTec.icvtop.TruncSF64), (@SpecTec.icvtop.TruncUF64), (@SpecTec.icvtop.TruncSatSF64), (@SpecTec.icvtop.TruncSatUF64)] : (_root_.List SpecTec.icvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.F64T), (@numtype.I32T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:3» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op SpecTec.icvtop SpecTec.icvtop fcvtop fcvtop) := input0; (.bind (.guard (((«exec:match:op:I64» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .I64 «exec:1» => (let icvtop : SpecTec.icvtop := «exec:1»; (.bind (.guard ((icvtop ∈ ([(@SpecTec.icvtop.ExtendSI32), (@SpecTec.icvtop.ExtendUI32)] : (_root_.List SpecTec.icvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.I32T), (@numtype.I64T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:4» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op SpecTec.icvtop SpecTec.icvtop fcvtop fcvtop) := input0; (.bind (.guard (((«exec:match:op:I64» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .I64 «exec:1» => (let icvtop : SpecTec.icvtop := «exec:1»; (.bind (.guard ((icvtop ∈ ([(@SpecTec.icvtop.TruncSF32), (@SpecTec.icvtop.TruncUF32), (@SpecTec.icvtop.TruncSatSF32), (@SpecTec.icvtop.TruncSatUF32)] : (_root_.List SpecTec.icvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.F32T), (@numtype.I64T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:5» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op SpecTec.icvtop SpecTec.icvtop fcvtop fcvtop) := input0; (.bind (.guard (((«exec:match:op:I64» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .I64 «exec:1» => (let icvtop : SpecTec.icvtop := «exec:1»; (.bind (.guard ((icvtop ∈ ([(@SpecTec.icvtop.TruncSF64), (@SpecTec.icvtop.TruncUF64), (@SpecTec.icvtop.TruncSatSF64), (@SpecTec.icvtop.TruncSatUF64), (@SpecTec.icvtop.ReinterpretFloat)] : (_root_.List SpecTec.icvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.F64T), (@numtype.I64T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:6» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op icvtop icvtop SpecTec.fcvtop SpecTec.fcvtop) := input0; (.bind (.guard (((«exec:match:op:F32» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .F32 «exec:1» => (let fcvtop : SpecTec.fcvtop := «exec:1»; (.bind (.guard ((fcvtop ∈ ([(@SpecTec.fcvtop.ConvertSI32), (@SpecTec.fcvtop.ConvertUI32), (@SpecTec.fcvtop.ReinterpretInt)] : (_root_.List SpecTec.fcvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.I32T), (@numtype.F32T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:7» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op icvtop icvtop SpecTec.fcvtop SpecTec.fcvtop) := input0; (.bind (.guard (((«exec:match:op:F32» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .F32 «exec:1» => (let fcvtop : SpecTec.fcvtop := «exec:1»; (.bind (.guard ((fcvtop ∈ ([(@SpecTec.fcvtop.ConvertSI64), (@SpecTec.fcvtop.ConvertUI64)] : (_root_.List SpecTec.fcvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.I64T), (@numtype.F32T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:8» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op icvtop icvtop SpecTec.fcvtop SpecTec.fcvtop) := input0; (.bind (.guard (((«exec:match:op:F32» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .F32 «exec:1» => (let fcvtop : SpecTec.fcvtop := «exec:1»; (.bind (.guard ((fcvtop ∈ ([(@SpecTec.fcvtop.DemoteF64)] : (_root_.List SpecTec.fcvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.F64T), (@numtype.F32T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:9» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op icvtop icvtop SpecTec.fcvtop SpecTec.fcvtop) := input0; (.bind (.guard (((«exec:match:op:F64» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .F64 «exec:1» => (let fcvtop : SpecTec.fcvtop := «exec:1»; (.bind (.guard ((fcvtop ∈ ([(@SpecTec.fcvtop.ConvertSI32), (@SpecTec.fcvtop.ConvertUI32)] : (_root_.List SpecTec.fcvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.I32T), (@numtype.F64T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:10» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op icvtop icvtop SpecTec.fcvtop SpecTec.fcvtop) := input0; (.bind (.guard (((«exec:match:op:F64» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .F64 «exec:1» => (let fcvtop : SpecTec.fcvtop := «exec:1»; (.bind (.guard ((fcvtop ∈ ([(@SpecTec.fcvtop.ConvertSI64), (@SpecTec.fcvtop.ConvertUI64), (@SpecTec.fcvtop.ReinterpretInt)] : (_root_.List SpecTec.fcvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.I64T), (@numtype.F64T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop:clause:11» (input0 : cvtop_) : ExecutablePlan Call (numtype × numtype) :=
  (let «op<icvtop, icvtop, fcvtop, fcvtop>» : (op icvtop icvtop SpecTec.fcvtop SpecTec.fcvtop) := input0; (.bind (.guard (((«exec:match:op:F64» «op<icvtop, icvtop, fcvtop, fcvtop>») = true))) (fun (_ : Unit) => (match «op<icvtop, icvtop, fcvtop, fcvtop>» with | .F64 «exec:1» => (let fcvtop : SpecTec.fcvtop := «exec:1»; (.bind (.guard ((fcvtop ∈ ([(@SpecTec.fcvtop.PromoteF32)] : (_root_.List SpecTec.fcvtop))))) (fun (_ : Unit) => (.pure ((((@numtype.F32T), (@numtype.F64T)) : (numtype × numtype))))))) | _ => .unmatch))))

def «$type_cvtop_clauses» (input0 : cvtop_) : List (ExecutablePlan.Clause Call _root_.Unit (numtype × numtype)) :=
  [fun (_ : _root_.Unit) => («$type_cvtop:clause:0»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:1»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:2»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:3»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:4»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:5»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:6»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:7»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:8»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:9»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:10»  input0), fun (_ : _root_.Unit) => («$type_cvtop:clause:11»  input0)]

def «$check_uop_extends:clause:0» (input0 : unop_) : ExecutablePlan Call _root_.Bool :=
  (let «op<iunop, iunop, funop, funop>» : (op SpecTec.iunop SpecTec.iunop funop funop) := input0; (.bind (.guard (((«exec:match:op:I32» «op<iunop, iunop, funop, funop>») = true))) (fun (_ : Unit) => (match «op<iunop, iunop, funop, funop>» with | .I32 «exec:1» => (let iunop : SpecTec.iunop := «exec:1»; (.bind (.guard (((«exec:match:iunop:ExtendS» iunop) = true))) (fun (_ : Unit) => (match iunop with | .ExtendS «exec:2» => (let _pt : packtype := «exec:2»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))) | _ => .unmatch))))

def «$check_uop_extends:clause:1» (input0 : unop_) : ExecutablePlan Call _root_.Bool :=
  (let «op<iunop, iunop, funop, funop>» : (op SpecTec.iunop SpecTec.iunop funop funop) := input0; (.bind (.guard (((«exec:match:op:I64» «op<iunop, iunop, funop, funop>») = true))) (fun (_ : Unit) => (match «op<iunop, iunop, funop, funop>» with | .I64 «exec:1» => (let iunop : SpecTec.iunop := «exec:1»; (.bind (.guard (((«exec:match:iunop:ExtendS» iunop) = true))) (fun (_ : Unit) => (match iunop with | .ExtendS «exec:2» => (let _pt : packtype := «exec:2»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))) | _ => .unmatch))))

def «$check_uop_extends:clause:2» (input0 : unop_) : ExecutablePlan Call _root_.Bool :=
  (let uop : unop_ := input0; (.pure ((false : _root_.Bool))))

def «$check_uop_extends_clauses» (input0 : unop_) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$check_uop_extends:clause:0»  input0), fun (_ : _root_.Unit) => («$check_uop_extends:clause:1»  input0), fun (_ : _root_.Unit) => («$check_uop_extends:clause:2»  input0)]

def «$pack_size:clause:0» (input0 : packtype) : ExecutablePlan Call _root_.Int :=
  (let pt : packtype := input0; (.bind (.guard (((«exec:match:packtype:I8» pt) = true))) (fun (_ : Unit) => (.pure (((_root_.Int.ofNat (1 : _root_.Nat)) : _root_.Int))))))

def «$pack_size:clause:1» (input0 : packtype) : ExecutablePlan Call _root_.Int :=
  (let pt : packtype := input0; (.bind (.guard (((«exec:match:packtype:I16» pt) = true))) (fun (_ : Unit) => (.pure (((_root_.Int.ofNat (2 : _root_.Nat)) : _root_.Int))))))

def «$pack_size:clause:2» (input0 : packtype) : ExecutablePlan Call _root_.Int :=
  (let pt : packtype := input0; (.bind (.guard (((«exec:match:packtype:I32» pt) = true))) (fun (_ : Unit) => (.pure (((_root_.Int.ofNat (4 : _root_.Nat)) : _root_.Int))))))

def «$pack_size:clause:3» (input0 : packtype) : ExecutablePlan Call _root_.Int :=
  (let pt : packtype := input0; (.bind (.guard (((«exec:match:packtype:I64» pt) = true))) (fun (_ : Unit) => (.pure (((_root_.Int.ofNat (8 : _root_.Nat)) : _root_.Int))))))

def «$pack_size_clauses» (input0 : packtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Int) :=
  [fun (_ : _root_.Unit) => («$pack_size:clause:0»  input0), fun (_ : _root_.Unit) => («$pack_size:clause:1»  input0), fun (_ : _root_.Unit) => («$pack_size:clause:2»  input0), fun (_ : _root_.Unit) => («$pack_size:clause:3»  input0)]

def «Pack_ok:clause:0» (input0 : _root_.Int) (input1 : SpecTec.packtype) : ExecutablePlan Call _root_.Unit :=
  (let int : _root_.Int := input0; (let packtype : SpecTec.packtype := input1; (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:1» => (let «eval:0» : SpecTec.i := «exec:1»; (let i : SpecTec.i := «eval:0»; (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:2» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:2»; (.bind (.guard ((«eval:1» < (_root_.Int.ofNat i)))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))) | none => .unmatch)))))

def Pack_ok_clauses (input0 : _root_.Int) (input1 : packtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Pack_ok:clause:0»  input0 input1)]

def «Unop_ok:clause:0» (input0 : unop_) : ExecutablePlan Call _root_.Unit :=
  (let uop : unop_ := input0; (let «op<iunop, iunop, funop, funop>» : (op SpecTec.iunop SpecTec.iunop funop funop) := uop; (.bind (.guard (((«exec:match:op:I32» «op<iunop, iunop, funop, funop>») = true))) (fun (_ : Unit) => (match «op<iunop, iunop, funop, funop>» with | .I32 «exec:1» => (let iunop : SpecTec.iunop := «exec:1»; (.bind (.guard (((«exec:match:iunop:ExtendS» iunop) = true))) (fun (_ : Unit) => (match iunop with | .ExtendS «exec:2» => (let packtype : SpecTec.packtype := «exec:2»; (.bind (.call (Call.«$type_num» SpecTec.iunop SpecTec.iunop funop funop uop)) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (.bind (.call (Call.«$num_size» «eval:0»)) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (.bind (.call (Call.Pack_ok «eval:1» packtype)) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | _ => .unmatch)))) | _ => .unmatch)))))

def «Unop_ok:clause:1» (input0 : unop_) : ExecutablePlan Call _root_.Unit :=
  (let uop : unop_ := input0; (let «op<iunop, iunop, funop, funop>» : (op SpecTec.iunop SpecTec.iunop funop funop) := uop; (.bind (.guard (((«exec:match:op:I64» «op<iunop, iunop, funop, funop>») = true))) (fun (_ : Unit) => (match «op<iunop, iunop, funop, funop>» with | .I64 «exec:1» => (let iunop : SpecTec.iunop := «exec:1»; (.bind (.guard (((«exec:match:iunop:ExtendS» iunop) = true))) (fun (_ : Unit) => (match iunop with | .ExtendS «exec:2» => (let packtype : SpecTec.packtype := «exec:2»; (.bind (.call (Call.«$type_num» SpecTec.iunop SpecTec.iunop funop funop uop)) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (.bind (.call (Call.«$num_size» «eval:0»)) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (.bind (.call (Call.Pack_ok «eval:1» packtype)) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | _ => .unmatch)))) | _ => .unmatch)))))

def «Unop_ok:clause:2» (input0 : unop_) : ExecutablePlan Call _root_.Unit :=
  (let uop : unop_ := input0; (.bind (.call (Call.«$check_uop_extends» uop)) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))

def Unop_ok_clauses (input0 : unop_) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Unop_ok:clause:0»  input0), fun (_ : _root_.Unit) => («Unop_ok:clause:1»  input0), fun (_ : _root_.Unit) => («Unop_ok:clause:2»  input0)]

def «Loadop_ok:clause:0» (input0 : context) (input1 : loadop_) : ExecutablePlan Call numtype :=
  (let C_0 : context := input0; (let nt : numtype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let «(packtype, extension)?» : (_root_.Option (SpecTec.packtype × SpecTec.extension)) := (input1).PACK; (.bind (.guard (((_root_.Option.isSome «(packtype, extension)?») = true))) (fun (_ : Unit) => (match «(packtype, extension)?» with | some «exec:1» => (let packtype : SpecTec.packtype := («exec:1»).1; (let extension : SpecTec.extension := («exec:1»).2; (.bind (.call (Call.«$num_size» nt)) (fun («exec:2» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:2»; (.bind (.call (Call.Pack_ok «eval:0» packtype)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (let int_3 : _root_.Int := «eval:1»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:5» => (let «eval:2» : memtype := «exec:5»; (match «eval:2» with | .MemoryT «exec:6» «exec:7» => (let «at» : addrtype := «exec:6»; (let lim : limits := «exec:7»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.guard ((u64 < (4294967296 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((nt : numtype))))))))))) | none => .unmatch)))))))))))))))) | none => .unmatch))))))))

def «Loadop_ok:clause:1» (input0 : context) (input1 : loadop_) : ExecutablePlan Call numtype :=
  (let C_0 : context := input0; (let nt : numtype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let «(packtype, extension)?» : (_root_.Option (SpecTec.packtype × SpecTec.extension)) := (input1).PACK; (.bind (.guard (((_root_.Option.isSome «(packtype, extension)?») = true))) (fun (_ : Unit) => (match «(packtype, extension)?» with | some «exec:1» => (let packtype : SpecTec.packtype := («exec:1»).1; (let extension : SpecTec.extension := («exec:1»).2; (.bind (.call (Call.«$num_size» nt)) (fun («exec:2» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:2»; (.bind (.call (Call.Pack_ok «eval:0» packtype)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (let int_3 : _root_.Int := «eval:1»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:5» => (let «eval:2» : memtype := «exec:5»; (match «eval:2» with | .MemoryT «exec:6» «exec:7» => (let «at» : addrtype := «exec:6»; (let lim : limits := «exec:7»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure ((nt : numtype))))))))) | none => .unmatch)))))))))))))))) | none => .unmatch))))))))

def «Loadop_ok:clause:2» (input0 : context) (input1 : loadop_) : ExecutablePlan Call numtype :=
  (let C_0 : context := input0; (let nt : numtype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let «(packtype, extension)?» : (_root_.Option (packtype × extension)) := (input1).PACK; (.bind (.guard (((_root_.Option.isNone «(packtype, extension)?») = true))) (fun (_ : Unit) => (.bind (.call (Call.«$num_size» nt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let int_3 : _root_.Int := «eval:0»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : memtype := «exec:2»; (match «eval:1» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.guard ((u64 < (4294967296 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((nt : numtype))))))))))) | none => .unmatch))))))))))))))))

def «Loadop_ok:clause:3» (input0 : context) (input1 : loadop_) : ExecutablePlan Call numtype :=
  (let C_0 : context := input0; (let nt : numtype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let «(packtype, extension)?» : (_root_.Option (packtype × extension)) := (input1).PACK; (.bind (.guard (((_root_.Option.isNone «(packtype, extension)?») = true))) (fun (_ : Unit) => (.bind (.call (Call.«$num_size» nt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let int_3 : _root_.Int := «eval:0»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : memtype := «exec:2»; (match «eval:1» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure ((nt : numtype))))))))) | none => .unmatch))))))))))))))))

def Loadop_ok_clauses (input0 : context) (input1 : loadop_) : List (ExecutablePlan.Clause Call _root_.Unit numtype) :=
  [fun (_ : _root_.Unit) => («Loadop_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Loadop_ok:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Loadop_ok:clause:2»  input0 input1), fun (_ : _root_.Unit) => («Loadop_ok:clause:3»  input0 input1)]

def «Storeop_ok:clause:0» (input0 : context) (input1 : storeop_) : ExecutablePlan Call numtype :=
  (let C_0 : context := input0; (let nt : numtype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let pt? : (_root_.Option SpecTec.packtype) := (input1).PACK; (.bind (.guard (((_root_.Option.isSome pt?) = true))) (fun (_ : Unit) => (match pt? with | some «exec:1» => (let packtype : SpecTec.packtype := «exec:1»; (.bind (.call (Call.«$num_size» nt)) (fun («exec:2» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:2»; (.bind (.call (Call.Pack_ok «eval:0» packtype)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (let int_3 : _root_.Int := «eval:1»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:5» => (let «eval:2» : memtype := «exec:5»; (match «eval:2» with | .MemoryT «exec:6» «exec:7» => (let «at» : addrtype := «exec:6»; (let lim : limits := «exec:7»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.guard ((u64 < (4294967296 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((nt : numtype))))))))))) | none => .unmatch))))))))))))))) | none => .unmatch))))))))

def «Storeop_ok:clause:1» (input0 : context) (input1 : storeop_) : ExecutablePlan Call numtype :=
  (let C_0 : context := input0; (let nt : numtype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let pt? : (_root_.Option SpecTec.packtype) := (input1).PACK; (.bind (.guard (((_root_.Option.isSome pt?) = true))) (fun (_ : Unit) => (match pt? with | some «exec:1» => (let packtype : SpecTec.packtype := «exec:1»; (.bind (.call (Call.«$num_size» nt)) (fun («exec:2» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:2»; (.bind (.call (Call.Pack_ok «eval:0» packtype)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (let int_3 : _root_.Int := «eval:1»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:5» => (let «eval:2» : memtype := «exec:5»; (match «eval:2» with | .MemoryT «exec:6» «exec:7» => (let «at» : addrtype := «exec:6»; (let lim : limits := «exec:7»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure ((nt : numtype))))))))) | none => .unmatch))))))))))))))) | none => .unmatch))))))))

def «Storeop_ok:clause:2» (input0 : context) (input1 : storeop_) : ExecutablePlan Call numtype :=
  (let C_0 : context := input0; (let nt : numtype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let pt? : (_root_.Option packtype) := (input1).PACK; (.bind (.guard (((_root_.Option.isNone pt?) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$num_size» nt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let int_3 : _root_.Int := «eval:0»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : memtype := «exec:2»; (match «eval:1» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.guard ((u64 < (4294967296 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((nt : numtype))))))))))) | none => .unmatch))))))))))))))))

def «Storeop_ok:clause:3» (input0 : context) (input1 : storeop_) : ExecutablePlan Call numtype :=
  (let C_0 : context := input0; (let nt : numtype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let pt? : (_root_.Option packtype) := (input1).PACK; (.bind (.guard (((_root_.Option.isNone pt?) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$num_size» nt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let int_3 : _root_.Int := «eval:0»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : memtype := «exec:2»; (match «eval:1» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure ((nt : numtype))))))))) | none => .unmatch))))))))))))))))

def Storeop_ok_clauses (input0 : context) (input1 : storeop_) : List (ExecutablePlan.Clause Call _root_.Unit numtype) :=
  [fun (_ : _root_.Unit) => («Storeop_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Storeop_ok:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Storeop_ok:clause:2»  input0 input1), fun (_ : _root_.Unit) => («Storeop_ok:clause:3»  input0 input1)]

def «Vloadop_ok:clause:0» (input0 : context) (input1 : vloadop_) : ExecutablePlan Call vectype :=
  (let C_0 : context := input0; (let vt : vectype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let «(packtype, vextension)?» : (_root_.Option (SpecTec.packtype × SpecTec.vextension)) := (input1).PACK; (.bind (.guard (((_root_.Option.isSome «(packtype, vextension)?») = true))) (fun (_ : Unit) => (match «(packtype, vextension)?» with | some «exec:1» => (let packtype : SpecTec.packtype := («exec:1»).1; (let vextension : SpecTec.vextension := («exec:1»).2; (.bind (.call (Call.«$vec_size» vt)) (fun («exec:2» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:2»; (.bind (.call (Call.Pack_ok «eval:0» packtype)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (let int_3 : _root_.Int := «eval:1»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:5» => (let «eval:2» : memtype := «exec:5»; (match «eval:2» with | .MemoryT «exec:6» «exec:7» => (let «at» : addrtype := «exec:6»; (let lim : limits := «exec:7»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.guard ((u64 < (4294967296 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((vt : vectype))))))))))) | none => .unmatch)))))))))))))))) | none => .unmatch))))))))

def «Vloadop_ok:clause:1» (input0 : context) (input1 : vloadop_) : ExecutablePlan Call vectype :=
  (let C_0 : context := input0; (let vt : vectype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let «(packtype, vextension)?» : (_root_.Option (SpecTec.packtype × SpecTec.vextension)) := (input1).PACK; (.bind (.guard (((_root_.Option.isSome «(packtype, vextension)?») = true))) (fun (_ : Unit) => (match «(packtype, vextension)?» with | some «exec:1» => (let packtype : SpecTec.packtype := («exec:1»).1; (let vextension : SpecTec.vextension := («exec:1»).2; (.bind (.call (Call.«$vec_size» vt)) (fun («exec:2» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:2»; (.bind (.call (Call.Pack_ok «eval:0» packtype)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:4» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:4»; (let int_3 : _root_.Int := «eval:1»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:5» => (let «eval:2» : memtype := «exec:5»; (match «eval:2» with | .MemoryT «exec:6» «exec:7» => (let «at» : addrtype := «exec:6»; (let lim : limits := «exec:7»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure ((vt : vectype))))))))) | none => .unmatch)))))))))))))))) | none => .unmatch))))))))

def «Vloadop_ok:clause:2» (input0 : context) (input1 : vloadop_) : ExecutablePlan Call vectype :=
  (let C_0 : context := input0; (let vt : vectype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let «(packtype, vextension)?» : (_root_.Option (packtype × vextension)) := (input1).PACK; (.bind (.guard (((_root_.Option.isNone «(packtype, vextension)?») = true))) (fun (_ : Unit) => (.bind (.call (Call.«$vec_size» vt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let int_3 : _root_.Int := «eval:0»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : memtype := «exec:2»; (match «eval:1» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.guard ((u64 < (4294967296 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((vt : vectype))))))))))) | none => .unmatch))))))))))))))))

def «Vloadop_ok:clause:3» (input0 : context) (input1 : vloadop_) : ExecutablePlan Call vectype :=
  (let C_0 : context := input0; (let vt : vectype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let «(packtype, vextension)?» : (_root_.Option (packtype × vextension)) := (input1).PACK; (.bind (.guard (((_root_.Option.isNone «(packtype, vextension)?») = true))) (fun (_ : Unit) => (.bind (.call (Call.«$vec_size» vt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (let int_3 : _root_.Int := «eval:0»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:2» => (let «eval:1» : memtype := «exec:2»; (match «eval:1» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure ((vt : vectype))))))))) | none => .unmatch))))))))))))))))

def Vloadop_ok_clauses (input0 : context) (input1 : vloadop_) : List (ExecutablePlan.Clause Call _root_.Unit vectype) :=
  [fun (_ : _root_.Unit) => («Vloadop_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Vloadop_ok:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Vloadop_ok:clause:2»  input0 input1), fun (_ : _root_.Unit) => («Vloadop_ok:clause:3»  input0 input1)]

def «Vlaneop_ok:clause:0» (input0 : context) (input1 : vlaneop_) : ExecutablePlan Call vectype :=
  (let C_0 : context := input0; (let vt : vectype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let packtype : SpecTec.packtype := (input1).PACK; (.bind (.call (Call.«$vec_size» vt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (.bind (.call (Call.Pack_ok «eval:0» packtype)) (fun («exec:2» : _root_.Unit) => (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:3» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:3»; (let int_3 : _root_.Int := «eval:1»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:4» => (let «eval:2» : memtype := «exec:4»; (match «eval:2» with | .MemoryT «exec:5» «exec:6» => (let «at» : addrtype := «exec:5»; (let lim : limits := «exec:6»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.guard ((u64 < (4294967296 : _root_.Nat)))) (fun (_ : Unit) => (.pure ((vt : vectype))))))))))) | none => .unmatch)))))))))))))))))))

def «Vlaneop_ok:clause:1» (input0 : context) (input1 : vlaneop_) : ExecutablePlan Call vectype :=
  (let C_0 : context := input0; (let vt : vectype := (input1).TYPE; (let u32 : SpecTec.u32 := (input1).ALIGN; (let u64 : SpecTec.u64 := (input1).OFFSET; (let packtype : SpecTec.packtype := (input1).PACK; (.bind (.call (Call.«$vec_size» vt)) (fun («exec:1» : _root_.Int) => (let «eval:0» : _root_.Int := «exec:1»; (.bind (.call (Call.Pack_ok «eval:0» packtype)) (fun («exec:2» : _root_.Unit) => (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:3» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:3»; (let int_3 : _root_.Int := «eval:1»; (.bind (.guard ((((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≥ (_root_.Int.ofNat (1 : _root_.Nat))) ∧ ((«$lsl_» (_root_.Int.ofNat (1 : _root_.Nat)) (_root_.Int.ofNat u32)) ≤ int_3)))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[(0 : _root_.Nat)]?) with | some «exec:4» => (let «eval:2» : memtype := «exec:4»; (match «eval:2» with | .MemoryT «exec:5» «exec:6» => (let «at» : addrtype := «exec:5»; (let lim : limits := «exec:6»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.pure ((vt : vectype))))))))) | none => .unmatch)))))))))))))))))))

def Vlaneop_ok_clauses (input0 : context) (input1 : vlaneop_) : List (ExecutablePlan.Clause Call _root_.Unit vectype) :=
  [fun (_ : _root_.Unit) => («Vlaneop_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Vlaneop_ok:clause:1»  input0 input1)]

def «$unpacked_storage_type:clause:0» (input0 : storagetype) : ExecutablePlan Call valtype :=
  (let zt : storagetype := input0; (.bind (.guard (((«exec:match:storagetype:ValStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .ValStorageT «exec:1» => (let t : valtype := «exec:1»; (.pure ((t : valtype)))) | _ => .unmatch))))

def «$unpacked_storage_type:clause:1» (input0 : storagetype) : ExecutablePlan Call valtype :=
  (let zt : storagetype := input0; (.bind (.guard (((«exec:match:storagetype:PackStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .PackStorageT «exec:1» => (let pt : packtype := «exec:1»; (.pure (((@valtype.NumT (@numtype.I32T)) : valtype)))) | _ => .unmatch))))

def «$unpacked_storage_type_clauses» (input0 : storagetype) : List (ExecutablePlan.Clause Call _root_.Unit valtype) :=
  [fun (_ : _root_.Unit) => («$unpacked_storage_type:clause:0»  input0), fun (_ : _root_.Unit) => («$unpacked_storage_type:clause:1»  input0)]

def «$unpacked_field_type:clause:0» (input0 : fieldtype) : ExecutablePlan Call valtype :=
  (match input0 with | .FieldT «exec:1» «exec:2» => (let «mut» : SpecTec.«mut» := «exec:1»; (let zt : storagetype := «exec:2»; (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:3» : valtype) => (let «eval:0» : valtype := «exec:3»; (.pure ((«eval:0» : valtype)))))))))

def «$unpacked_field_type_clauses» (input0 : fieldtype) : List (ExecutablePlan.Clause Call _root_.Unit valtype) :=
  [fun (_ : _root_.Unit) => («$unpacked_field_type:clause:0»  input0)]

def «$is_packed_storage_type:clause:0» (input0 : storagetype) : ExecutablePlan Call _root_.Bool :=
  (let zt : storagetype := input0; (.bind (.guard (((«exec:match:storagetype:ValStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .ValStorageT «exec:1» => (let _t : valtype := «exec:1»; (.pure ((false : _root_.Bool)))) | _ => .unmatch))))

def «$is_packed_storage_type:clause:1» (input0 : storagetype) : ExecutablePlan Call _root_.Bool :=
  (let zt : storagetype := input0; (.bind (.guard (((«exec:match:storagetype:PackStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .PackStorageT «exec:1» => (let _pt : packtype := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch))))

def «$is_packed_storage_type_clauses» (input0 : storagetype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$is_packed_storage_type:clause:0»  input0), fun (_ : _root_.Unit) => («$is_packed_storage_type:clause:1»  input0)]

def «Instr_ok:struct.new.explicit:iter:1:clause:0» (input0 : (_root_.List fieldtype)) : ExecutablePlan Call (_root_.List valtype) :=
  (match input0 with | [] => (.pure ((([] : (_root_.List valtype)) : (_root_.List valtype)))) | _ :: _ => .unmatch)

def «Instr_ok:struct.new.explicit:iter:1:clause:1» (input0 : (_root_.List fieldtype)) : ExecutablePlan Call (_root_.List valtype) :=
  (match input0 with | «exec:2» :: «exec:1» => (let yt : fieldtype := «exec:2»; (let «tail:0» : (_root_.List fieldtype) := «exec:1»; (.bind (.call (Call.«$unpacked_field_type» yt)) (fun («exec:3» : valtype) => (let «eval:2» : valtype := «exec:3»; (let t : valtype := «eval:2»; (.bind (.call (Call.«Instr_ok:struct.new.explicit:iter:1» «tail:0»)) (fun («exec:4» : (_root_.List valtype)) => (let «tail:1» : (_root_.List valtype) := «exec:4»; (.pure (((t :: «tail:1») : (_root_.List valtype))))))))))))) | [] => .unmatch)

def «Instr_ok:struct.new.explicit:iter:1_clauses» (input0 : (_root_.List fieldtype)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List valtype)) :=
  [fun (_ : _root_.Unit) => («Instr_ok:struct.new.explicit:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Instr_ok:struct.new.explicit:iter:1:clause:1»  input0)]

def «$functype_of_strtype:clause:0» (input0 : strtype) : ExecutablePlan Call functype :=
  (let strt : strtype := input0; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefFuncT «exec:1» => (let ft : functype := «exec:1»; (.pure ((ft : functype)))) | _ => .unmatch))))

def «$functype_of_strtype_clauses» (input0 : strtype) : List (ExecutablePlan.Clause Call _root_.Unit functype) :=
  [fun (_ : _root_.Unit) => («$functype_of_strtype:clause:0»  input0)]

def «$abs_of_str_type:clause:0» (input0 : strtype) : ExecutablePlan Call heaptype :=
  (let strt : strtype := input0; (.bind (.guard (((«exec:match:strtype:DefStructT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefStructT «exec:1» => (let _strctt : structtype := «exec:1»; (.pure (((@heaptype.StructHT) : heaptype)))) | _ => .unmatch))))

def «$abs_of_str_type:clause:1» (input0 : strtype) : ExecutablePlan Call heaptype :=
  (let strt : strtype := input0; (.bind (.guard (((«exec:match:strtype:DefArrayT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefArrayT «exec:1» => (let _arrt : arraytype := «exec:1»; (.pure (((@heaptype.ArrayHT) : heaptype)))) | _ => .unmatch))))

def «$abs_of_str_type:clause:2» (input0 : strtype) : ExecutablePlan Call heaptype :=
  (let strt : strtype := input0; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefFuncT «exec:1» => (let _ft : functype := «exec:1»; (.pure (((@heaptype.FuncHT) : heaptype)))) | _ => .unmatch))))

def «$abs_of_str_type_clauses» (input0 : strtype) : List (ExecutablePlan.Clause Call _root_.Unit heaptype) :=
  [fun (_ : _root_.Unit) => («$abs_of_str_type:clause:0»  input0), fun (_ : _root_.Unit) => («$abs_of_str_type:clause:1»  input0), fun (_ : _root_.Unit) => («$abs_of_str_type:clause:2»  input0)]

def «$s_unroll:clause:0» (input0 : typevar) (input1 : rectype) : ExecutablePlan Call heaptype :=
  (let tv : typevar := input0; (let rect : rectype := input1; (let tv' : typevar := tv; (.bind (.guard (((«exec:match:typevar:RecX» tv') = true))) (fun (_ : Unit) => (match tv' with | .RecX «exec:1» => (let n : SpecTec.n := «exec:1»; (.pure (((@heaptype.DefHT (@deftype.DefT rect n)) : heaptype)))) | _ => .unmatch))))))

def «$s_unroll:clause:1» (input0 : typevar) (input1 : rectype) : ExecutablePlan Call heaptype :=
  (let tv : typevar := input0; (let rect : rectype := input1; (.pure (((@heaptype.VarHT tv) : heaptype)))))

def «$s_unroll_clauses» (input0 : typevar) (input1 : rectype) : List (ExecutablePlan.Clause Call _root_.Unit heaptype) :=
  [fun (_ : _root_.Unit) => («$s_unroll:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$s_unroll:clause:1»  input0 input1)]

def «$s_roll:clause:0» (input0 : typevar) (input1 : (typeidx × typeidx)) : ExecutablePlan Call heaptype :=
  (let tv : typevar := input0; (let x : idx := (input1).1; (let y : idx := (input1).2; (let tv' : typevar := tv; (.bind (.guard (((«exec:match:typevar:StatX» tv') = true))) (fun (_ : Unit) => (match tv' with | .StatX «exec:1» => (let x' : idx := «exec:1»; (.bind (.guard (((x ≤ x') ∧ (x' < y)))) (fun (_ : Unit) => (let int : _root_.Int := ((_root_.Int.ofNat x') - (_root_.Int.ofNat x)); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:2» => (let «eval:0» : idx := «exec:2»; (let x'' : idx := «eval:0»; (.pure (((@heaptype.VarHT (@typevar.RecX x'')) : heaptype))))) | none => .unmatch))))))) | _ => .unmatch)))))))

def «$s_roll:clause:1» (input0 : typevar) (input1 : (typeidx × typeidx)) : ExecutablePlan Call heaptype :=
  (let tv : typevar := input0; (let x : idx := (input1).1; (let y : idx := (input1).2; (.pure (((@heaptype.VarHT tv) : heaptype))))))

def «$s_roll_clauses» (input0 : typevar) (input1 : (typeidx × typeidx)) : List (ExecutablePlan.Clause Call _root_.Unit heaptype) :=
  [fun (_ : _root_.Unit) => («$s_roll:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$s_roll:clause:1»  input0 input1)]

def «$free_typevar:clause:0» (input0 : typevar) : ExecutablePlan Call free :=
  (let tv : typevar := input0; (.bind (.guard (((«exec:match:typevar:StatX» tv) = true))) (fun (_ : Unit) => (match tv with | .StatX «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_typevar:clause:1» (input0 : typevar) : ExecutablePlan Call free :=
  (let tv : typevar := input0; (.bind (.guard (((«exec:match:typevar:RecX» tv) = true))) (fun (_ : Unit) => (match tv with | .RecX «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_typevar_clauses» (input0 : typevar) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_typevar:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typevar:clause:1»  input0)]

def «$subst_of:clause:0» (input0 : typevar) (input1 : (_root_.List deftype)) : ExecutablePlan Call heaptype :=
  (let tv : typevar := input0; (let «dt*» : (_root_.List deftype) := input1; (.bind (.guard (((«exec:match:typevar:StatX» tv) = true))) (fun (_ : Unit) => (match tv with | .StatX «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length «dt*»)))) (fun (_ : Unit) => (match («dt*»[x]?) with | some «exec:2» => (let «eval:0» : deftype := «exec:2»; (.pure (((@heaptype.DefHT «eval:0») : heaptype)))) | none => .unmatch)))) | _ => .unmatch)))))

def «$subst_of:clause:1» (input0 : typevar) (input1 : (_root_.List deftype)) : ExecutablePlan Call heaptype :=
  (let tv : typevar := input0; (let «dt*» : (_root_.List deftype) := input1; (.bind (.guard (((«exec:match:typevar:RecX» tv) = true))) (fun (_ : Unit) => (match tv with | .RecX «exec:1» => (let x : idx := «exec:1»; (.pure (((@heaptype.VarHT (@typevar.RecX x)) : heaptype)))) | _ => .unmatch)))))

def «$subst_of_clauses» (input0 : typevar) (input1 : (_root_.List deftype)) : List (ExecutablePlan.Clause Call _root_.Unit heaptype) :=
  [fun (_ : _root_.Unit) => («$subst_of:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_of:clause:1»  input0 input1)]

def «$is_num_type:clause:0» (input0 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:NumT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .NumT «exec:1» => (let _nt : numtype := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch))))

def «$is_num_type:clause:1» (input0 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:BotT» valtype) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))

def «$is_num_type:clause:2» (input0 : valtype) : ExecutablePlan Call _root_.Bool :=
  (let t : valtype := input0; (.pure ((false : _root_.Bool))))

def «$is_num_type_clauses» (input0 : valtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$is_num_type:clause:0»  input0), fun (_ : _root_.Unit) => («$is_num_type:clause:1»  input0), fun (_ : _root_.Unit) => («$is_num_type:clause:2»  input0)]

def «$peek_ref:clause:0» (input0 : _root_.Nat) (input1 : inferresulttype) : ExecutablePlan Call reftype :=
  (let n : SpecTec.n := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t*» : (_root_.List SpecTec.valtype) := (input1).2; (.bind (.call (Call.«$peek» n (ellipses, «t*»))) (fun («exec:1» : SpecTec.valtype) => (let «eval:0» : SpecTec.valtype := «exec:1»; (let valtype : SpecTec.valtype := «eval:0»; (.bind (.guard (((«exec:match:valtype:RefT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .RefT «exec:2» => (let rt : reftype := «exec:2»; (.pure ((rt : reftype)))) | _ => .unmatch))))))))))

def «$peek_ref:clause:1» (input0 : _root_.Nat) (input1 : inferresulttype) : ExecutablePlan Call reftype :=
  (let n : SpecTec.n := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t*» : (_root_.List valtype) := (input1).2; (.bind (.call (Call.«$peek» n (ellipses, «t*»))) (fun («exec:1» : valtype) => (let «eval:0» : valtype := «exec:1»; (.bind (.guard ((@valtype.BotT) = «eval:0»)) (fun (_ : Unit) => (.pure (((@reftype.«% %» (@null.NoNull) (@heaptype.BotHT)) : reftype)))))))))))

def «$peek_ref_clauses» (input0 : _root_.Nat) (input1 : inferresulttype) : List (ExecutablePlan.Clause Call _root_.Unit reftype) :=
  [fun (_ : _root_.Unit) => («$peek_ref:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$peek_ref:clause:1»  input0 input1)]

def «$is_vec_type:clause:0» (input0 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:VecT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .VecT «exec:1» => (let _vt : vectype := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch))))

def «$is_vec_type:clause:1» (input0 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:BotT» valtype) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))

def «$is_vec_type:clause:2» (input0 : valtype) : ExecutablePlan Call _root_.Bool :=
  (let t : valtype := input0; (.pure ((false : _root_.Bool))))

def «$is_vec_type_clauses» (input0 : valtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$is_vec_type:clause:0»  input0), fun (_ : _root_.Unit) => («$is_vec_type:clause:1»  input0), fun (_ : _root_.Unit) => («$is_vec_type:clause:2»  input0)]

def «$defaultable:clause:0» (input0 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:NumT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .NumT «exec:1» => (let nt : numtype := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch))))

def «$defaultable:clause:1» (input0 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:VecT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .VecT «exec:1» => (let vt : vectype := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch))))

def «$defaultable:clause:2» (input0 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:RefT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .RefT «exec:1» => (match «exec:1» with | .«% %» «exec:2» «exec:3» => (let null : SpecTec.null := «exec:2»; (let ht : heaptype := «exec:3»; (.pure (((_root_.Decidable.decide (null = (@SpecTec.null.Null))) : _root_.Bool)))))) | _ => .unmatch))))

def «$defaultable:clause:3» (input0 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:BotT» valtype) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))

def «$defaultable_clauses» (input0 : valtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$defaultable:clause:0»  input0), fun (_ : _root_.Unit) => («$defaultable:clause:1»  input0), fun (_ : _root_.Unit) => («$defaultable:clause:2»  input0), fun (_ : _root_.Unit) => («$defaultable:clause:3»  input0)]

def «Instr_ok:struct.new.implicit:iter:1:clause:0» (input0 : (_root_.List fieldtype)) : ExecutablePlan Call _root_.Unit :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)

def «Instr_ok:struct.new.implicit:iter:1:clause:1» (input0 : (_root_.List fieldtype)) : ExecutablePlan Call _root_.Unit :=
  (match input0 with | «exec:2» :: «exec:1» => (let yt : fieldtype := «exec:2»; (let «tail:0» : (_root_.List fieldtype) := «exec:1»; (.bind (.call (Call.«$unpacked_field_type» yt)) (fun («exec:3» : valtype) => (let «eval:2» : valtype := «exec:3»; (.bind (.call (Call.«$defaultable» «eval:2»)) (fun («exec:4» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:3» = true))) (fun (_ : Unit) => (.bind (.call (Call.«Instr_ok:struct.new.implicit:iter:1» «tail:0»)) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))))) | [] => .unmatch)

def «Instr_ok:struct.new.implicit:iter:1_clauses» (input0 : (_root_.List fieldtype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Instr_ok:struct.new.implicit:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Instr_ok:struct.new.implicit:iter:1:clause:1»  input0)]

def «$check_vbop_shuffle:clause:0» (input0 : vbinop_) : ExecutablePlan Call _root_.Bool :=
  (match input0 with | .V128 «exec:1» => (let «laneop<vibinop, vibinop, vibinop, vibinop, vfbinop, vfbinop>» : (laneop SpecTec.vibinop SpecTec.vibinop SpecTec.vibinop SpecTec.vibinop vfbinop vfbinop) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I8x16» «laneop<vibinop, vibinop, vibinop, vibinop, vfbinop, vfbinop>») = true))) (fun (_ : Unit) => (match «laneop<vibinop, vibinop, vibinop, vibinop, vfbinop, vfbinop>» with | .I8x16 «exec:2» => (let vibinop : SpecTec.vibinop := «exec:2»; (.bind (.guard (((«exec:match:vibinop:Shuffle» vibinop) = true))) (fun (_ : Unit) => (match vibinop with | .Shuffle «exec:3» => (let «_nat*» : (_root_.List _root_.Nat) := «exec:3»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))) | _ => .unmatch)))))

def «$check_vbop_shuffle:clause:1» (input0 : vbinop_) : ExecutablePlan Call _root_.Bool :=
  (let vbop : vbinop_ := input0; (.pure ((false : _root_.Bool))))

def «$check_vbop_shuffle_clauses» (input0 : vbinop_) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$check_vbop_shuffle:clause:0»  input0), fun (_ : _root_.Unit) => («$check_vbop_shuffle:clause:1»  input0)]

def «Vecbinop_ok:clause:0» (input0 : vbinop_) : ExecutablePlan Call _root_.Unit :=
  (let vbop : vbinop_ := input0; (match vbop with | .V128 «exec:1» => (let «laneop<vibinop, vibinop, vibinop, vibinop, vfbinop, vfbinop>» : (laneop SpecTec.vibinop SpecTec.vibinop SpecTec.vibinop SpecTec.vibinop vfbinop vfbinop) := «exec:1»; (.bind (.guard (((«exec:match:laneop:I8x16» «laneop<vibinop, vibinop, vibinop, vibinop, vfbinop, vfbinop>») = true))) (fun (_ : Unit) => (match «laneop<vibinop, vibinop, vibinop, vibinop, vfbinop, vfbinop>» with | .I8x16 «exec:2» => (let vibinop : SpecTec.vibinop := «exec:2»; (.bind (.guard (((«exec:match:vibinop:Shuffle» vibinop) = true))) (fun (_ : Unit) => (match vibinop with | .Shuffle «exec:3» => (let «i*» : (_root_.List i) := «exec:3»; (.bind (.call (Call.«$check_lane_index» «i*»)) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «Vecbinop_ok:clause:1» (input0 : vbinop_) : ExecutablePlan Call _root_.Unit :=
  (let vbop : vbinop_ := input0; (.bind (.call (Call.«$check_vbop_shuffle» vbop)) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))

def Vecbinop_ok_clauses (input0 : vbinop_) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Vecbinop_ok:clause:0»  input0), fun (_ : _root_.Unit) => («Vecbinop_ok:clause:1»  input0)]

def «$subst_heaptype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : heaptype) : ExecutablePlan Call heaptype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let ht : heaptype := input2; (.bind (.guard ((((((((((((((ht = (@heaptype.AnyHT)) ∨ (ht = (@heaptype.NoneHT))) ∨ (ht = (@heaptype.EqHT))) ∨ (ht = (@heaptype.I31HT))) ∨ (ht = (@heaptype.StructHT))) ∨ (ht = (@heaptype.ArrayHT))) ∨ (ht = (@heaptype.FuncHT))) ∨ (ht = (@heaptype.NoFuncHT))) ∨ (ht = (@heaptype.ExnHT))) ∨ (ht = (@heaptype.NoExnHT))) ∨ (ht = (@heaptype.ExternHT))) ∨ (ht = (@heaptype.NoExternHT))) ∨ (ht = (@heaptype.BotHT))))) (fun (_ : Unit) => (.pure ((ht : heaptype))))))))

def «$subst_heaptype:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : heaptype) : ExecutablePlan Call heaptype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let ht : heaptype := input2; (let ht' : heaptype := ht; (.bind (.guard (((«sub:heaptype:heaptypeVar» ht') = true))) (fun (_ : Unit) => (match (@«$subst_heaptype:case_2:downcast:0» X_T ht') with | some «exec:1» => (let «eval:0» : heaptypeVar := «exec:1»; (match «eval:0» with | .VarHT «exec:2» => (let tv : typevar := «exec:2»; (.bind (.call («$s» tv X)) (fun («exec:3» : heaptype) => (let «eval:1» : heaptype := «exec:3»; (.pure ((«eval:1» : heaptype))))))))) | none => .unmatch)))))))

def «$subst_heaptype:clause:2» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : heaptype) : ExecutablePlan Call heaptype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let ht : heaptype := input2; (let ht' : heaptype := ht; (.bind (.guard (((«exec:match:heaptype:DefHT» ht') = true))) (fun (_ : Unit) => (match ht' with | .DefHT «exec:1» => (let dt : deftype := «exec:1»; (.pure (((@heaptype.DefHT dt) : heaptype)))) | _ => .unmatch)))))))

def «$subst_heaptype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : heaptype) : List (ExecutablePlan.Clause Call _root_.Unit heaptype) :=
  [fun (_ : _root_.Unit) => («$subst_heaptype:clause:0» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_heaptype:clause:1» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_heaptype:clause:2» X_T input0 input1 input2)]

def «$subst_subtype:case_1:iter:0:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List heaptype)) : ExecutablePlan Call (_root_.List heaptype) :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List heaptype)) : (_root_.List heaptype)))) | _ :: _ => .unmatch)))

def «$subst_subtype:case_1:iter:0:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List heaptype)) : ExecutablePlan Call (_root_.List heaptype) :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | «exec:2» :: «exec:1» => (let ht : heaptype := «exec:2»; (let «tail:0» : (_root_.List heaptype) := «exec:1»; (.bind (.call (Call.«$subst_heaptype» X_T X «$s» ht)) (fun («exec:3» : heaptype) => (let «eval:1» : heaptype := «exec:3»; (let ht' : heaptype := «eval:1»; (.bind (.call (Call.«$subst_subtype:case_1:iter:0» X_T X «$s» «tail:0»)) (fun («exec:4» : (_root_.List heaptype)) => (let «tail:1» : (_root_.List heaptype) := «exec:4»; (.pure (((ht' :: «tail:1») : (_root_.List heaptype))))))))))))) | [] => .unmatch)))

def «$subst_subtype:case_1:iter:0_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List heaptype)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List heaptype)) :=
  [fun (_ : _root_.Unit) => («$subst_subtype:case_1:iter:0:clause:0» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_subtype:case_1:iter:0:clause:1» X_T input0 input1 input2)]

def «$subst_reftype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : reftype) : ExecutablePlan Call reftype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | .«% %» «exec:1» «exec:2» => (let null : SpecTec.null := «exec:1»; (let ht : heaptype := «exec:2»; (.bind (.call (Call.«$subst_heaptype» X_T X «$s» ht)) (fun («exec:3» : heaptype) => (let «eval:0» : heaptype := «exec:3»; (let ht' : heaptype := «eval:0»; (.pure (((@reftype.«% %» null ht') : reftype))))))))))))

def «$subst_reftype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : reftype) : List (ExecutablePlan.Clause Call _root_.Unit reftype) :=
  [fun (_ : _root_.Unit) => («$subst_reftype:clause:0» X_T input0 input1 input2)]

def «$subst_valtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : SpecTec.valtype) : ExecutablePlan Call valtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let t : SpecTec.valtype := input2; (let valtype : SpecTec.valtype := t; (.bind (.guard (((«exec:match:valtype:NumT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .NumT «exec:1» => (let nt : numtype := «exec:1»; (.pure (((@SpecTec.valtype.NumT nt) : SpecTec.valtype)))) | _ => .unmatch)))))))

def «$subst_valtype:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : SpecTec.valtype) : ExecutablePlan Call valtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let t : SpecTec.valtype := input2; (let valtype : SpecTec.valtype := t; (.bind (.guard (((«exec:match:valtype:VecT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .VecT «exec:1» => (let vt : vectype := «exec:1»; (.pure (((@SpecTec.valtype.VecT vt) : SpecTec.valtype)))) | _ => .unmatch)))))))

def «$subst_valtype:clause:2» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : SpecTec.valtype) : ExecutablePlan Call valtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let t : SpecTec.valtype := input2; (let valtype : SpecTec.valtype := t; (.bind (.guard (((«exec:match:valtype:RefT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .RefT «exec:1» => (let rt : reftype := «exec:1»; (.bind (.call (Call.«$subst_reftype» X_T X «$s» rt)) (fun («exec:2» : reftype) => (let «eval:0» : reftype := «exec:2»; (let rt' : reftype := «eval:0»; (.pure (((@SpecTec.valtype.RefT rt') : SpecTec.valtype)))))))) | _ => .unmatch)))))))

def «$subst_valtype:clause:3» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : valtype) : ExecutablePlan Call valtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let t : valtype := input2; (.bind (.guard ((@valtype.BotT) = t)) (fun (_ : Unit) => (.pure (((@valtype.BotT) : valtype))))))))

def «$subst_valtype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : valtype) : List (ExecutablePlan.Clause Call _root_.Unit valtype) :=
  [fun (_ : _root_.Unit) => («$subst_valtype:clause:0» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_valtype:clause:1» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_valtype:clause:2» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_valtype:clause:3» X_T input0 input1 input2)]

def «$subst_resulttype:case_1:iter:0:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List valtype)) : ExecutablePlan Call (_root_.List valtype) :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List valtype)) : (_root_.List valtype)))) | _ :: _ => .unmatch)))

def «$subst_resulttype:case_1:iter:0:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List valtype)) : ExecutablePlan Call (_root_.List valtype) :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | «exec:2» :: «exec:1» => (let t : valtype := «exec:2»; (let «tail:0» : (_root_.List valtype) := «exec:1»; (.bind (.call (Call.«$subst_valtype» X_T X «$s» t)) (fun («exec:3» : valtype) => (let «eval:1» : valtype := «exec:3»; (let t' : valtype := «eval:1»; (.bind (.call (Call.«$subst_resulttype:case_1:iter:0» X_T X «$s» «tail:0»)) (fun («exec:4» : (_root_.List valtype)) => (let «tail:1» : (_root_.List valtype) := «exec:4»; (.pure (((t' :: «tail:1») : (_root_.List valtype))))))))))))) | [] => .unmatch)))

def «$subst_resulttype:case_1:iter:0_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List valtype)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List valtype)) :=
  [fun (_ : _root_.Unit) => («$subst_resulttype:case_1:iter:0:clause:0» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_resulttype:case_1:iter:0:clause:1» X_T input0 input1 input2)]

def «$subst_resulttype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : resulttype) : ExecutablePlan Call resulttype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let «t*» : (_root_.List valtype) := input2; (.bind (.call (Call.«$subst_resulttype:case_1:iter:0» X_T X «$s» «t*»)) (fun («exec:1» : (_root_.List valtype)) => (let «t'*» : (_root_.List valtype) := «exec:1»; (.pure ((«t'*» : resulttype)))))))))

def «$subst_resulttype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : resulttype) : List (ExecutablePlan.Clause Call _root_.Unit resulttype) :=
  [fun (_ : _root_.Unit) => («$subst_resulttype:clause:0» X_T input0 input1 input2)]

def «$subst_functype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : functype) : ExecutablePlan Call functype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | .FuncT «exec:1» «exec:2» => (let resulttype_1 : resulttype := «exec:1»; (let resulttype_2 : resulttype := «exec:2»; (.bind (.call (Call.«$subst_resulttype» X_T X «$s» resulttype_1)) (fun («exec:3» : resulttype) => (let «eval:0» : resulttype := «exec:3»; (let resulttype_1' : resulttype := «eval:0»; (.bind (.call (Call.«$subst_resulttype» X_T X «$s» resulttype_2)) (fun («exec:4» : resulttype) => (let «eval:1» : resulttype := «exec:4»; (let resulttype_2' : resulttype := «eval:1»; (.pure (((@functype.FuncT resulttype_1' resulttype_2') : functype))))))))))))))))

def «$subst_functype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : functype) : List (ExecutablePlan.Clause Call _root_.Unit functype) :=
  [fun (_ : _root_.Unit) => («$subst_functype:clause:0» X_T input0 input1 input2)]

def «$subst_storagetype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : storagetype) : ExecutablePlan Call storagetype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let zt : storagetype := input2; (.bind (.guard (((«exec:match:storagetype:ValStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .ValStorageT «exec:1» => (let t : valtype := «exec:1»; (.bind (.call (Call.«$subst_valtype» X_T X «$s» t)) (fun («exec:2» : valtype) => (let «eval:0» : valtype := «exec:2»; (let t' : valtype := «eval:0»; (.pure (((@storagetype.ValStorageT t') : storagetype)))))))) | _ => .unmatch))))))

def «$subst_storagetype:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : storagetype) : ExecutablePlan Call storagetype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let zt : storagetype := input2; (.bind (.guard (((«exec:match:storagetype:PackStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .PackStorageT «exec:1» => (let pt : packtype := «exec:1»; (.pure (((@storagetype.PackStorageT pt) : storagetype)))) | _ => .unmatch))))))

def «$subst_storagetype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : storagetype) : List (ExecutablePlan.Clause Call _root_.Unit storagetype) :=
  [fun (_ : _root_.Unit) => («$subst_storagetype:clause:0» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_storagetype:clause:1» X_T input0 input1 input2)]

def «$subst_fieldtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : fieldtype) : ExecutablePlan Call fieldtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | .FieldT «exec:1» «exec:2» => (let «mut» : SpecTec.«mut» := «exec:1»; (let zt : storagetype := «exec:2»; (.bind (.call (Call.«$subst_storagetype» X_T X «$s» zt)) (fun («exec:3» : storagetype) => (let «eval:0» : storagetype := «exec:3»; (let zt' : storagetype := «eval:0»; (.pure (((@fieldtype.FieldT «mut» zt') : fieldtype))))))))))))

def «$subst_fieldtype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : fieldtype) : List (ExecutablePlan.Clause Call _root_.Unit fieldtype) :=
  [fun (_ : _root_.Unit) => («$subst_fieldtype:clause:0» X_T input0 input1 input2)]

def «$subst_structtype:case_1:iter:0:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List fieldtype)) : ExecutablePlan Call (_root_.List fieldtype) :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List fieldtype)) : (_root_.List fieldtype)))) | _ :: _ => .unmatch)))

def «$subst_structtype:case_1:iter:0:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List fieldtype)) : ExecutablePlan Call (_root_.List fieldtype) :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | «exec:2» :: «exec:1» => (let yt : fieldtype := «exec:2»; (let «tail:0» : (_root_.List fieldtype) := «exec:1»; (.bind (.call (Call.«$subst_fieldtype» X_T X «$s» yt)) (fun («exec:3» : fieldtype) => (let «eval:1» : fieldtype := «exec:3»; (let yt' : fieldtype := «eval:1»; (.bind (.call (Call.«$subst_structtype:case_1:iter:0» X_T X «$s» «tail:0»)) (fun («exec:4» : (_root_.List fieldtype)) => (let «tail:1» : (_root_.List fieldtype) := «exec:4»; (.pure (((yt' :: «tail:1») : (_root_.List fieldtype))))))))))))) | [] => .unmatch)))

def «$subst_structtype:case_1:iter:0_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List fieldtype)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List fieldtype)) :=
  [fun (_ : _root_.Unit) => («$subst_structtype:case_1:iter:0:clause:0» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_structtype:case_1:iter:0:clause:1» X_T input0 input1 input2)]

def «$subst_structtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : structtype) : ExecutablePlan Call structtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | .StructT «exec:1» => (let «yt*» : (_root_.List fieldtype) := «exec:1»; (.bind (.call (Call.«$subst_structtype:case_1:iter:0» X_T X «$s» «yt*»)) (fun («exec:2» : (_root_.List fieldtype)) => (let «yt'*» : (_root_.List fieldtype) := «exec:2»; (.pure (((@structtype.StructT «yt'*») : structtype))))))))))

def «$subst_structtype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : structtype) : List (ExecutablePlan.Clause Call _root_.Unit structtype) :=
  [fun (_ : _root_.Unit) => («$subst_structtype:clause:0» X_T input0 input1 input2)]

def «$subst_arraytype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : arraytype) : ExecutablePlan Call arraytype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | .ArrayT «exec:1» => (let yt : fieldtype := «exec:1»; (.bind (.call (Call.«$subst_fieldtype» X_T X «$s» yt)) (fun («exec:2» : fieldtype) => (let «eval:0» : fieldtype := «exec:2»; (let yt' : fieldtype := «eval:0»; (.pure (((@arraytype.ArrayT yt') : arraytype)))))))))))

def «$subst_arraytype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : arraytype) : List (ExecutablePlan.Clause Call _root_.Unit arraytype) :=
  [fun (_ : _root_.Unit) => («$subst_arraytype:clause:0» X_T input0 input1 input2)]

def «$subst_strtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : strtype) : ExecutablePlan Call strtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let strt : strtype := input2; (let strt' : strtype := strt; (.bind (.guard (((«exec:match:strtype:DefStructT» strt') = true))) (fun (_ : Unit) => (match strt' with | .DefStructT «exec:1» => (let structtype : SpecTec.structtype := «exec:1»; (.bind (.call (Call.«$subst_structtype» X_T X «$s» structtype)) (fun («exec:2» : SpecTec.structtype) => (let «eval:0» : SpecTec.structtype := «exec:2»; (let structtype' : SpecTec.structtype := «eval:0»; (.pure (((@strtype.DefStructT structtype') : strtype)))))))) | _ => .unmatch)))))))

def «$subst_strtype:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : strtype) : ExecutablePlan Call strtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let strt : strtype := input2; (let strt' : strtype := strt; (.bind (.guard (((«exec:match:strtype:DefArrayT» strt') = true))) (fun (_ : Unit) => (match strt' with | .DefArrayT «exec:1» => (let arraytype : SpecTec.arraytype := «exec:1»; (.bind (.call (Call.«$subst_arraytype» X_T X «$s» arraytype)) (fun («exec:2» : SpecTec.arraytype) => (let «eval:0» : SpecTec.arraytype := «exec:2»; (let arraytype' : SpecTec.arraytype := «eval:0»; (.pure (((@strtype.DefArrayT arraytype') : strtype)))))))) | _ => .unmatch)))))))

def «$subst_strtype:clause:2» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : strtype) : ExecutablePlan Call strtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let strt : strtype := input2; (let strt' : strtype := strt; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt') = true))) (fun (_ : Unit) => (match strt' with | .DefFuncT «exec:1» => (let functype : SpecTec.functype := «exec:1»; (.bind (.call (Call.«$subst_functype» X_T X «$s» functype)) (fun («exec:2» : SpecTec.functype) => (let «eval:0» : SpecTec.functype := «exec:2»; (let functype' : SpecTec.functype := «eval:0»; (.pure (((@strtype.DefFuncT functype') : strtype)))))))) | _ => .unmatch)))))))

def «$subst_strtype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : strtype) : List (ExecutablePlan.Clause Call _root_.Unit strtype) :=
  [fun (_ : _root_.Unit) => («$subst_strtype:clause:0» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_strtype:clause:1» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_strtype:clause:2» X_T input0 input1 input2)]

def «$subst_subtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : subtype) : ExecutablePlan Call subtype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let st : subtype := input2; (match st with | .SubT «exec:1» «exec:2» «exec:3» => (let fin : final := «exec:1»; (let «ht*» : (_root_.List heaptype) := «exec:2»; (let strt : strtype := «exec:3»; (.bind (.call (Call.«$subst_subtype:case_1:iter:0» X_T X «$s» «ht*»)) (fun («exec:4» : (_root_.List heaptype)) => (let «ht'*» : (_root_.List heaptype) := «exec:4»; (.bind (.call (Call.«$subst_strtype» X_T X «$s» strt)) (fun («exec:5» : strtype) => (let «eval:2» : strtype := «exec:5»; (let strt' : strtype := «eval:2»; (.pure (((@subtype.SubT fin «ht'*» strt') : subtype)))))))))))))))))

def «$subst_subtype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : subtype) : List (ExecutablePlan.Clause Call _root_.Unit subtype) :=
  [fun (_ : _root_.Unit) => («$subst_subtype:clause:0» X_T input0 input1 input2)]

def «$subst_rectype:case_1:iter:0:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List subtype)) : ExecutablePlan Call (_root_.List subtype) :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List subtype)) : (_root_.List subtype)))) | _ :: _ => .unmatch)))

def «$subst_rectype:case_1:iter:0:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List subtype)) : ExecutablePlan Call (_root_.List subtype) :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | «exec:2» :: «exec:1» => (let st : subtype := «exec:2»; (let «tail:0» : (_root_.List subtype) := «exec:1»; (.bind (.call (Call.«$subst_subtype» X_T X «$s» st)) (fun («exec:3» : subtype) => (let «eval:1» : subtype := «exec:3»; (let st' : subtype := «eval:1»; (.bind (.call (Call.«$subst_rectype:case_1:iter:0» X_T X «$s» «tail:0»)) (fun («exec:4» : (_root_.List subtype)) => (let «tail:1» : (_root_.List subtype) := «exec:4»; (.pure (((st' :: «tail:1») : (_root_.List subtype))))))))))))) | [] => .unmatch)))

def «$subst_rectype:case_1:iter:0_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List subtype)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List subtype)) :=
  [fun (_ : _root_.Unit) => («$subst_rectype:case_1:iter:0:clause:0» X_T input0 input1 input2), fun (_ : _root_.Unit) => («$subst_rectype:case_1:iter:0:clause:1» X_T input0 input1 input2)]

def «$subst_rectype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : rectype) : ExecutablePlan Call rectype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (let rect : rectype := input2; (match rect with | .RecT «exec:1» => (let «st*» : (_root_.List subtype) := «exec:1»; (.bind (.call (Call.«$subst_rectype:case_1:iter:0» X_T X «$s» «st*»)) (fun («exec:2» : (_root_.List subtype)) => (let «st'*» : (_root_.List subtype) := «exec:2»; (.pure (((@rectype.RecT «st'*») : rectype)))))))))))

def «$subst_rectype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : rectype) : List (ExecutablePlan.Clause Call _root_.Unit rectype) :=
  [fun (_ : _root_.Unit) => («$subst_rectype:clause:0» X_T input0 input1 input2)]

def «$subst_deftype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : deftype) : ExecutablePlan Call deftype :=
  (let X : X_T := input0; (let «$s» : (typevar → X_T → (Call heaptype)) := input1; (match input2 with | .DefT «exec:1» «exec:2» => (let rect : rectype := «exec:1»; (let n : SpecTec.n := «exec:2»; (.bind (.call (Call.«$subst_rectype» X_T X «$s» rect)) (fun («exec:3» : rectype) => (let «eval:0» : rectype := «exec:3»; (let rect' : rectype := «eval:0»; (.pure (((@deftype.DefT rect' n) : deftype))))))))))))

def «$subst_deftype_clauses» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : deftype) : List (ExecutablePlan.Clause Call _root_.Unit deftype) :=
  [fun (_ : _root_.Unit) => («$subst_deftype:clause:0» X_T input0 input1 input2)]

def «$rollrt:clause:0» (input0 : typeidx) (input1 : rectype) : ExecutablePlan Call rectype :=
  (let x : idx := input0; (let rect : rectype := input1; (match rect with | .RecT «exec:1» => (let «st*» : (_root_.List subtype) := «exec:1»; (let y : idx := ((_root_.List.length «st*») + x); (.bind (.call (Call.«$subst_rectype» (_root_.Nat × _root_.Nat) (x, y) Call.«$s_roll» rect)) (fun («exec:2» : rectype) => (let «eval:0» : rectype := «exec:2»; (.pure ((«eval:0» : rectype)))))))))))

def «$rollrt_clauses» (input0 : typeidx) (input1 : rectype) : List (ExecutablePlan.Clause Call _root_.Unit rectype) :=
  [fun (_ : _root_.Unit) => («$rollrt:clause:0»  input0 input1)]

def «$unrollrt:clause:0» (input0 : rectype) : ExecutablePlan Call rectype :=
  (let rect : rectype := input0; (.bind (.call (Call.«$subst_rectype» rectype rect Call.«$s_unroll» rect)) (fun («exec:1» : rectype) => (let «eval:0» : rectype := «exec:1»; (.pure ((«eval:0» : rectype)))))))

def «$unrollrt_clauses» (input0 : rectype) : List (ExecutablePlan.Clause Call _root_.Unit rectype) :=
  [fun (_ : _root_.Unit) => («$unrollrt:clause:0»  input0)]

def «$rolldt:clause:0» (input0 : typeidx) (input1 : rectype) : ExecutablePlan Call (_root_.List deftype) :=
  (let x : idx := input0; (let rect : rectype := input1; (.bind (.call (Call.«$rollrt» x rect)) (fun («exec:1» : rectype) => (let «eval:0» : rectype := «exec:1»; (let rect' : rectype := «eval:0»; (.bind (.call (Call.«$rolldt'» (0 : _root_.Nat) rect')) (fun («exec:2» : (_root_.List deftype)) => (let «eval:1» : (_root_.List deftype) := «exec:2»; (.pure ((«eval:1» : (_root_.List deftype)))))))))))))

def «$rolldt_clauses» (input0 : typeidx) (input1 : rectype) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List deftype)) :=
  [fun (_ : _root_.Unit) => («$rolldt:clause:0»  input0 input1)]

def «$unrolldt:clause:0» (input0 : deftype) : ExecutablePlan Call subtype :=
  (let dt : deftype := input0; (match dt with | .DefT «exec:1» «exec:2» => (let rect : rectype := «exec:1»; (let n : SpecTec.n := «exec:2»; (.bind (.call (Call.«$unrollrt» rect)) (fun («exec:3» : rectype) => (let «eval:0» : rectype := «exec:3»; (match «eval:0» with | .RecT «exec:4» => (let «st*» : (_root_.List subtype) := «exec:4»; (.bind (.guard ((n < (_root_.List.length «st*»)))) (fun (_ : Unit) => (match («st*»[n]?) with | some «exec:5» => (let «eval:1» : subtype := «exec:5»; (.pure ((«eval:1» : subtype)))) | none => .unmatch))))))))))))

def «$unrolldt_clauses» (input0 : deftype) : List (ExecutablePlan.Clause Call _root_.Unit subtype) :=
  [fun (_ : _root_.Unit) => («$unrolldt:clause:0»  input0)]

def «$expanddt:clause:0» (input0 : deftype) : ExecutablePlan Call strtype :=
  (let dt : deftype := input0; (.bind (.call (Call.«$unrolldt» dt)) (fun («exec:1» : subtype) => (let «eval:0» : subtype := «exec:1»; (match «eval:0» with | .SubT «exec:2» «exec:3» «exec:4» => (let _fin : final := «exec:2»; (let «_ht*» : (_root_.List heaptype) := «exec:3»; (let strt : strtype := «exec:4»; (.pure ((strt : strtype)))))))))))

def «$expanddt_clauses» (input0 : deftype) : List (ExecutablePlan.Clause Call _root_.Unit strtype) :=
  [fun (_ : _root_.Unit) => («$expanddt:clause:0»  input0)]

def «$free_heaptype:clause:0» (input0 : heaptype) : ExecutablePlan Call free :=
  (let ht : heaptype := input0; (let ht' : heaptype := ht; (.bind (.guard (((«sub:heaptype:heaptypeVar» ht') = true))) (fun (_ : Unit) => (match («$free_heaptype:case_1:downcast:0» ht') with | some «exec:1» => (let «eval:0» : heaptypeVar := «exec:1»; (match «eval:0» with | .VarHT «exec:2» => (let tv : typevar := «exec:2»; (.bind (.call (Call.«$free_typevar» tv)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free))))))))) | none => .unmatch)))))

def «$free_heaptype:clause:1» (input0 : heaptype) : ExecutablePlan Call free :=
  (let ht : heaptype := input0; (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_heaptype_clauses» (input0 : heaptype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_heaptype:clause:0»  input0), fun (_ : _root_.Unit) => («$free_heaptype:clause:1»  input0)]

def «$free_reftype:clause:0» (input0 : reftype) : ExecutablePlan Call free :=
  (match input0 with | .«% %» «exec:1» «exec:2» => (let _null : null := «exec:1»; (let ht : heaptype := «exec:2»; (.bind (.call (Call.«$free_heaptype» ht)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.pure ((«eval:0» : free)))))))))

def «$free_reftype_clauses» (input0 : reftype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_reftype:clause:0»  input0)]

def «$free_valtype:clause:0» (input0 : SpecTec.valtype) : ExecutablePlan Call free :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:NumT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .NumT «exec:1» => (let nt : numtype := «exec:1»; (.bind (.call (Call.«$free_numtype» nt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_valtype:clause:1» (input0 : SpecTec.valtype) : ExecutablePlan Call free :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:VecT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .VecT «exec:1» => (let vt : vectype := «exec:1»; (.bind (.call (Call.«$free_vectype» vt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_valtype:clause:2» (input0 : SpecTec.valtype) : ExecutablePlan Call free :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:RefT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .RefT «exec:1» => (let rt : reftype := «exec:1»; (.bind (.call (Call.«$free_reftype» rt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_valtype:clause:3» (input0 : SpecTec.valtype) : ExecutablePlan Call free :=
  (let valtype : SpecTec.valtype := input0; (.bind (.guard (((«exec:match:valtype:BotT» valtype) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_valtype_clauses» (input0 : valtype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_valtype:clause:0»  input0), fun (_ : _root_.Unit) => («$free_valtype:clause:1»  input0), fun (_ : _root_.Unit) => («$free_valtype:clause:2»  input0), fun (_ : _root_.Unit) => («$free_valtype:clause:3»  input0)]

def «$free_functype:clause:0» (input0 : functype) : ExecutablePlan Call free :=
  (match input0 with | .FuncT «exec:1» «exec:2» => (let «t_1*» : (_root_.List valtype) := «exec:1»; (let «t_2*» : (_root_.List valtype) := «exec:2»; (.bind (.call (Call.«$free_list» valtype Call.«$free_valtype» «t_1*»)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.bind (.call (Call.«$free_list» valtype Call.«$free_valtype» «t_2*»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_union» «eval:0» «eval:1»)) (fun («exec:5» : free) => (let «eval:2» : free := «exec:5»; (.pure ((«eval:2» : free)))))))))))))))

def «$free_functype_clauses» (input0 : functype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_functype:clause:0»  input0)]

def «$free_storagetype:clause:0» (input0 : storagetype) : ExecutablePlan Call free :=
  (let zt : storagetype := input0; (.bind (.guard (((«exec:match:storagetype:ValStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .ValStorageT «exec:1» => (let t : valtype := «exec:1»; (.bind (.call (Call.«$free_valtype» t)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_storagetype:clause:1» (input0 : storagetype) : ExecutablePlan Call free :=
  (let zt : storagetype := input0; (.bind (.guard (((«exec:match:storagetype:PackStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .PackStorageT «exec:1» => (let pt : packtype := «exec:1»; (.bind (.call (Call.«$free_packtype» pt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_storagetype_clauses» (input0 : storagetype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_storagetype:clause:0»  input0), fun (_ : _root_.Unit) => («$free_storagetype:clause:1»  input0)]

def «$free_fieldtype:clause:0» (input0 : fieldtype) : ExecutablePlan Call free :=
  (match input0 with | .FieldT «exec:1» «exec:2» => (let _mut : «mut» := «exec:1»; (let zt : storagetype := «exec:2»; (.bind (.call (Call.«$free_storagetype» zt)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.pure ((«eval:0» : free)))))))))

def «$free_fieldtype_clauses» (input0 : fieldtype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_fieldtype:clause:0»  input0)]

def «$free_structtype:clause:0» (input0 : structtype) : ExecutablePlan Call free :=
  (match input0 with | .StructT «exec:1» => (let «yt*» : (_root_.List fieldtype) := «exec:1»; (.bind (.call (Call.«$free_list» fieldtype Call.«$free_fieldtype» «yt*»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))))

def «$free_structtype_clauses» (input0 : structtype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_structtype:clause:0»  input0)]

def «$free_arraytype:clause:0» (input0 : arraytype) : ExecutablePlan Call free :=
  (match input0 with | .ArrayT «exec:1» => (let yt : fieldtype := «exec:1»; (.bind (.call (Call.«$free_fieldtype» yt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))))

def «$free_arraytype_clauses» (input0 : arraytype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_arraytype:clause:0»  input0)]

def «$free_strtype:clause:0» (input0 : strtype) : ExecutablePlan Call free :=
  (let strt : strtype := input0; (.bind (.guard (((«exec:match:strtype:DefStructT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefStructT «exec:1» => (let strctt : structtype := «exec:1»; (.bind (.call (Call.«$free_structtype» strctt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_strtype:clause:1» (input0 : strtype) : ExecutablePlan Call free :=
  (let strt : strtype := input0; (.bind (.guard (((«exec:match:strtype:DefArrayT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefArrayT «exec:1» => (let arrt : arraytype := «exec:1»; (.bind (.call (Call.«$free_arraytype» arrt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_strtype:clause:2» (input0 : strtype) : ExecutablePlan Call free :=
  (let strt : strtype := input0; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefFuncT «exec:1» => (let ft : functype := «exec:1»; (.bind (.call (Call.«$free_functype» ft)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_strtype_clauses» (input0 : strtype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_strtype:clause:0»  input0), fun (_ : _root_.Unit) => («$free_strtype:clause:1»  input0), fun (_ : _root_.Unit) => («$free_strtype:clause:2»  input0)]

def «$free_subtype:clause:0» (input0 : subtype) : ExecutablePlan Call free :=
  (match input0 with | .SubT «exec:1» «exec:2» «exec:3» => (let fin : final := «exec:1»; (let «ht*» : (_root_.List heaptype) := «exec:2»; (let strt : strtype := «exec:3»; (.bind (.call (Call.«$free_list» heaptype Call.«$free_heaptype» «ht*»)) (fun («exec:4» : free) => (let «eval:0» : free := «exec:4»; (.bind (.call (Call.«$free_strtype» strt)) (fun («exec:5» : free) => (let «eval:1» : free := «exec:5»; (.bind (.call (Call.«$free_union» «eval:0» «eval:1»)) (fun («exec:6» : free) => (let «eval:2» : free := «exec:6»; (.pure ((«eval:2» : free))))))))))))))))

def «$free_subtype_clauses» (input0 : subtype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_subtype:clause:0»  input0)]

def «$free_rectype:clause:0» (input0 : rectype) : ExecutablePlan Call free :=
  (match input0 with | .RecT «exec:1» => (let «st*» : (_root_.List subtype) := «exec:1»; (.bind (.call (Call.«$free_list» subtype Call.«$free_subtype» «st*»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))))

def «$free_rectype_clauses» (input0 : rectype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_rectype:clause:0»  input0)]

def «$free_type_:clause:0» (input0 : SpecTec.type) : ExecutablePlan Call free :=
  (let type : SpecTec.type := input0; (.bind (.call (Call.«$free_rectype» type)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_type__clauses» (input0 : type) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_type_:clause:0»  input0)]

def «$free_globaltype:clause:0» (input0 : globaltype) : ExecutablePlan Call free :=
  (match input0 with | .GlobalT «exec:1» «exec:2» => (let _mut : «mut» := «exec:1»; (let t : valtype := «exec:2»; (.bind (.call (Call.«$free_valtype» t)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.pure ((«eval:0» : free)))))))))

def «$free_globaltype_clauses» (input0 : globaltype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_globaltype:clause:0»  input0)]

def «$free_blocktype:clause:0» (input0 : SpecTec.blocktype) : ExecutablePlan Call free :=
  (let blocktype : SpecTec.blocktype := input0; (.bind (.guard (((«exec:match:blocktype:VarBlockType» blocktype) = true))) (fun (_ : Unit) => (match blocktype with | .VarBlockType «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_blocktype:clause:1» (input0 : SpecTec.blocktype) : ExecutablePlan Call free :=
  (let blocktype : SpecTec.blocktype := input0; (.bind (.guard (((«exec:match:blocktype:ValBlockType» blocktype) = true))) (fun (_ : Unit) => (match blocktype with | .ValBlockType «exec:1» => (let valtype? : (_root_.Option valtype) := «exec:1»; (.bind (.guard (((_root_.Option.isSome valtype?) = true))) (fun (_ : Unit) => (match valtype? with | some «exec:2» => (let t : valtype := «exec:2»; (.bind (.call (Call.«$free_valtype» t)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.pure ((«eval:0» : free))))))) | none => .unmatch)))) | _ => .unmatch))))

def «$free_blocktype:clause:2» (input0 : SpecTec.blocktype) : ExecutablePlan Call free :=
  (let blocktype : SpecTec.blocktype := input0; (.bind (.guard ((@SpecTec.blocktype.ValBlockType ((_root_.Option.none) : (_root_.Option valtype))) = blocktype)) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_blocktype_clauses» (input0 : blocktype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_blocktype:clause:0»  input0), fun (_ : _root_.Unit) => («$free_blocktype:clause:1»  input0), fun (_ : _root_.Unit) => («$free_blocktype:clause:2»  input0)]

def «$free_instr:clause:0» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:UNREACHABLE» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:1» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:NOP» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:2» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:DROP» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:3» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard ((@SpecTec.instr.SELECT ((_root_.Option.none) : (_root_.Option (_root_.List valtype)))) = instr)) (fun (_ : Unit) => (.bind (.call (Call.«$free_list» valtype Call.«$free_valtype» ([] : (_root_.List valtype)))) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:4» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:SELECT» instr) = true))) (fun (_ : Unit) => (match instr with | .SELECT «exec:1» => (let «valtype*?» : (_root_.Option (_root_.List valtype)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome «valtype*?») = true))) (fun (_ : Unit) => (match «valtype*?» with | some «exec:2» => (let «t*» : (_root_.List valtype) := «exec:2»; (.bind (.call (Call.«$free_list» valtype Call.«$free_valtype» «t*»)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.pure ((«eval:0» : free))))))) | none => .unmatch)))) | _ => .unmatch))))

def «$free_instr:clause:5» (input0 : instr) : ExecutablePlan Call free :=
  (let instr' : instr := input0; (.bind (.guard (((«exec:match:instr:BLOCK» instr') = true))) (fun (_ : Unit) => (match instr' with | .BLOCK «exec:1» «exec:2» => (let blocktype : SpecTec.blocktype := «exec:1»; (let «instr*» : (_root_.List instr) := «exec:2»; (.bind (.call (Call.«$free_blocktype» blocktype)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.bind (.call (Call.«$free_block» «instr*»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_union» «eval:0» «eval:1»)) (fun («exec:5» : free) => (let «eval:2» : free := «exec:5»; (.pure ((«eval:2» : free)))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:6» (input0 : instr) : ExecutablePlan Call free :=
  (let instr' : instr := input0; (.bind (.guard (((«exec:match:instr:LOOP» instr') = true))) (fun (_ : Unit) => (match instr' with | .LOOP «exec:1» «exec:2» => (let blocktype : SpecTec.blocktype := «exec:1»; (let «instr*» : (_root_.List instr) := «exec:2»; (.bind (.call (Call.«$free_blocktype» blocktype)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.bind (.call (Call.«$free_block» «instr*»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_union» «eval:0» «eval:1»)) (fun («exec:5» : free) => (let «eval:2» : free := «exec:5»; (.pure ((«eval:2» : free)))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:7» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:IF % % ELSE %» instr) = true))) (fun (_ : Unit) => (match instr with | .«IF % % ELSE %» «exec:1» «exec:2» «exec:3» => (let blocktype : SpecTec.blocktype := «exec:1»; (let «instr_t*» : (_root_.List SpecTec.instr) := «exec:2»; (let «instr_f*» : (_root_.List SpecTec.instr) := «exec:3»; (.bind (.call (Call.«$free_blocktype» blocktype)) (fun («exec:4» : free) => (let «eval:0» : free := «exec:4»; (.bind (.call (Call.«$free_block» «instr_t*»)) (fun («exec:5» : free) => (let «eval:1» : free := «exec:5»; (.bind (.call (Call.«$free_block» «instr_f*»)) (fun («exec:6» : free) => (let «eval:2» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:2»)) (fun («exec:7» : free) => (let «eval:3» : free := «exec:7»; (.bind (.call (Call.«$free_union» «eval:0» «eval:3»)) (fun («exec:8» : free) => (let «eval:4» : free := «exec:8»; (.pure ((«eval:4» : free))))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:8» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:BR» instr) = true))) (fun (_ : Unit) => (match instr with | .BR «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:9» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:BR_IF» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_IF «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:10» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:BR_TABLE» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_TABLE «exec:1» «exec:2» => (let «x*» : (_root_.List idx) := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_list» idx Call.«$update_label» (y :: «x*»))) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.pure ((«eval:0» : free)))))))) | _ => .unmatch))))

def «$free_instr:clause:11» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:BR_ON_NULL» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_ON_NULL «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:12» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:BR_ON_NON_NULL» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_ON_NON_NULL «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:13» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:BR_ON_CAST» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_ON_CAST «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let rt_1 : reftype := «exec:2»; (let rt_2 : reftype := «exec:3»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:4» : (set idx)) => (let «eval:0» : (set idx) := «exec:4»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:5» : free) => (let «eval:1» : free := «exec:5»; (.bind (.call (Call.«$free_reftype» rt_1)) (fun («exec:6» : free) => (let «eval:2» : free := «exec:6»; (.bind (.call (Call.«$free_reftype» rt_2)) (fun («exec:7» : free) => (let «eval:3» : free := «exec:7»; (.bind (.call (Call.«$free_union» «eval:2» «eval:3»)) (fun («exec:8» : free) => (let «eval:4» : free := «exec:8»; (.bind (.call (Call.«$free_union» «eval:1» «eval:4»)) (fun («exec:9» : free) => (let «eval:5» : free := «exec:9»; (.pure ((«eval:5» : free)))))))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:14» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:BR_ON_CAST_FAIL» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_ON_CAST_FAIL «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let rt_1 : reftype := «exec:2»; (let rt_2 : reftype := «exec:3»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:4» : (set idx)) => (let «eval:0» : (set idx) := «exec:4»; (.bind (.call (Call.«$update_labels» «eval:0»)) (fun («exec:5» : free) => (let «eval:1» : free := «exec:5»; (.bind (.call (Call.«$free_reftype» rt_1)) (fun («exec:6» : free) => (let «eval:2» : free := «exec:6»; (.bind (.call (Call.«$free_reftype» rt_2)) (fun («exec:7» : free) => (let «eval:3» : free := «exec:7»; (.bind (.call (Call.«$free_union» «eval:2» «eval:3»)) (fun («exec:8» : free) => (let «eval:4» : free := «exec:8»; (.bind (.call (Call.«$free_union» «eval:1» «eval:4»)) (fun («exec:9» : free) => (let «eval:5» : free := «exec:9»; (.pure ((«eval:5» : free)))))))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:15» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:CALL» instr) = true))) (fun (_ : Unit) => (match instr with | .CALL «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_funcs» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:16» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:CALL_REF» instr) = true))) (fun (_ : Unit) => (match instr with | .CALL_REF «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:17» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:CALL_INDIRECT» instr) = true))) (fun (_ : Unit) => (match instr with | .CALL_INDIRECT «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_types» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:18» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:RETURN» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:19» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:RETURN_CALL» instr) = true))) (fun (_ : Unit) => (match instr with | .RETURN_CALL «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_funcs» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:20» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:RETURN_CALL_REF» instr) = true))) (fun (_ : Unit) => (match instr with | .RETURN_CALL_REF «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:21» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:RETURN_CALL_INDIRECT» instr) = true))) (fun (_ : Unit) => (match instr with | .RETURN_CALL_INDIRECT «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_types» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:22» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:THROW» instr) = true))) (fun (_ : Unit) => (match instr with | .THROW «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tags» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:23» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:THROW_REF» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:24» (input0 : instr) : ExecutablePlan Call free :=
  (let instr' : instr := input0; (.bind (.guard (((«exec:match:instr:TRY_TABLE» instr') = true))) (fun (_ : Unit) => (match instr' with | .TRY_TABLE «exec:1» «exec:2» «exec:3» => (let blocktype : SpecTec.blocktype := «exec:1»; (let «catch*» : (_root_.List «catch») := «exec:2»; (let «instr*» : (_root_.List instr) := «exec:3»; (.bind (.call (Call.«$free_blocktype» blocktype)) (fun («exec:4» : free) => (let «eval:0» : free := «exec:4»; (.bind (.call (Call.«$free_list» «catch» Call.«$free_catch» «catch*»)) (fun («exec:5» : free) => (let «eval:1» : free := «exec:5»; (.bind (.call (Call.«$free_block» «instr*»)) (fun («exec:6» : free) => (let «eval:2» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:2»)) (fun («exec:7» : free) => (let «eval:3» : free := «exec:7»; (.bind (.call (Call.«$free_union» «eval:0» «eval:3»)) (fun («exec:8» : free) => (let «eval:4» : free := «exec:8»; (.pure ((«eval:4» : free))))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:25» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:LOCAL.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«LOCAL.GET» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_locals» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:26» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:LOCAL.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«LOCAL.SET» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_locals» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:27» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:LOCAL.TEE» instr) = true))) (fun (_ : Unit) => (match instr with | .«LOCAL.TEE» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_locals» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:28» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:GLOBAL.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«GLOBAL.GET» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_globals» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:29» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:GLOBAL.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«GLOBAL.SET» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_globals» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:30» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:TABLE.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.GET» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:31» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:TABLE.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.SET» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:32» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:TABLE.SIZE» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.SIZE» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:33» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:TABLE.GROW» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.GROW» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:34» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:TABLE.FILL» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.FILL» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:35» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:TABLE.COPY» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.COPY» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_tables» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:36» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:TABLE.INIT» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.INIT» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_tables» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_elems» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:37» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ELEM.DROP» instr) = true))) (fun (_ : Unit) => (match instr with | .«ELEM.DROP» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_elems» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:38» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:LOAD» instr) = true))) (fun (_ : Unit) => (match instr with | .LOAD «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _lop : loadop_ := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:39» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:STORE» instr) = true))) (fun (_ : Unit) => (match instr with | .STORE «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _sop : storeop_ := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:40» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:VEC.LOAD» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.LOAD» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _vlop : vloadop_ := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:41» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:VEC.STORE» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.STORE» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _vsop : vstoreop_ := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:42» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:VEC.LOAD_LANE» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.LOAD_LANE» «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let _vlaneop : vlaneop_ := «exec:2»; (let _int : _root_.Int := «exec:3»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:4» : (set idx)) => (let «eval:0» : (set idx) := «exec:4»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:5» : free) => (let «eval:1» : free := «exec:5»; (.pure ((«eval:1» : free)))))))))))) | _ => .unmatch))))

def «$free_instr:clause:43» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:VEC.STORE_LANE» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.STORE_LANE» «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let _vlaneop : vlaneop_ := «exec:2»; (let _int : _root_.Int := «exec:3»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:4» : (set idx)) => (let «eval:0» : (set idx) := «exec:4»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:5» : free) => (let «eval:1» : free := «exec:5»; (.pure ((«eval:1» : free)))))))))))) | _ => .unmatch))))

def «$free_instr:clause:44» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:MEMORY.SIZE» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.SIZE» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:45» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:MEMORY.GROW» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.GROW» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:46» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:MEMORY.FILL» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.FILL» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:47» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:MEMORY.COPY» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.COPY» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_mems» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:48» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:MEMORY.INIT» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.INIT» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_mems» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_datas» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:49» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:DATA.DROP» instr) = true))) (fun (_ : Unit) => (match instr with | .«DATA.DROP» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_datas» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:50» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:REF.NULL» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.NULL» «exec:1» => (let ht : heaptype := «exec:1»; (.bind (.call (Call.«$free_heaptype» ht)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:51» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:REF.FUNC» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.FUNC» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_funcs» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:52» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:REF.IS_NULL» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:53» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:REF.AS_NON_NULL» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:54» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:REF.TEST» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.TEST» «exec:1» => (let rt : reftype := «exec:1»; (.bind (.call (Call.«$free_reftype» rt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:55» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:REF.CAST» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.CAST» «exec:1» => (let rt : reftype := «exec:1»; (.bind (.call (Call.«$free_reftype» rt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:56» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:REF.EQ» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:57» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:REF.I31» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:58» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:I31.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«I31.GET» «exec:1» => (let _extension : extension := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:59» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:STRUCT.NEW» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.NEW» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _iop : initop_ := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:60» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:STRUCT.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.GET» «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let _ti : typeidx := «exec:2»; (let _extension? : (_root_.Option extension) := «exec:3»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:4» : (set idx)) => (let «eval:0» : (set idx) := «exec:4»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:5» : free) => (let «eval:1» : free := «exec:5»; (.pure ((«eval:1» : free)))))))))))) | _ => .unmatch))))

def «$free_instr:clause:61» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:STRUCT.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.SET» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _ti : typeidx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:62» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.NEW» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _iop : initop_ := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:63» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.NEW_FIXED» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW_FIXED» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _u32 : u32 := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:64» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.NEW_ELEM» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW_ELEM» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_elems» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:65» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.NEW_DATA» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW_DATA» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_datas» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:66» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.GET» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let _extension? : (_root_.Option extension) := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.pure ((«eval:1» : free))))))))))) | _ => .unmatch))))

def «$free_instr:clause:67» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.SET» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:68» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.LEN» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_instr:clause:69» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.COPY» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.COPY» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_types» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:70» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.FILL» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.FILL» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_instr:clause:71» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.INIT_DATA» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.INIT_DATA» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_datas» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:72» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:ARRAY.INIT_ELEM» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.INIT_ELEM» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:3» : (set idx)) => (let «eval:0» : (set idx) := «exec:3»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$free_idx» y)) (fun («exec:5» : (set idx)) => (let «eval:2» : (set idx) := «exec:5»; (.bind (.call (Call.«$update_elems» «eval:2»)) (fun («exec:6» : free) => (let «eval:3» : free := «exec:6»; (.bind (.call (Call.«$free_union» «eval:1» «eval:3»)) (fun («exec:7» : free) => (let «eval:4» : free := «exec:7»; (.pure ((«eval:4» : free)))))))))))))))))))) | _ => .unmatch))))

def «$free_instr:clause:73» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:EXTERN.CONVERT» instr) = true))) (fun (_ : Unit) => (match instr with | .«EXTERN.CONVERT» «exec:1» => (let _eop : externop_ := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:74» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:CONST» instr) = true))) (fun (_ : Unit) => (match instr with | .CONST «exec:1» => (let _num : num_ := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:75» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:TEST» instr) = true))) (fun (_ : Unit) => (match instr with | .TEST «exec:1» => (let _top : testop_ := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:76» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:COMPARE» instr) = true))) (fun (_ : Unit) => (match instr with | .COMPARE «exec:1» => (let _rop : relop_ := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:77» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:UNARY» instr) = true))) (fun (_ : Unit) => (match instr with | .UNARY «exec:1» => (let _uop : unop_ := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:78» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:BINOP» instr) = true))) (fun (_ : Unit) => (match instr with | .BINOP «exec:1» => (let _bop : binop_ := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:79» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.guard (((«exec:match:instr:CONVERT» instr) = true))) (fun (_ : Unit) => (match instr with | .CONVERT «exec:1» => (let _cop : cvtop_ := «exec:1»; (.bind (.call (Call.«$free_empty»)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_instr:clause:80» (input0 : SpecTec.instr) : ExecutablePlan Call free :=
  (let instr : SpecTec.instr := input0; (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_instr_clauses» (input0 : instr) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_instr:clause:0»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:1»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:2»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:3»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:4»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:5»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:6»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:7»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:8»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:9»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:10»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:11»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:12»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:13»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:14»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:15»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:16»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:17»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:18»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:19»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:20»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:21»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:22»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:23»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:24»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:25»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:26»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:27»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:28»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:29»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:30»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:31»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:32»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:33»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:34»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:35»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:36»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:37»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:38»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:39»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:40»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:41»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:42»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:43»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:44»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:45»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:46»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:47»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:48»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:49»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:50»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:51»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:52»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:53»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:54»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:55»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:56»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:57»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:58»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:59»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:60»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:61»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:62»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:63»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:64»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:65»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:66»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:67»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:68»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:69»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:70»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:71»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:72»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:73»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:74»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:75»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:76»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:77»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:78»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:79»  input0), fun (_ : _root_.Unit) => («$free_instr:clause:80»  input0)]

def «$free_block:clause:0» (input0 : (_root_.List instr)) : ExecutablePlan Call free :=
  (let «instr*» : (_root_.List instr) := input0; (.bind (.call (Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» «instr*»)) (fun («exec:1» : SpecTec.free) => (let «eval:0» : SpecTec.free := «exec:1»; (let free : SpecTec.free := «eval:0»; (.bind (.call (Call.«$free_shift» (SpecTec.free.LABELS free))) (fun («exec:2» : (set idx)) => (let «eval:1» : (set idx) := «exec:2»; (let free' : SpecTec.free := ({ free with LABELS := «eval:1» } : SpecTec.free); (.pure ((free' : SpecTec.free))))))))))))

def «$free_block_clauses» (input0 : (_root_.List instr)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_block:clause:0»  input0)]

def «$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0» (input0 : (_root_.List instr)) : ExecutablePlan Call free :=
  (let «X*» : (_root_.List instr) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))))

def «$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1» (input0 : (_root_.List instr)) : ExecutablePlan Call free :=
  (let «X*» : (_root_.List instr) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «X*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «X*» with | «exec:2» :: «exec:1» => (let X_h : instr := «exec:2»; (let «X_t*» : (_root_.List instr) := «exec:1»; (.bind (.call (Call.«$free_instr» X_h)) (fun («exec:3» : free) => (let «eval:0» : free := «exec:3»; (.bind (.call (Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» «X_t*»)) (fun («exec:4» : free) => (let «eval:1» : free := «exec:4»; (.bind (.call (Call.«$fold_left» free free Call.«$free_union» «eval:0» ([«eval:1»] : (_root_.List free)))) (fun («exec:5» : free) => (let «eval:2» : free := «exec:5»; (.pure ((«eval:2» : free)))))))))))))) | [] => .unmatch))))

def «$free_list:specialized:627ab0672e3a767978c05fd35fc5a959_clauses» (input0 : (_root_.List instr)) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0»  input0), fun (_ : _root_.Unit) => («$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1»  input0)]

def «$free_const:clause:0» (input0 : const) : ExecutablePlan Call free :=
  (let «instr*» : (_root_.List instr) := input0; (.bind (.call (Call.«$free_block» «instr*»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_const_clauses» (input0 : const) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_const:clause:0»  input0)]

def «$free_global:clause:0» (input0 : SpecTec.global) : ExecutablePlan Call free :=
  (let global : SpecTec.global := input0; (.bind (.call (Call.«$free_globaltype» (SpecTec.global.GTYPE global))) (fun («exec:1» : SpecTec.free) => (let «eval:0» : SpecTec.free := «exec:1»; (let free_1 : SpecTec.free := «eval:0»; (.bind (.call (Call.«$free_const» (SpecTec.global.GINIT global))) (fun («exec:2» : SpecTec.free) => (let «eval:1» : SpecTec.free := «exec:2»; (let free_2 : SpecTec.free := «eval:1»; (.bind (.call (Call.«$free_union» free_1 free_2)) (fun («exec:3» : SpecTec.free) => (let «eval:2» : SpecTec.free := «exec:3»; (let free : SpecTec.free := «eval:2»; (.pure ((free : SpecTec.free))))))))))))))))

def «$free_global_clauses» (input0 : global) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_global:clause:0»  input0)]

def «$free_tabletype:clause:0» (input0 : tabletype) : ExecutablePlan Call free :=
  (match input0 with | .TableT «exec:1» «exec:2» «exec:3» => (let _at : addrtype := «exec:1»; (let _lim : limits := «exec:2»; (let rt : reftype := «exec:3»; (.bind (.call (Call.«$free_reftype» rt)) (fun («exec:4» : free) => (let «eval:0» : free := «exec:4»; (.pure ((«eval:0» : free))))))))))

def «$free_tabletype_clauses» (input0 : tabletype) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_tabletype:clause:0»  input0)]

def «$free_table:clause:0» (input0 : SpecTec.table) : ExecutablePlan Call free :=
  (let table : SpecTec.table := input0; (.bind (.call (Call.«$free_tabletype» (SpecTec.table.TTYPE table))) (fun («exec:1» : SpecTec.free) => (let «eval:0» : SpecTec.free := «exec:1»; (let free_1 : SpecTec.free := «eval:0»; (.bind (.call (Call.«$free_const» (SpecTec.table.TINIT table))) (fun («exec:2» : SpecTec.free) => (let «eval:1» : SpecTec.free := «exec:2»; (let free_2 : SpecTec.free := «eval:1»; (.bind (.call (Call.«$free_union» free_1 free_2)) (fun («exec:3» : SpecTec.free) => (let «eval:2» : SpecTec.free := «exec:3»; (let free : SpecTec.free := «eval:2»; (.pure ((free : SpecTec.free))))))))))))))))

def «$free_table_clauses» (input0 : table) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_table:clause:0»  input0)]

def «$free_elemmode:clause:0» (input0 : ((set tableidx) → (Call free))) (input1 : SpecTec.elemmode) : ExecutablePlan Call free :=
  (let «$f» : ((set tableidx) → (Call free)) := input0; (let elemmode : SpecTec.elemmode := input1; (.bind (.guard (((elemmode = (@SpecTec.elemmode.Passive)) ∨ (elemmode = (@SpecTec.elemmode.Declarative))))) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free))))))))))

def «$free_elemmode:clause:1» (input0 : ((set tableidx) → (Call free))) (input1 : SpecTec.elemmode) : ExecutablePlan Call free :=
  (let «$f» : ((set tableidx) → (Call free)) := input0; (let elemmode : SpecTec.elemmode := input1; (let elemmode' : SpecTec.elemmode := elemmode; (.bind (.guard (((«exec:match:elemmode:Active» elemmode') = true))) (fun (_ : Unit) => (match elemmode' with | .Active «exec:1» => (let idx : SpecTec.idx := («exec:1»).INDEX; (let «instr*» : (_root_.List instr) := («exec:1»).OFFSET; (.bind (.call («$f» (@set.«`{ % `}» tableidx ([idx] : (_root_.List SpecTec.idx))))) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (let free_1 : free := «eval:0»; (.bind (.call (Call.«$free_const» «instr*»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (let free_2 : free := «eval:1»; (.bind (.call (Call.«$free_union» free_1 free_2)) (fun («exec:4» : free) => (let «eval:2» : free := «exec:4»; (.pure ((«eval:2» : free)))))))))))))))) | _ => .unmatch))))))

def «$free_elemmode_clauses» (input0 : ((set tableidx) → (Call free))) (input1 : elemmode) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_elemmode:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$free_elemmode:clause:1»  input0 input1)]

def «$free_elem:clause:0» (input0 : SpecTec.elem) : ExecutablePlan Call free :=
  (let elem : SpecTec.elem := input0; (.bind (.call (Call.«$free_list» const Call.«$free_const» (SpecTec.elem.EINIT elem))) (fun («exec:1» : SpecTec.free) => (let «eval:0» : SpecTec.free := «exec:1»; (let free_1 : SpecTec.free := «eval:0»; (.bind (.call (Call.«$free_elemmode» Call.«$update_tables» (SpecTec.elem.EMODE elem))) (fun («exec:2» : SpecTec.free) => (let «eval:1» : SpecTec.free := «exec:2»; (let free_2 : SpecTec.free := «eval:1»; (.bind (.call (Call.«$free_union» free_1 free_2)) (fun («exec:3» : SpecTec.free) => (let «eval:2» : SpecTec.free := «exec:3»; (let free : SpecTec.free := «eval:2»; (.pure ((free : SpecTec.free))))))))))))))))

def «$free_elem_clauses» (input0 : elem) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_elem:clause:0»  input0)]

def «$free_datamode:clause:0» (input0 : ((set memidx) → (Call free))) (input1 : SpecTec.datamode) : ExecutablePlan Call free :=
  (let «$f» : ((set memidx) → (Call free)) := input0; (let datamode : SpecTec.datamode := input1; (.bind (.guard ((@SpecTec.datamode.Passive) = datamode)) (fun (_ : Unit) => (.bind (.call (Call.«$free_empty»)) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free))))))))))

def «$free_datamode:clause:1» (input0 : ((set memidx) → (Call free))) (input1 : SpecTec.datamode) : ExecutablePlan Call free :=
  (let «$f» : ((set memidx) → (Call free)) := input0; (let datamode : SpecTec.datamode := input1; (let datamode' : SpecTec.datamode := datamode; (.bind (.guard (((«exec:match:datamode:Active» datamode') = true))) (fun (_ : Unit) => (match datamode' with | .Active «exec:1» => (let idx : SpecTec.idx := («exec:1»).INDEX; (let «instr*» : (_root_.List instr) := («exec:1»).OFFSET; (.bind (.call («$f» (@set.«`{ % `}» memidx ([idx] : (_root_.List SpecTec.idx))))) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (let free_1 : free := «eval:0»; (.bind (.call (Call.«$free_const» «instr*»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (let free_2 : free := «eval:1»; (.bind (.call (Call.«$free_union» free_1 free_2)) (fun («exec:4» : free) => (let «eval:2» : free := «exec:4»; (.pure ((«eval:2» : free)))))))))))))))) | _ => .unmatch))))))

def «$free_datamode_clauses» (input0 : ((set memidx) → (Call free))) (input1 : datamode) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_datamode:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$free_datamode:clause:1»  input0 input1)]

def «$free_data:clause:0» (input0 : SpecTec.data) : ExecutablePlan Call free :=
  (let data : SpecTec.data := input0; (.bind (.call (Call.«$free_datamode» Call.«$update_mems» (SpecTec.data.DMODE data))) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_data_clauses» (input0 : data) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_data:clause:0»  input0)]

def «$free_importdesc:clause:0» (input0 : SpecTec.importdesc) : ExecutablePlan Call free :=
  (let importdesc : SpecTec.importdesc := input0; (.bind (.guard (((«exec:match:importdesc:FuncImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .FuncImport «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_types» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_importdesc:clause:1» (input0 : SpecTec.importdesc) : ExecutablePlan Call free :=
  (let importdesc : SpecTec.importdesc := input0; (.bind (.guard (((«exec:match:importdesc:TableImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .TableImport «exec:1» => (let tt : tabletype := «exec:1»; (.bind (.call (Call.«$free_tabletype» tt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_importdesc:clause:2» (input0 : SpecTec.importdesc) : ExecutablePlan Call free :=
  (let importdesc : SpecTec.importdesc := input0; (.bind (.guard (((«exec:match:importdesc:MemImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .MemImport «exec:1» => (let mt : memtype := «exec:1»; (.bind (.call (Call.«$free_memtype» mt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_importdesc:clause:3» (input0 : SpecTec.importdesc) : ExecutablePlan Call free :=
  (let importdesc : SpecTec.importdesc := input0; (.bind (.guard (((«exec:match:importdesc:GlobalImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .GlobalImport «exec:1» => (let gt : globaltype := «exec:1»; (.bind (.call (Call.«$free_globaltype» gt)) (fun («exec:2» : free) => (let «eval:0» : free := «exec:2»; (.pure ((«eval:0» : free))))))) | _ => .unmatch))))

def «$free_importdesc:clause:4» (input0 : SpecTec.importdesc) : ExecutablePlan Call free :=
  (let importdesc : SpecTec.importdesc := input0; (.bind (.guard (((«exec:match:importdesc:TagImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .TagImport «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$free_idx» x)) (fun («exec:2» : (set idx)) => (let «eval:0» : (set idx) := «exec:2»; (.bind (.call (Call.«$update_tags» «eval:0»)) (fun («exec:3» : free) => (let «eval:1» : free := «exec:3»; (.pure ((«eval:1» : free)))))))))) | _ => .unmatch))))

def «$free_importdesc_clauses» (input0 : importdesc) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_importdesc:clause:0»  input0), fun (_ : _root_.Unit) => («$free_importdesc:clause:1»  input0), fun (_ : _root_.Unit) => («$free_importdesc:clause:2»  input0), fun (_ : _root_.Unit) => («$free_importdesc:clause:3»  input0), fun (_ : _root_.Unit) => («$free_importdesc:clause:4»  input0)]

def «$free_import:clause:0» (input0 : SpecTec.«import») : ExecutablePlan Call free :=
  (let «import» : SpecTec.«import» := input0; (.bind (.call (Call.«$free_importdesc» (SpecTec.«import».IDESC «import»))) (fun («exec:1» : free) => (let «eval:0» : free := «exec:1»; (.pure ((«eval:0» : free)))))))

def «$free_import_clauses» (input0 : «import») : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_import:clause:0»  input0)]

def «$free_module:clause:0» (input0 : SpecTec.module) : ExecutablePlan Call free :=
  (let module : SpecTec.module := input0; (.bind (.call (Call.«$free_list» type Call.«$free_type_» (SpecTec.module.TYPES module))) (fun («exec:1» : SpecTec.free) => (let «eval:0» : SpecTec.free := «exec:1»; (let free_1 : SpecTec.free := «eval:0»; (.bind (.call (Call.«$free_list» global Call.«$free_global» (SpecTec.module.GLOBALS module))) (fun («exec:2» : SpecTec.free) => (let «eval:1» : SpecTec.free := «exec:2»; (let free_2 : SpecTec.free := «eval:1»; (.bind (.call (Call.«$free_list» table Call.«$free_table» (SpecTec.module.TABLES module))) (fun («exec:3» : SpecTec.free) => (let «eval:2» : SpecTec.free := «exec:3»; (let free_3 : SpecTec.free := «eval:2»; (.bind (.call (Call.«$free_list» memory Call.«$free_mem» (SpecTec.module.MEMS module))) (fun («exec:4» : SpecTec.free) => (let «eval:3» : SpecTec.free := «exec:4»; (let free_4 : SpecTec.free := «eval:3»; (.bind (.call (Call.«$free_opt» start Call.«$free_start» (SpecTec.module.START module))) (fun («exec:5» : SpecTec.free) => (let «eval:4» : SpecTec.free := «exec:5»; (let free_5 : SpecTec.free := «eval:4»; (.bind (.call (Call.«$free_list» elem Call.«$free_elem» (SpecTec.module.ELEMS module))) (fun («exec:6» : SpecTec.free) => (let «eval:5» : SpecTec.free := «exec:6»; (let free_6 : SpecTec.free := «eval:5»; (.bind (.call (Call.«$free_list» data Call.«$free_data» (SpecTec.module.DATAS module))) (fun («exec:7» : SpecTec.free) => (let «eval:6» : SpecTec.free := «exec:7»; (let free_7 : SpecTec.free := «eval:6»; (.bind (.call (Call.«$free_list» «import» Call.«$free_import» (SpecTec.module.IMPORTS module))) (fun («exec:8» : SpecTec.free) => (let «eval:7» : SpecTec.free := «exec:8»; (let free_8 : SpecTec.free := «eval:7»; (.bind (.call (Call.«$free_list» «export» Call.«$free_export» (SpecTec.module.EXPORTS module))) (fun («exec:9» : SpecTec.free) => (let «eval:8» : SpecTec.free := «exec:9»; (let free_9 : SpecTec.free := «eval:8»; (.bind (.call (Call.«$free_unions» ([free_1, free_2, free_3, free_4, free_5, free_6, free_7, free_8, free_9] : (_root_.List SpecTec.free)))) (fun («exec:10» : SpecTec.free) => (let «eval:9» : SpecTec.free := «exec:10»; (let free : SpecTec.free := «eval:9»; (.pure ((free : SpecTec.free))))))))))))))))))))))))))))))))))))))))))))

def «$free_module_clauses» (input0 : module) : List (ExecutablePlan.Clause Call _root_.Unit free) :=
  [fun (_ : _root_.Unit) => («$free_module:clause:0»  input0)]

def «$match_deftype:clause:0» (input0 : (_root_.List deftype)) (input1 : deftype) (input2 : deftype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let dt_1 : deftype := input1; (let dt_2 : deftype := input2; (.bind (.guard (dt_2 = dt_1)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))

def «$match_deftype:clause:1» (input0 : (_root_.List deftype)) (input1 : deftype) (input2 : deftype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let dt_1 : deftype := input1; (let dt_2 : deftype := input2; (.bind (.guard ((dt_1 ≠ dt_2))) (fun (_ : Unit) => (.bind (.call (Call.«$subst_deftype» (_root_.List deftype) «dt*» Call.«$subst_of» dt_1)) (fun («exec:1» : deftype) => (let «eval:0» : deftype := «exec:1»; (.bind (.call (Call.«$subst_deftype» (_root_.List deftype) «dt*» Call.«$subst_of» dt_2)) (fun («exec:2» : deftype) => (let «eval:1» : deftype := «exec:2»; (.bind (.guard («eval:1» = «eval:0»)) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))))))))

def «$match_deftype:clause:2» (input0 : (_root_.List deftype)) (input1 : deftype) (input2 : deftype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let dt_1 : deftype := input1; (let dt_2 : deftype := input2; (.bind (.guard ((dt_1 ≠ dt_2))) (fun (_ : Unit) => (.bind (.call (Call.«$subst_deftype» (_root_.List deftype) «dt*» Call.«$subst_of» dt_1)) (fun («exec:1» : deftype) => (let «eval:0» : deftype := «exec:1»; (.bind (.call (Call.«$subst_deftype» (_root_.List deftype) «dt*» Call.«$subst_of» dt_2)) (fun («exec:2» : deftype) => (let «eval:1» : deftype := «exec:2»; (.bind (.guard ((«eval:0» ≠ «eval:1»))) (fun (_ : Unit) => (.bind (.call (Call.«$unrolldt» dt_1)) (fun («exec:3» : subtype) => (let «eval:2» : subtype := «exec:3»; (match «eval:2» with | .SubT «exec:4» «exec:5» «exec:6» => (let fin : final := «exec:4»; (let «ht*» : (_root_.List heaptype) := «exec:5»; (let strt : strtype := «exec:6»; (.bind (.call (Call.«$match_heaptype_exists» «dt*» «ht*» dt_2)) (fun («exec:7» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:7»; (.pure ((«eval:3» : _root_.Bool))))))))))))))))))))))))))

def «$match_deftype_clauses» (input0 : (_root_.List deftype)) (input1 : deftype) (input2 : deftype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_deftype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_deftype:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_deftype:clause:2»  input0 input1 input2)]

def «$match_heaptype:clause:0» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (let ht' : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:AnyHT» ht') = true))) (fun (_ : Unit) => (.bind (.guard (((((ht = (@heaptype.EqHT)) ∨ (ht = (@heaptype.StructHT))) ∨ (ht = (@heaptype.ArrayHT))) ∨ (ht = (@heaptype.I31HT))))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))

def «$match_heaptype:clause:1» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (let ht' : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:EqHT» ht') = true))) (fun (_ : Unit) => (.bind (.guard ((((ht = (@heaptype.I31HT)) ∨ (ht = (@heaptype.StructHT))) ∨ (ht = (@heaptype.ArrayHT))))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))

def «$match_heaptype:clause:2» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht' : heaptype := input1; (let ht : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:NoneHT» ht') = true))) (fun (_ : Unit) => (.bind (.call (Call.«$match_heaptype» «dt*» ht (@heaptype.AnyHT))) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool)))))))))))

def «$match_heaptype:clause:3» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht' : heaptype := input1; (let ht : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:NoFuncHT» ht') = true))) (fun (_ : Unit) => (.bind (.call (Call.«$match_heaptype» «dt*» ht (@heaptype.FuncHT))) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool)))))))))))

def «$match_heaptype:clause:4» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht' : heaptype := input1; (let ht : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:NoExnHT» ht') = true))) (fun (_ : Unit) => (.bind (.call (Call.«$match_heaptype» «dt*» ht (@heaptype.ExnHT))) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool)))))))))))

def «$match_heaptype:clause:5» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht' : heaptype := input1; (let ht : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:NoExternHT» ht') = true))) (fun (_ : Unit) => (.bind (.call (Call.«$match_heaptype» «dt*» ht (@heaptype.ExternHT))) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool)))))))))))

def «$match_heaptype:clause:6» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht' : heaptype := input1; (let ht : heaptype := input2; (.bind (.guard (((«sub:heaptype:heaptypeVar» ht') = true))) (fun (_ : Unit) => (match («$match_heaptype:case_7:downcast:0» ht') with | some «exec:1» => (let «eval:0» : heaptypeVar := «exec:1»; (match «eval:0» with | .VarHT «exec:2» => (let tv : typevar := «exec:2»; (.bind (.guard (((«exec:match:typevar:StatX» tv) = true))) (fun (_ : Unit) => (match tv with | .StatX «exec:3» => (let x : idx := «exec:3»; (.bind (.guard ((x < (_root_.List.length «dt*»)))) (fun (_ : Unit) => (match («dt*»[x]?) with | some «exec:4» => (let «eval:1» : deftype := «exec:4»; (.bind (.call (Call.«$match_heaptype» «dt*» (@heaptype.DefHT «eval:1») ht)) (fun («exec:5» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:5»; (.pure ((«eval:2» : _root_.Bool))))))) | none => .unmatch)))) | _ => .unmatch)))))) | none => .unmatch))))))

def «$match_heaptype:clause:7» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (let ht' : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:DefHT» ht) = true))) (fun (_ : Unit) => (match ht with | .DefHT «exec:1» => (let dt_1 : deftype := «exec:1»; (.bind (.guard (((«sub:heaptype:heaptypeVar» ht') = true))) (fun (_ : Unit) => (match («$match_heaptype:case_8:downcast:0» ht') with | some «exec:2» => (let «eval:0» : heaptypeVar := «exec:2»; (match «eval:0» with | .VarHT «exec:3» => (let tv : typevar := «exec:3»; (.bind (.guard (((«exec:match:typevar:StatX» tv) = true))) (fun (_ : Unit) => (match tv with | .StatX «exec:4» => (let x : idx := «exec:4»; (.bind (.guard ((x < (_root_.List.length «dt*»)))) (fun (_ : Unit) => (match («dt*»[x]?) with | some «exec:5» => (let «eval:1» : deftype := «exec:5»; (.bind (.call (Call.«$match_heaptype» «dt*» (@heaptype.DefHT dt_1) (@heaptype.DefHT «eval:1»))) (fun («exec:6» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:6»; (.pure ((«eval:2» : _root_.Bool))))))) | none => .unmatch)))) | _ => .unmatch)))))) | none => .unmatch)))) | _ => .unmatch))))))

def «$match_heaptype:clause:8» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (let ht' : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:DefHT» ht) = true))) (fun (_ : Unit) => (match ht with | .DefHT «exec:1» => (let dt_1 : deftype := «exec:1»; (.bind (.guard (((«exec:match:heaptype:DefHT» ht') = true))) (fun (_ : Unit) => (match ht' with | .DefHT «exec:2» => (let dt_2 : deftype := «exec:2»; (.bind (.call (Call.«$match_deftype» «dt*» dt_1 dt_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_heaptype:clause:9» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht' : heaptype := input1; (let ht : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:DefHT» ht') = true))) (fun (_ : Unit) => (match ht' with | .DefHT «exec:1» => (let dt_1 : deftype := «exec:1»; (.bind (.call (Call.«$expanddt» dt_1)) (fun («exec:2» : strtype) => (let «eval:0» : strtype := «exec:2»; (let strt : strtype := «eval:0»; (.bind (.guard (((«exec:match:strtype:DefStructT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefStructT «exec:3» => (let _strctt : structtype := «exec:3»; (.bind (.guard ((((ht = (@heaptype.AnyHT)) ∨ (ht = (@heaptype.EqHT))) ∨ (ht = (@heaptype.StructHT))))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)))))))) | _ => .unmatch))))))

def «$match_heaptype:clause:10» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht' : heaptype := input1; (let ht : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:DefHT» ht') = true))) (fun (_ : Unit) => (match ht' with | .DefHT «exec:1» => (let dt_1 : deftype := «exec:1»; (.bind (.call (Call.«$expanddt» dt_1)) (fun («exec:2» : strtype) => (let «eval:0» : strtype := «exec:2»; (let strt : strtype := «eval:0»; (.bind (.guard (((«exec:match:strtype:DefArrayT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefArrayT «exec:3» => (let _arrt : arraytype := «exec:3»; (.bind (.guard ((((ht = (@heaptype.AnyHT)) ∨ (ht = (@heaptype.EqHT))) ∨ (ht = (@heaptype.ArrayHT))))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)))))))) | _ => .unmatch))))))

def «$match_heaptype:clause:11» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (let ht' : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:DefHT» ht) = true))) (fun (_ : Unit) => (match ht with | .DefHT «exec:1» => (let dt_1 : deftype := «exec:1»; (.bind (.guard (((«exec:match:heaptype:FuncHT» ht') = true))) (fun (_ : Unit) => (.bind (.call (Call.«$expanddt» dt_1)) (fun («exec:2» : strtype) => (let «eval:0» : strtype := «exec:2»; (let strt : strtype := «eval:0»; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefFuncT «exec:3» => (let _ft : functype := «exec:3»; (.pure ((true : _root_.Bool)))) | _ => .unmatch)))))))))) | _ => .unmatch))))))

def «$match_heaptype:clause:12» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (let _ht : heaptype := input2; (.bind (.guard (((«exec:match:heaptype:BotHT» ht) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))

def «$match_heaptype:clause:13» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht_1 : heaptype := input1; (let ht_2 : heaptype := input2; (.pure (((_root_.Decidable.decide (ht_1 = ht_2)) : _root_.Bool))))))

def «$match_heaptype_clauses» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_heaptype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:4»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:5»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:6»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:7»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:8»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:9»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:10»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:11»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:12»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype:clause:13»  input0 input1 input2)]

def «$match_heaptype_exists:clause:0» (input0 : (_root_.List deftype)) (input1 : (_root_.List heaptype)) (input2 : deftype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let «ht*» : (_root_.List heaptype) := input1; (let dt_1 : deftype := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ht*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))))

def «$match_heaptype_exists:clause:1» (input0 : (_root_.List deftype)) (input1 : (_root_.List heaptype)) (input2 : deftype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let «ht*» : (_root_.List heaptype) := input1; (let dt_1 : deftype := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ht*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ht*» with | «exec:2» :: «exec:1» => (let ht_h : heaptype := «exec:2»; (let «ht_t*» : (_root_.List heaptype) := «exec:1»; (.bind (.call (Call.«$match_heaptype» «dt*» ht_h (@heaptype.DefHT dt_1))) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))) | [] => .unmatch))))))

def «$match_heaptype_exists:clause:2» (input0 : (_root_.List deftype)) (input1 : (_root_.List heaptype)) (input2 : deftype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let «ht*» : (_root_.List heaptype) := input1; (let dt_1 : deftype := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ht*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ht*» with | «exec:2» :: «exec:1» => (let ht_h : heaptype := «exec:2»; (let «ht_t*» : (_root_.List heaptype) := «exec:1»; (.bind (.call (Call.«$match_heaptype» «dt*» ht_h (@heaptype.DefHT dt_1))) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.bind (.guard ((¬ («eval:0» = true)))) (fun (_ : Unit) => (.bind (.call (Call.«$match_heaptype_exists» «dt*» «ht_t*» dt_1)) (fun («exec:4» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:4»; (.pure ((«eval:1» : _root_.Bool))))))))))))) | [] => .unmatch))))))

def «$match_heaptype_exists_clauses» (input0 : (_root_.List deftype)) (input1 : (_root_.List heaptype)) (input2 : deftype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_heaptype_exists:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype_exists:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_heaptype_exists:clause:2»  input0 input1 input2)]

def «$match_reftype:clause:0» (input0 : (_root_.List deftype)) (input1 : reftype) (input2 : reftype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | .«% %» «exec:1» «exec:2» => (let null_1 : null := «exec:1»; (let ht_1 : heaptype := «exec:2»; (match input2 with | .«% %» «exec:3» «exec:4» => (let null_2 : null := «exec:3»; (let ht_2 : heaptype := «exec:4»; (.bind (.call (Call.«$match_null» null_1 null_2)) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.call (Call.«$match_heaptype» «dt*» ht_1 ht_2)) (fun («exec:6» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:6»; (.bind (.guard (((«eval:0» = true) ∧ («eval:1» = true)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))))))))))

def «$match_reftype:clause:1» (input0 : (_root_.List deftype)) (input1 : reftype) (input2 : reftype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let _rt : reftype := input1; (let _rt' : reftype := input2; (.pure ((false : _root_.Bool))))))

def «$match_reftype_clauses» (input0 : (_root_.List deftype)) (input1 : reftype) (input2 : reftype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_reftype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_reftype:clause:1»  input0 input1 input2)]

def «$match_valtype:clause:0» (input0 : (_root_.List deftype)) (input1 : SpecTec.valtype) (input2 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let valtype : SpecTec.valtype := input1; (let valtype' : SpecTec.valtype := input2; (.bind (.guard (((«exec:match:valtype:NumT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .NumT «exec:1» => (let nt_1 : numtype := «exec:1»; (.bind (.guard (((«exec:match:valtype:NumT» valtype') = true))) (fun (_ : Unit) => (match valtype' with | .NumT «exec:2» => (let nt_2 : numtype := «exec:2»; (.bind (.call (Call.«$match_numtype» «dt*» nt_1 nt_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_valtype:clause:1» (input0 : (_root_.List deftype)) (input1 : SpecTec.valtype) (input2 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let valtype : SpecTec.valtype := input1; (let valtype' : SpecTec.valtype := input2; (.bind (.guard (((«exec:match:valtype:VecT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .VecT «exec:1» => (let vt_1 : vectype := «exec:1»; (.bind (.guard (((«exec:match:valtype:VecT» valtype') = true))) (fun (_ : Unit) => (match valtype' with | .VecT «exec:2» => (let vt_2 : vectype := «exec:2»; (.bind (.call (Call.«$match_vectype» «dt*» vt_1 vt_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_valtype:clause:2» (input0 : (_root_.List deftype)) (input1 : SpecTec.valtype) (input2 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let valtype : SpecTec.valtype := input1; (let valtype' : SpecTec.valtype := input2; (.bind (.guard (((«exec:match:valtype:RefT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .RefT «exec:1» => (let rt_1 : reftype := «exec:1»; (.bind (.guard (((«exec:match:valtype:RefT» valtype') = true))) (fun (_ : Unit) => (match valtype' with | .RefT «exec:2» => (let rt_2 : reftype := «exec:2»; (.bind (.call (Call.«$match_reftype» «dt*» rt_1 rt_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_valtype:clause:3» (input0 : (_root_.List deftype)) (input1 : SpecTec.valtype) (input2 : SpecTec.valtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let valtype : SpecTec.valtype := input1; (let _t : SpecTec.valtype := input2; (.bind (.guard (((«exec:match:valtype:BotT» valtype) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))

def «$match_valtype:clause:4» (input0 : (_root_.List deftype)) (input1 : valtype) (input2 : valtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let t_1 : valtype := input1; (let t_2 : valtype := input2; (.pure ((false : _root_.Bool))))))

def «$match_valtype_clauses» (input0 : (_root_.List deftype)) (input1 : valtype) (input2 : valtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_valtype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_valtype:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_valtype:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_valtype:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_valtype:clause:4»  input0 input1 input2)]

def «$match_storagetype:clause:0» (input0 : (_root_.List deftype)) (input1 : storagetype) (input2 : storagetype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let zt : storagetype := input1; (let zt' : storagetype := input2; (.bind (.guard (((«exec:match:storagetype:ValStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .ValStorageT «exec:1» => (let t_1 : valtype := «exec:1»; (.bind (.guard (((«exec:match:storagetype:ValStorageT» zt') = true))) (fun (_ : Unit) => (match zt' with | .ValStorageT «exec:2» => (let t_2 : valtype := «exec:2»; (.bind (.call (Call.«$match_valtype» «dt*» t_1 t_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_storagetype:clause:1» (input0 : (_root_.List deftype)) (input1 : storagetype) (input2 : storagetype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let zt : storagetype := input1; (let zt' : storagetype := input2; (.bind (.guard (((«exec:match:storagetype:PackStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .PackStorageT «exec:1» => (let pt_1 : packtype := «exec:1»; (.bind (.guard (((«exec:match:storagetype:PackStorageT» zt') = true))) (fun (_ : Unit) => (match zt' with | .PackStorageT «exec:2» => (let pt_2 : packtype := «exec:2»; (.bind (.call (Call.«$match_packtype» «dt*» pt_1 pt_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_storagetype:clause:2» (input0 : (_root_.List deftype)) (input1 : storagetype) (input2 : storagetype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let _zt : storagetype := input1; (let _zt' : storagetype := input2; (.pure ((false : _root_.Bool))))))

def «$match_storagetype_clauses» (input0 : (_root_.List deftype)) (input1 : storagetype) (input2 : storagetype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_storagetype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_storagetype:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_storagetype:clause:2»  input0 input1 input2)]

def «$match_fieldtype:clause:0» (input0 : (_root_.List deftype)) (input1 : fieldtype) (input2 : fieldtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | .FieldT «exec:1» «exec:2» => (let mut_1 : «mut» := «exec:1»; (let zt_1 : storagetype := «exec:2»; (match input2 with | .FieldT «exec:3» «exec:4» => (let mut_2 : «mut» := «exec:3»; (let zt_2 : storagetype := «exec:4»; (.bind (.call (Call.«$match_storagetype» «dt*» zt_1 zt_2)) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.guard ((((mut_1 = mut_2) ∧ («eval:0» = true)) ∧ (mut_1 = (@«mut».Cons))))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))))))))

def «$match_fieldtype:clause:1» (input0 : (_root_.List deftype)) (input1 : fieldtype) (input2 : fieldtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | .FieldT «exec:1» «exec:2» => (let mut_1 : «mut» := «exec:1»; (let zt_1 : storagetype := «exec:2»; (match input2 with | .FieldT «exec:3» «exec:4» => (let mut_2 : «mut» := «exec:3»; (let zt_2 : storagetype := «exec:4»; (.bind (.call (Call.«$match_storagetype» «dt*» zt_1 zt_2)) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.call (Call.«$match_storagetype» «dt*» zt_2 zt_1)) (fun («exec:6» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:6»; (.bind (.guard (((((mut_1 = mut_2) ∧ («eval:0» = true)) ∧ (mut_1 = (@«mut».Var))) ∧ («eval:1» = true)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))))))))))

def «$match_fieldtype:clause:2» (input0 : (_root_.List deftype)) (input1 : fieldtype) (input2 : fieldtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let _yt : fieldtype := input1; (let _yt' : fieldtype := input2; (.pure ((false : _root_.Bool))))))

def «$match_fieldtype_clauses» (input0 : (_root_.List deftype)) (input1 : fieldtype) (input2 : fieldtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_fieldtype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_fieldtype:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_fieldtype:clause:2»  input0 input1 input2)]

def «$match_arraytype:clause:0» (input0 : (_root_.List deftype)) (input1 : arraytype) (input2 : arraytype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | .ArrayT «exec:1» => (let yt_1 : fieldtype := «exec:1»; (match input2 with | .ArrayT «exec:2» => (let yt_2 : fieldtype := «exec:2»; (.bind (.call (Call.«$match_fieldtype» «dt*» yt_1 yt_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))))

def «$match_arraytype_clauses» (input0 : (_root_.List deftype)) (input1 : arraytype) (input2 : arraytype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_arraytype:clause:0»  input0 input1 input2)]

def «$match_structtype:case_1:iter:0:clause:0» (input0 : (_root_.List deftype)) (input1 : (_root_.List fieldtype)) (input2 : (_root_.List fieldtype)) : ExecutablePlan Call _root_.Unit :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | [] => (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch))

def «$match_structtype:case_1:iter:0:clause:1» (input0 : (_root_.List deftype)) (input1 : (_root_.List fieldtype)) (input2 : (_root_.List fieldtype)) : ExecutablePlan Call _root_.Unit :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | «exec:2» :: «exec:1» => (let yt_1' : fieldtype := «exec:2»; (let «tail:0» : (_root_.List fieldtype) := «exec:1»; (match input2 with | «exec:4» :: «exec:3» => (let yt_2 : fieldtype := «exec:4»; (let «tail:1» : (_root_.List fieldtype) := «exec:3»; (.bind (.call (Call.«$match_fieldtype» «dt*» yt_1' yt_2)) (fun («exec:5» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:5»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$match_structtype:case_1:iter:0» «dt*» «tail:0» «tail:1»)) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch))) | [] => .unmatch))

def «$match_structtype:case_1:iter:0_clauses» (input0 : (_root_.List deftype)) (input1 : (_root_.List fieldtype)) (input2 : (_root_.List fieldtype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_structtype:case_1:iter:0:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_structtype:case_1:iter:0:clause:1»  input0 input1 input2)]

def «$match_structtype:clause:0» (input0 : (_root_.List deftype)) (input1 : structtype) (input2 : structtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | .StructT «exec:1» => (let «yt_1*» : (_root_.List fieldtype) := «exec:1»; (match input2 with | .StructT «exec:2» => (let «yt_2*» : (_root_.List fieldtype) := «exec:2»; (.bind (.guard (((_root_.List.length «yt_1*») ≥ (_root_.List.length «yt_2*»)))) (fun (_ : Unit) => (.bind (ExecutablePlan.require ((((0 : _root_.Nat) + (_root_.List.length «yt_2*»)) ≤ (_root_.List.length «yt_1*»))) "slice out of bounds") (fun (_ : Unit) => (let «yt_1'*» : (_root_.List fieldtype) := (_root_.List.take (_root_.List.length «yt_2*») (_root_.List.drop (0 : _root_.Nat) «yt_1*»)); (.bind (.guard ((_root_.List.length «yt_2*») = (_root_.List.length «yt_1'*»))) (fun (_ : Unit) => (.bind (.call (Call.«$match_structtype:case_1:iter:0» «dt*» «yt_1'*» «yt_2*»)) (fun («exec:3» : _root_.Unit) => (.pure ((true : _root_.Bool)))))))))))))))))

def «$match_structtype:clause:1» (input0 : (_root_.List deftype)) (input1 : structtype) (input2 : structtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let _strctt : structtype := input1; (let _strctt' : structtype := input2; (.pure ((false : _root_.Bool))))))

def «$match_structtype_clauses» (input0 : (_root_.List deftype)) (input1 : structtype) (input2 : structtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_structtype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_structtype:clause:1»  input0 input1 input2)]

def «$match_resulttype:case_1:iter:0:clause:0» (input0 : (_root_.List deftype)) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) : ExecutablePlan Call _root_.Unit :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | [] => (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch))

def «$match_resulttype:case_1:iter:0:clause:1» (input0 : (_root_.List deftype)) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) : ExecutablePlan Call _root_.Unit :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | «exec:2» :: «exec:1» => (let t_1 : valtype := «exec:2»; (let «tail:0» : (_root_.List valtype) := «exec:1»; (match input2 with | «exec:4» :: «exec:3» => (let t_2 : valtype := «exec:4»; (let «tail:1» : (_root_.List valtype) := «exec:3»; (.bind (.call (Call.«$match_valtype» «dt*» t_1 t_2)) (fun («exec:5» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:5»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$match_resulttype:case_1:iter:0» «dt*» «tail:0» «tail:1»)) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch))) | [] => .unmatch))

def «$match_resulttype:case_1:iter:0_clauses» (input0 : (_root_.List deftype)) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_resulttype:case_1:iter:0:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_resulttype:case_1:iter:0:clause:1»  input0 input1 input2)]

def «$match_resulttype:clause:0» (input0 : (_root_.List deftype)) (input1 : resulttype) (input2 : resulttype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let «t_1*» : (_root_.List valtype) := input1; (let «t_2*» : (_root_.List valtype) := input2; (.bind (.guard ((_root_.List.length «t_2*») = (_root_.List.length «t_1*»))) (fun (_ : Unit) => (.bind (.call (Call.«$match_resulttype:case_1:iter:0» «dt*» «t_1*» «t_2*»)) (fun («exec:1» : _root_.Unit) => (.pure ((true : _root_.Bool))))))))))

def «$match_resulttype:clause:1» (input0 : (_root_.List deftype)) (input1 : resulttype) (input2 : resulttype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let _rest : resulttype := input1; (let _rest' : resulttype := input2; (.pure ((false : _root_.Bool))))))

def «$match_resulttype_clauses» (input0 : (_root_.List deftype)) (input1 : resulttype) (input2 : resulttype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_resulttype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_resulttype:clause:1»  input0 input1 input2)]

def «$match_functype:clause:0» (input0 : (_root_.List deftype)) (input1 : functype) (input2 : functype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (match input1 with | .FuncT «exec:1» «exec:2» => (let «t_1*» : (_root_.List valtype) := «exec:1»; (let «t_2*» : (_root_.List valtype) := «exec:2»; (match input2 with | .FuncT «exec:3» «exec:4» => (let «t_1'*» : (_root_.List valtype) := «exec:3»; (let «t_2'*» : (_root_.List valtype) := «exec:4»; (.bind (.call (Call.«$match_resulttype» «dt*» «t_1'*» «t_1*»)) (fun («exec:5» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:5»; (.bind (.call (Call.«$match_resulttype» «dt*» «t_2*» «t_2'*»)) (fun («exec:6» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:6»; (.pure (((«eval:0» && «eval:1») : _root_.Bool))))))))))))))))

def «$match_functype_clauses» (input0 : (_root_.List deftype)) (input1 : functype) (input2 : functype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_functype:clause:0»  input0 input1 input2)]

def «$match_strtype:clause:0» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let strt : strtype := input1; (let strt' : strtype := input2; (.bind (.guard (((«exec:match:strtype:DefStructT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefStructT «exec:1» => (let strctt_1 : structtype := «exec:1»; (.bind (.guard (((«exec:match:strtype:DefStructT» strt') = true))) (fun (_ : Unit) => (match strt' with | .DefStructT «exec:2» => (let strctt_2 : structtype := «exec:2»; (.bind (.call (Call.«$match_structtype» «dt*» strctt_1 strctt_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_strtype:clause:1» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let strt : strtype := input1; (let strt' : strtype := input2; (.bind (.guard (((«exec:match:strtype:DefArrayT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefArrayT «exec:1» => (let arrt_1 : arraytype := «exec:1»; (.bind (.guard (((«exec:match:strtype:DefArrayT» strt') = true))) (fun (_ : Unit) => (match strt' with | .DefArrayT «exec:2» => (let arrt_2 : arraytype := «exec:2»; (.bind (.call (Call.«$match_arraytype» «dt*» arrt_1 arrt_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_strtype:clause:2» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let strt : strtype := input1; (let strt' : strtype := input2; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefFuncT «exec:1» => (let ft_1 : functype := «exec:1»; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt') = true))) (fun (_ : Unit) => (match strt' with | .DefFuncT «exec:2» => (let ft_2 : functype := «exec:2»; (.bind (.call (Call.«$match_functype» «dt*» ft_1 ft_2)) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))) | _ => .unmatch)))) | _ => .unmatch))))))

def «$match_strtype:clause:3» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) : ExecutablePlan Call _root_.Bool :=
  (let «dt*» : (_root_.List deftype) := input0; (let strt_1 : strtype := input1; (let strt_2 : strtype := input2; (.pure ((false : _root_.Bool))))))

def «$match_strtype_clauses» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Bool) :=
  [fun (_ : _root_.Unit) => («$match_strtype:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_strtype:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_strtype:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$match_strtype:clause:3»  input0 input1 input2)]

def «$top_of_str_type:clause:0» (input0 : (_root_.List deftype)) (input1 : strtype) : ExecutablePlan Call heaptype :=
  (let «dt*» : (_root_.List deftype) := input0; (let strt : strtype := input1; (.bind (.call (Call.«$abs_of_str_type» strt)) (fun («exec:1» : heaptype) => (let «eval:0» : heaptype := «exec:1»; (.bind (.call (Call.«$top_of_heap_type» «dt*» «eval:0»)) (fun («exec:2» : heaptype) => (let «eval:1» : heaptype := «exec:2»; (.pure ((«eval:1» : heaptype)))))))))))

def «$top_of_str_type_clauses» (input0 : (_root_.List deftype)) (input1 : strtype) : List (ExecutablePlan.Clause Call _root_.Unit heaptype) :=
  [fun (_ : _root_.Unit) => («$top_of_str_type:clause:0»  input0 input1)]

def «$top_of_heap_type:clause:0» (input0 : (_root_.List deftype)) (input1 : heaptype) : ExecutablePlan Call heaptype :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (.bind (.guard ((ht ∈ ([(@heaptype.AnyHT), (@heaptype.NoneHT), (@heaptype.EqHT), (@heaptype.StructHT), (@heaptype.ArrayHT), (@heaptype.I31HT)] : (_root_.List heaptype))))) (fun (_ : Unit) => (.pure (((@heaptype.AnyHT) : heaptype)))))))

def «$top_of_heap_type:clause:1» (input0 : (_root_.List deftype)) (input1 : heaptype) : ExecutablePlan Call heaptype :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (.bind (.guard ((ht ∈ ([(@heaptype.FuncHT), (@heaptype.NoFuncHT)] : (_root_.List heaptype))))) (fun (_ : Unit) => (.pure (((@heaptype.FuncHT) : heaptype)))))))

def «$top_of_heap_type:clause:2» (input0 : (_root_.List deftype)) (input1 : heaptype) : ExecutablePlan Call heaptype :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (.bind (.guard ((ht ∈ ([(@heaptype.ExnHT), (@heaptype.NoExnHT)] : (_root_.List heaptype))))) (fun (_ : Unit) => (.pure (((@heaptype.ExnHT) : heaptype)))))))

def «$top_of_heap_type:clause:3» (input0 : (_root_.List deftype)) (input1 : heaptype) : ExecutablePlan Call heaptype :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (.bind (.guard ((ht ∈ ([(@heaptype.ExternHT), (@heaptype.NoExternHT)] : (_root_.List heaptype))))) (fun (_ : Unit) => (.pure (((@heaptype.ExternHT) : heaptype)))))))

def «$top_of_heap_type:clause:4» (input0 : (_root_.List deftype)) (input1 : heaptype) : ExecutablePlan Call heaptype :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (.bind (.guard (((«exec:match:heaptype:DefHT» ht) = true))) (fun (_ : Unit) => (match ht with | .DefHT «exec:1» => (let dt' : deftype := «exec:1»; (.bind (.call (Call.«$expanddt» dt')) (fun («exec:2» : strtype) => (let «eval:0» : strtype := «exec:2»; (.bind (.call (Call.«$top_of_str_type» «dt*» «eval:0»)) (fun («exec:3» : heaptype) => (let «eval:1» : heaptype := «exec:3»; (.pure ((«eval:1» : heaptype)))))))))) | _ => .unmatch)))))

def «$top_of_heap_type:clause:5» (input0 : (_root_.List deftype)) (input1 : heaptype) : ExecutablePlan Call heaptype :=
  (let «dt*» : (_root_.List deftype) := input0; (let ht : heaptype := input1; (.bind (.guard (((«sub:heaptype:heaptypeVar» ht) = true))) (fun (_ : Unit) => (match («$top_of_heap_type:case_6:downcast:0» ht) with | some «exec:1» => (let «eval:0» : heaptypeVar := «exec:1»; (match «eval:0» with | .VarHT «exec:2» => (let tv : typevar := «exec:2»; (.bind (.guard (((«exec:match:typevar:StatX» tv) = true))) (fun (_ : Unit) => (match tv with | .StatX «exec:3» => (let x : idx := «exec:3»; (.bind (.guard ((x < (_root_.List.length «dt*»)))) (fun (_ : Unit) => (match («dt*»[x]?) with | some «exec:4» => (let «eval:1» : deftype := «exec:4»; (.bind (.call (Call.«$expanddt» «eval:1»)) (fun («exec:5» : strtype) => (let «eval:2» : strtype := «exec:5»; (.bind (.call (Call.«$top_of_str_type» «dt*» «eval:2»)) (fun («exec:6» : heaptype) => (let «eval:3» : heaptype := «exec:6»; (.pure ((«eval:3» : heaptype)))))))))) | none => .unmatch)))) | _ => .unmatch)))))) | none => .unmatch)))))

def «$top_of_heap_type_clauses» (input0 : (_root_.List deftype)) (input1 : heaptype) : List (ExecutablePlan.Clause Call _root_.Unit heaptype) :=
  [fun (_ : _root_.Unit) => («$top_of_heap_type:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$top_of_heap_type:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$top_of_heap_type:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$top_of_heap_type:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$top_of_heap_type:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$top_of_heap_type:clause:5»  input0 input1)]

def «Match_resulttype:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) : ExecutablePlan Call _root_.Unit :=
  (let C : context := input0; (match input1 with | [] => (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch))

def «Match_resulttype:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) : ExecutablePlan Call _root_.Unit :=
  (let C : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let t_1 : valtype := «exec:2»; (let «tail:0» : (_root_.List valtype) := «exec:1»; (match input2 with | «exec:4» :: «exec:3» => (let t_2 : valtype := «exec:4»; (let «tail:1» : (_root_.List valtype) := «exec:3»; (.bind (.call (Call.«$match_valtype» (context.TYPES C) t_1 t_2)) (fun («exec:5» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:5»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call (Call.«Match_resulttype:rule:iter:0» C «tail:0» «tail:1»)) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch))) | [] => .unmatch))

def «Match_resulttype:rule:iter:0_clauses» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Match_resulttype:rule:iter:0:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Match_resulttype:rule:iter:0:clause:1»  input0 input1 input2)]

def «Match_resulttype:clause:0» (input0 : context) (input1 : resulttype) (input2 : resulttype) : ExecutablePlan Call _root_.Unit :=
  (let C : context := input0; (let «t_1*» : (_root_.List valtype) := input1; (let «t_2*» : (_root_.List valtype) := input2; (.bind (.guard ((_root_.List.length «t_2*») = (_root_.List.length «t_1*»))) (fun (_ : Unit) => (.bind (.call (Call.«Match_resulttype:rule:iter:0» C «t_1*» «t_2*»)) (fun («exec:1» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))

def Match_resulttype_clauses (input0 : context) (input1 : resulttype) (input2 : resulttype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Match_resulttype:clause:0»  input0 input1 input2)]

def «$pop:clause:0» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) : ExecutablePlan Call (ellipses × resulttype) :=
  (let C : context := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t_1*» : (_root_.List valtype) := (input1).2; (let ellipses' : SpecTec.ellipses := (input2).1; (let «t_2*» : (_root_.List valtype) := (input2).2; (.bind (.guard (((«exec:match:ellipses:Ellipses» ellipses) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ellipses:Ellipses» ellipses') = true))) (fun (_ : Unit) => (let n_1 : SpecTec.n := (_root_.List.length «t_1*»); (let n_2 : SpecTec.n := (_root_.List.length «t_2*»); (.bind (.call (Call.«$min_» n_1 n_2)) (fun («exec:1» : _root_.Nat) => (let «eval:0» : _root_.Nat := «exec:1»; (let n : SpecTec.n := «eval:0»; (let int : _root_.Int := ((_root_.Int.ofNat n_1) - (_root_.Int.ofNat n)); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:2» => (let «eval:1» : SpecTec.n := «exec:2»; (let n_3 : SpecTec.n := «eval:1»; (let int' : _root_.Int := ((_root_.Int.ofNat n_2) - (_root_.Int.ofNat n)); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int')) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int') with | some «exec:3» => (let «eval:2» : SpecTec.n := «exec:3»; (let n_4 : SpecTec.n := «eval:2»; (.bind (ExecutablePlan.require (((n_4 + n) ≤ (_root_.List.length «t_2*»))) "slice out of bounds") (fun (_ : Unit) => (let «t_2'*» : (_root_.List valtype) := (_root_.List.take n (_root_.List.drop n_4 «t_2*»)); (.bind (.call (Call.«$make_» valtype (@valtype.BotT) n_3)) (fun («exec:4» : (_root_.List valtype)) => (let «eval:3» : (_root_.List valtype) := «exec:4»; (.bind (.call (Call.Match_resulttype C («eval:3» ++ «t_2'*») «t_1*»)) (fun («exec:5» : _root_.Unit) => (.pure ((((@SpecTec.ellipses.Ellipses), ([] : (_root_.List valtype))) : (SpecTec.ellipses × resulttype)))))))))))))) | none => .unmatch)))))) | none => .unmatch)))))))))))))))))))

def «$pop:clause:1» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) : ExecutablePlan Call (ellipses × resulttype) :=
  (let C : context := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t_1*» : (_root_.List valtype) := (input1).2; (let ellipses' : SpecTec.ellipses := (input2).1; (let «t_2*» : (_root_.List valtype) := (input2).2; (.bind (.guard (((«exec:match:ellipses:NoEllipses» ellipses) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ellipses:Ellipses» ellipses') = true))) (fun (_ : Unit) => (let n_1 : SpecTec.n := (_root_.List.length «t_1*»); (let n_2 : SpecTec.n := (_root_.List.length «t_2*»); (.bind (.call (Call.«$min_» n_1 n_2)) (fun («exec:1» : _root_.Nat) => (let «eval:0» : _root_.Nat := «exec:1»; (let n : SpecTec.n := «eval:0»; (let int : _root_.Int := ((_root_.Int.ofNat n_1) - (_root_.Int.ofNat n)); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:2» => (let «eval:1» : SpecTec.n := «exec:2»; (let n_3 : SpecTec.n := «eval:1»; (let int' : _root_.Int := ((_root_.Int.ofNat n_2) - (_root_.Int.ofNat n)); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int')) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int') with | some «exec:3» => (let «eval:2» : SpecTec.n := «exec:3»; (let n_4 : SpecTec.n := «eval:2»; (.bind (ExecutablePlan.require (((n_4 + n) ≤ (_root_.List.length «t_2*»))) "slice out of bounds") (fun (_ : Unit) => (let «t_2'*» : (_root_.List valtype) := (_root_.List.take n (_root_.List.drop n_4 «t_2*»)); (.bind (.call (Call.«$make_» valtype (@valtype.BotT) n_3)) (fun («exec:4» : (_root_.List valtype)) => (let «eval:3» : (_root_.List valtype) := «exec:4»; (.bind (.call (Call.Match_resulttype C («eval:3» ++ «t_2'*») «t_1*»)) (fun («exec:5» : _root_.Unit) => (.bind (ExecutablePlan.require ((((0 : _root_.Nat) + n_4) ≤ (_root_.List.length «t_2*»))) "slice out of bounds") (fun (_ : Unit) => (.pure ((((@SpecTec.ellipses.Ellipses), (_root_.List.take n_4 (_root_.List.drop (0 : _root_.Nat) «t_2*»))) : (SpecTec.ellipses × resulttype)))))))))))))))) | none => .unmatch)))))) | none => .unmatch)))))))))))))))))))

def «$pop:clause:2» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) : ExecutablePlan Call (ellipses × resulttype) :=
  (let C : context := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t_1*» : (_root_.List valtype) := (input1).2; (let ellipses' : SpecTec.ellipses := (input2).1; (let «t_2*» : (_root_.List valtype) := (input2).2; (.bind (.guard (((«exec:match:ellipses:Ellipses» ellipses) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ellipses:NoEllipses» ellipses') = true))) (fun (_ : Unit) => (let n_1 : SpecTec.n := (_root_.List.length «t_1*»); (let n_2 : SpecTec.n := (_root_.List.length «t_2*»); (.bind (.call (Call.«$min_» n_1 n_2)) (fun («exec:1» : _root_.Nat) => (let «eval:0» : _root_.Nat := «exec:1»; (let n : SpecTec.n := «eval:0»; (let int : _root_.Int := ((_root_.Int.ofNat n_2) - (_root_.Int.ofNat n)); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:2» => (let «eval:1» : SpecTec.n := «exec:2»; (let n_3 : SpecTec.n := «eval:1»; (.bind (ExecutablePlan.require (((n_3 + n) ≤ (_root_.List.length «t_2*»))) "slice out of bounds") (fun (_ : Unit) => (let «t_2'*» : (_root_.List valtype) := (_root_.List.take n (_root_.List.drop n_3 «t_2*»)); (.bind (.call (Call.Match_resulttype C «t_2'*» «t_1*»)) (fun («exec:3» : _root_.Unit) => (.pure ((((@SpecTec.ellipses.NoEllipses), ([] : (_root_.List valtype))) : (SpecTec.ellipses × resulttype))))))))))) | none => .unmatch)))))))))))))))))))

def «$pop:clause:3» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) : ExecutablePlan Call (ellipses × resulttype) :=
  (let C : context := input0; (let ellipses : SpecTec.ellipses := (input1).1; (let «t_1*» : (_root_.List valtype) := (input1).2; (let ellipses' : SpecTec.ellipses := (input2).1; (let «t_2*» : (_root_.List valtype) := (input2).2; (.bind (.guard (((«exec:match:ellipses:NoEllipses» ellipses) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ellipses:NoEllipses» ellipses') = true))) (fun (_ : Unit) => (let n_1 : SpecTec.n := (_root_.List.length «t_1*»); (let n_2 : SpecTec.n := (_root_.List.length «t_2*»); (.bind (.call (Call.«$min_» n_1 n_2)) (fun («exec:1» : _root_.Nat) => (let «eval:0» : _root_.Nat := «exec:1»; (let n : SpecTec.n := «eval:0»; (let int : _root_.Int := ((_root_.Int.ofNat n_2) - (_root_.Int.ofNat n)); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:2» => (let «eval:1» : SpecTec.n := «exec:2»; (let n_3 : SpecTec.n := «eval:1»; (.bind (ExecutablePlan.require (((n_3 + n) ≤ (_root_.List.length «t_2*»))) "slice out of bounds") (fun (_ : Unit) => (let «t_2'*» : (_root_.List valtype) := (_root_.List.take n (_root_.List.drop n_3 «t_2*»)); (.bind (.call (Call.Match_resulttype C «t_2'*» «t_1*»)) (fun («exec:3» : _root_.Unit) => (.bind (ExecutablePlan.require ((((0 : _root_.Nat) + n_3) ≤ (_root_.List.length «t_2*»))) "slice out of bounds") (fun (_ : Unit) => (.pure ((((@SpecTec.ellipses.NoEllipses), (_root_.List.take n_3 (_root_.List.drop (0 : _root_.Nat) «t_2*»))) : (SpecTec.ellipses × resulttype))))))))))))) | none => .unmatch)))))))))))))))))))

def «$pop_clauses» (input0 : context) (input1 : (ellipses × resulttype)) (input2 : (ellipses × resulttype)) : List (ExecutablePlan.Clause Call _root_.Unit (ellipses × resulttype)) :=
  [fun (_ : _root_.Unit) => («$pop:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$pop:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$pop:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$pop:clause:3»  input0 input1 input2)]

def «Heaptype_ok:clause:0» (input0 : context) (input1 : heaptype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let ht : heaptype := input1; (.bind (.guard ((ht ∈ ([(@heaptype.AnyHT), (@heaptype.NoneHT), (@heaptype.EqHT), (@heaptype.I31HT), (@heaptype.StructHT), (@heaptype.ArrayHT), (@heaptype.FuncHT), (@heaptype.NoFuncHT), (@heaptype.ExnHT), (@heaptype.NoExnHT), (@heaptype.ExternHT), (@heaptype.NoExternHT), (@heaptype.BotHT)] : (_root_.List heaptype))))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))

def «Heaptype_ok:clause:1» (input0 : context) (input1 : heaptype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let ht : heaptype := input1; (.bind (.guard (((«sub:heaptype:heaptypeVar» ht) = true))) (fun (_ : Unit) => (match («Heaptype_ok:typeuse:downcast:0» ht) with | some «exec:1» => (let «eval:0» : heaptypeVar := «exec:1»; (match «eval:0» with | .VarHT «exec:2» => (let tv : typevar := «exec:2»; (.bind (.guard (((«exec:match:typevar:StatX» tv) = true))) (fun (_ : Unit) => (match tv with | .StatX «exec:3» => (let x : idx := «exec:3»; (.bind (.guard (((x ≥ (0 : _root_.Nat)) ∧ (x < (_root_.List.length (context.TYPES C_0)))))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))) | none => .unmatch)))))

def Heaptype_ok_clauses (input0 : context) (input1 : heaptype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Heaptype_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Heaptype_ok:clause:1»  input0 input1)]

def «Reftype_ok:clause:0» (input0 : context) (input1 : reftype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .«% %» «exec:1» «exec:2» => (let null : SpecTec.null := «exec:1»; (let ht : heaptype := «exec:2»; (.bind (.call (Call.Heaptype_ok C_0 ht)) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))

def Reftype_ok_clauses (input0 : context) (input1 : reftype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Reftype_ok:clause:0»  input0 input1)]

def «Valtype_ok:clause:0» (input0 : context) (input1 : SpecTec.valtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let valtype : SpecTec.valtype := input1; (.bind (.guard (((«exec:match:valtype:NumT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .NumT «exec:1» => (let nt : numtype := «exec:1»; (.bind (.call (Call.Numtype_ok C_0 nt)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))

def «Valtype_ok:clause:1» (input0 : context) (input1 : SpecTec.valtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let valtype : SpecTec.valtype := input1; (.bind (.guard (((«exec:match:valtype:VecT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .VecT «exec:1» => (let vt : vectype := «exec:1»; (.bind (.call (Call.Vectype_ok C_0 vt)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))

def «Valtype_ok:clause:2» (input0 : context) (input1 : SpecTec.valtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let valtype : SpecTec.valtype := input1; (.bind (.guard (((«exec:match:valtype:RefT» valtype) = true))) (fun (_ : Unit) => (match valtype with | .RefT «exec:1» => (match «exec:1» with | .«% %» «exec:2» «exec:3» => (let null : SpecTec.null := «exec:2»; (let ht : heaptype := «exec:3»; (.bind (.call (Call.Reftype_ok C_0 (@reftype.«% %» null ht))) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))) | _ => .unmatch)))))

def Valtype_ok_clauses (input0 : context) (input1 : valtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Valtype_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Valtype_ok:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Valtype_ok:clause:2»  input0 input1)]

def «Resulttype_ok:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List valtype)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))

def «Resulttype_ok:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List valtype)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let t : valtype := «exec:2»; (let «tail:0» : (_root_.List valtype) := «exec:1»; (.bind (.call (Call.Valtype_ok C_0 t)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«Resulttype_ok:rule:iter:0» C_0 «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))

def «Resulttype_ok:rule:iter:0_clauses» (input0 : context) (input1 : (_root_.List valtype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Resulttype_ok:rule:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Resulttype_ok:rule:iter:0:clause:1»  input0 input1)]

def «Resulttype_ok:clause:0» (input0 : context) (input1 : resulttype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t*» : (_root_.List valtype) := input1; (.bind (.call (Call.«Resulttype_ok:rule:iter:0» C_0 «t*»)) (fun («exec:1» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))

def Resulttype_ok_clauses (input0 : context) (input1 : resulttype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Resulttype_ok:clause:0»  input0 input1)]

def «Functype_ok:clause:0» (input0 : context) (input1 : functype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .FuncT «exec:1» «exec:2» => (let «t_1*» : (_root_.List valtype) := «exec:1»; (let «t_2*» : (_root_.List valtype) := «exec:2»; (.bind (.call (Call.Resulttype_ok C_0 «t_1*»)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.Resulttype_ok C_0 «t_2*»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))

def Functype_ok_clauses (input0 : context) (input1 : functype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Functype_ok:clause:0»  input0 input1)]

def «Subtype_ok:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List heaptype)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))

def «Subtype_ok:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List heaptype)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let ht : heaptype := «exec:2»; (let «tail:0» : (_root_.List heaptype) := «exec:1»; (.bind (.call (Call.Heaptype_ok C_0 ht)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«Subtype_ok:rule:iter:0» C_0 «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))

def «Subtype_ok:rule:iter:0_clauses» (input0 : context) (input1 : (_root_.List heaptype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Subtype_ok:rule:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Subtype_ok:rule:iter:0:clause:1»  input0 input1)]

def «Storagetype_ok:clause:0» (input0 : context) (input1 : storagetype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let zt : storagetype := input1; (.bind (.guard (((«exec:match:storagetype:ValStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .ValStorageT «exec:1» => (let t : valtype := «exec:1»; (.bind (.call (Call.Valtype_ok C_0 t)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))

def «Storagetype_ok:clause:1» (input0 : context) (input1 : storagetype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let zt : storagetype := input1; (.bind (.guard (((«exec:match:storagetype:PackStorageT» zt) = true))) (fun (_ : Unit) => (match zt with | .PackStorageT «exec:1» => (let pt : packtype := «exec:1»; (.bind (.guard ((pt ∈ ([(@packtype.I8), (@packtype.I16)] : (_root_.List packtype))))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))

def Storagetype_ok_clauses (input0 : context) (input1 : storagetype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Storagetype_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Storagetype_ok:clause:1»  input0 input1)]

def «Fieldtype_ok:clause:0» (input0 : context) (input1 : fieldtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .FieldT «exec:1» «exec:2» => (let «mut» : SpecTec.«mut» := «exec:1»; (let zt : storagetype := «exec:2»; (.bind (.call (Call.Storagetype_ok C_0 zt)) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))

def Fieldtype_ok_clauses (input0 : context) (input1 : fieldtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Fieldtype_ok:clause:0»  input0 input1)]

def «Structtype_ok:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List fieldtype)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))

def «Structtype_ok:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List fieldtype)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let yt : fieldtype := «exec:2»; (let «tail:0» : (_root_.List fieldtype) := «exec:1»; (.bind (.call (Call.Fieldtype_ok C_0 yt)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«Structtype_ok:rule:iter:0» C_0 «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))

def «Structtype_ok:rule:iter:0_clauses» (input0 : context) (input1 : (_root_.List fieldtype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Structtype_ok:rule:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Structtype_ok:rule:iter:0:clause:1»  input0 input1)]

def «Structtype_ok:clause:0» (input0 : context) (input1 : structtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .StructT «exec:1» => (let «yt*» : (_root_.List fieldtype) := «exec:1»; (.bind (.call (Call.«Structtype_ok:rule:iter:0» C_0 «yt*»)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))

def Structtype_ok_clauses (input0 : context) (input1 : structtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Structtype_ok:clause:0»  input0 input1)]

def «Arraytype_ok:clause:0» (input0 : context) (input1 : arraytype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .ArrayT «exec:1» => (let yt : fieldtype := «exec:1»; (.bind (.call (Call.Fieldtype_ok C_0 yt)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))

def Arraytype_ok_clauses (input0 : context) (input1 : arraytype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Arraytype_ok:clause:0»  input0 input1)]

def «Strtype_ok:clause:0» (input0 : context) (input1 : strtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let strt : strtype := input1; (.bind (.guard (((«exec:match:strtype:DefStructT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefStructT «exec:1» => (let strctt : structtype := «exec:1»; (.bind (.call (Call.Structtype_ok C_0 strctt)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))

def «Strtype_ok:clause:1» (input0 : context) (input1 : strtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let strt : strtype := input1; (.bind (.guard (((«exec:match:strtype:DefArrayT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefArrayT «exec:1» => (let arrt : arraytype := «exec:1»; (.bind (.call (Call.Arraytype_ok C_0 arrt)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))

def «Strtype_ok:clause:2» (input0 : context) (input1 : strtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let strt : strtype := input1; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefFuncT «exec:1» => (let ft : functype := «exec:1»; (.bind (.call (Call.Functype_ok C_0 ft)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))) | _ => .unmatch)))))

def Strtype_ok_clauses (input0 : context) (input1 : strtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Strtype_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Strtype_ok:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Strtype_ok:clause:2»  input0 input1)]

def «Subtype_ok:clause:0» (input0 : context) (input1 : SpecTec.subtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let subtype : SpecTec.subtype := input1; (match subtype with | .SubT «exec:1» «exec:2» «exec:3» => (let fin : final := «exec:1»; (let «ht*» : (_root_.List heaptype) := «exec:2»; (let strt : strtype := «exec:3»; (.bind (.guard (((_root_.List.length «ht*») ≤ (1 : _root_.Nat)))) (fun (_ : Unit) => (.bind (.call (Call.«Subtype_ok:rule:iter:0» C_0 «ht*»)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.Strtype_ok C_0 strt)) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))

def Subtype_ok_clauses (input0 : context) (input1 : subtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Subtype_ok:clause:0»  input0 input1)]

def «Subtype_sub_ok':clause:0» (input0 : context) (input1 : typeidx) (input2 : strtype) (input3 : heaptype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let x : idx := input1; (let strt : strtype := input2; (let ht : heaptype := input3; (.bind (.guard (((«sub:heaptype:heaptypeVar» ht) = true))) (fun (_ : Unit) => (match («Subtype_sub_ok':rule:downcast:0» ht) with | some «exec:1» => (let «eval:0» : heaptypeVar := «exec:1»; (match «eval:0» with | .VarHT «exec:2» => (let tv : typevar := «exec:2»; (.bind (.guard (((«exec:match:typevar:StatX» tv) = true))) (fun (_ : Unit) => (match tv with | .StatX «exec:3» => (let x' : idx := «exec:3»; (.bind (.guard ((x' < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x']?) with | some «exec:4» => (let «eval:1» : deftype := «exec:4»; (.bind (.call (Call.«$unrolldt» «eval:1»)) (fun («exec:5» : subtype) => (let «eval:2» : subtype := «exec:5»; (match «eval:2» with | .SubT «exec:6» «exec:7» «exec:8» => (let fin : final := «exec:6»; (let «_ht*» : (_root_.List heaptype) := «exec:7»; (let strt' : strtype := «exec:8»; (.bind (.call (Call.«$match_strtype» (context.TYPES C_0) strt strt')) (fun («exec:9» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:9»; (.bind (.guard ((((x' < x) ∧ (fin = (@final.NoFinal))) ∧ («eval:3» = true)))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))) | none => .unmatch)))) | _ => .unmatch)))))) | none => .unmatch)))))))

def Subtype_sub_ok'_clauses (input0 : context) (input1 : typeidx) (input2 : strtype) (input3 : heaptype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Subtype_sub_ok':clause:0»  input0 input1 input2 input3)]

def «Subtype_sub_ok:rule:iter:0:clause:0» (input0 : context) (input1 : idx) (input2 : strtype) (input3 : (_root_.List heaptype)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let x : idx := input1; (let strt : strtype := input2; (match input3 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))))

def «Subtype_sub_ok:rule:iter:0:clause:1» (input0 : context) (input1 : idx) (input2 : strtype) (input3 : (_root_.List heaptype)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let x : idx := input1; (let strt : strtype := input2; (match input3 with | «exec:2» :: «exec:1» => (let ht : heaptype := «exec:2»; (let «tail:0» : (_root_.List heaptype) := «exec:1»; (.bind (.call (Call.Subtype_sub_ok' C_0 x strt ht)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«Subtype_sub_ok:rule:iter:0» C_0 x strt «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))))

def «Subtype_sub_ok:rule:iter:0_clauses» (input0 : context) (input1 : idx) (input2 : strtype) (input3 : (_root_.List heaptype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Subtype_sub_ok:rule:iter:0:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («Subtype_sub_ok:rule:iter:0:clause:1»  input0 input1 input2 input3)]

def «Subtype_sub_ok:clause:0» (input0 : context) (input1 : typeidx) (input2 : SpecTec.subtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let x : idx := input1; (let subtype : SpecTec.subtype := input2; (match subtype with | .SubT «exec:1» «exec:2» «exec:3» => (let fin : final := «exec:1»; (let «ht*» : (_root_.List heaptype) := «exec:2»; (let strt : strtype := «exec:3»; (.bind (.call (Call.«Subtype_sub_ok:rule:iter:0» C_0 x strt «ht*»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))

def Subtype_sub_ok_clauses (input0 : context) (input1 : typeidx) (input2 : subtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Subtype_sub_ok:clause:0»  input0 input1 input2)]

def «Rectype_ok:rule:iter:2:clause:0» (input0 : context) (input1 : (_root_.List deftype)) : ExecutablePlan Call (_root_.List deftype) :=
  (let C_0 : context := input0; (match input1 with | [] => (.pure ((([] : (_root_.List deftype)) : (_root_.List deftype)))) | _ :: _ => .unmatch))

def «Rectype_ok:rule:iter:2:clause:1» (input0 : context) (input1 : (_root_.List deftype)) : ExecutablePlan Call (_root_.List deftype) :=
  (let C_0 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let dt_rolled : deftype := «exec:2»; (let «tail:0» : (_root_.List deftype) := «exec:1»; (.bind (.call (Call.«$subst_deftype» (_root_.List deftype) (context.TYPES C_0) Call.«$subst_of» dt_rolled)) (fun («exec:3» : deftype) => (let «eval:3» : deftype := «exec:3»; (.bind (.call (Call.«Rectype_ok:rule:iter:2» C_0 «tail:0»)) (fun («exec:4» : (_root_.List deftype)) => (let «tail:1» : (_root_.List deftype) := «exec:4»; (.pure (((«eval:3» :: «tail:1») : (_root_.List deftype)))))))))))) | [] => .unmatch))

def «Rectype_ok:rule:iter:2_clauses» (input0 : context) (input1 : (_root_.List deftype)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List deftype)) :=
  [fun (_ : _root_.Unit) => («Rectype_ok:rule:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Rectype_ok:rule:iter:2:clause:1»  input0 input1)]

def «Rectype_ok:rule:iter:5:clause:0» (input0 : context) (input1 : (_root_.List subtype)) : ExecutablePlan Call _root_.Unit :=
  (let C_1 : context := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))

def «Rectype_ok:rule:iter:5:clause:1» (input0 : context) (input1 : (_root_.List subtype)) : ExecutablePlan Call _root_.Unit :=
  (let C_1 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let st : subtype := «exec:2»; (let «tail:0» : (_root_.List subtype) := «exec:1»; (.bind (.call (Call.Subtype_ok C_1 st)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«Rectype_ok:rule:iter:5» C_1 «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))

def «Rectype_ok:rule:iter:5_clauses» (input0 : context) (input1 : (_root_.List subtype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Rectype_ok:rule:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Rectype_ok:rule:iter:5:clause:1»  input0 input1)]

def «Rectype_ok:rule:iter:6:clause:0» (input0 : context) (input1 : idx) (input2 : (_root_.List n)) (input3 : (_root_.List subtype)) : ExecutablePlan Call _root_.Unit :=
  (let C_1 : context := input0; (let x : idx := input1; (match input2 with | [] => (match input3 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)))

def «Rectype_ok:rule:iter:6:clause:1» (input0 : context) (input1 : idx) (input2 : (_root_.List SpecTec.n)) (input3 : (_root_.List subtype)) : ExecutablePlan Call _root_.Unit :=
  (let C_1 : context := input0; (let x : idx := input1; (match input2 with | «exec:2» :: «exec:1» => (let n : SpecTec.n := «exec:2»; (let «tail:0» : (_root_.List SpecTec.n) := «exec:1»; (match input3 with | «exec:4» :: «exec:3» => (let st : subtype := «exec:4»; (let «tail:1» : (_root_.List subtype) := «exec:3»; (.bind (.call (Call.Subtype_sub_ok C_1 (x + n) st)) (fun («exec:5» : _root_.Unit) => (.bind (.call (Call.«Rectype_ok:rule:iter:6» C_1 x «tail:0» «tail:1»)) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)))

def «Rectype_ok:rule:iter:6_clauses» (input0 : context) (input1 : idx) (input2 : (_root_.List n)) (input3 : (_root_.List subtype)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Rectype_ok:rule:iter:6:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («Rectype_ok:rule:iter:6:clause:1»  input0 input1 input2 input3)]

def «Rectype_ok:clause:0» (input0 : context) (input1 : SpecTec.rectype) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let rectype : SpecTec.rectype := input1; (match rectype with | .RecT «exec:1» => (let «st*» : (_root_.List subtype) := «exec:1»; (let x : idx := (_root_.List.length (context.TYPES C_0)); (.bind (.call (Call.«$range» (_root_.List.length «st*»))) (fun («exec:2» : (_root_.List _root_.Nat)) => (let «eval:0» : (_root_.List _root_.Nat) := «exec:2»; (let «n*» : (_root_.List n) := «eval:0»; (.bind (.call (Call.«$rolldt» x rectype)) (fun («exec:3» : (_root_.List deftype)) => (let «eval:1» : (_root_.List deftype) := «exec:3»; (let «dt_rolled*» : (_root_.List deftype) := «eval:1»; (.bind (.call (Call.«Rectype_ok:rule:iter:2» C_0 «dt_rolled*»)) (fun («exec:4» : (_root_.List deftype)) => (let «eval:4» : (_root_.List deftype) := «exec:4»; (let «dt*» : (_root_.List deftype) := «eval:4»; (let C_1 : context := ({ C_0 with TYPES := ((context.TYPES C_0) ++ «dt*») } : context); (.bind (.call (Call.«Rectype_ok:rule:iter:5» C_1 «st*»)) (fun («exec:5» : _root_.Unit) => (.bind (.guard ((_root_.List.length «st*») = (_root_.List.length «n*»))) (fun (_ : Unit) => (.bind (.call (Call.«Rectype_ok:rule:iter:6» C_1 x «n*» «st*»)) (fun («exec:6» : _root_.Unit) => (.pure ((C_1 : context)))))))))))))))))))))))))))

def Rectype_ok_clauses (input0 : context) (input1 : rectype) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Rectype_ok:clause:0»  input0 input1)]

def «Globaltype_ok:clause:0» (input0 : context) (input1 : globaltype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .GlobalT «exec:1» «exec:2» => (let «mut» : SpecTec.«mut» := «exec:1»; (let t : valtype := «exec:2»; (.bind (.call (Call.Valtype_ok C_0 t)) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))

def Globaltype_ok_clauses (input0 : context) (input1 : globaltype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Globaltype_ok:clause:0»  input0 input1)]

def «Tagtype_ok:clause:0» (input0 : context) (input1 : tagtype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .TagT «exec:1» => (let dt : deftype := «exec:1»; (.bind (.call (Call.«$expanddt» dt)) (fun («exec:2» : strtype) => (let «eval:0» : strtype := «exec:2»; (.bind (.call (Call.«$functype_of_strtype» «eval:0»)) (fun («exec:3» : functype) => (let «eval:1» : functype := «exec:3»; (match «eval:1» with | .FuncT «exec:4» «exec:5» => (let _rest : resulttype := «exec:4»; (let «valtype*» : (_root_.List valtype) := «exec:5»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «valtype*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))))

def Tagtype_ok_clauses (input0 : context) (input1 : tagtype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Tagtype_ok:clause:0»  input0 input1)]

def «Tabletype_ok:clause:0» (input0 : context) (input1 : tabletype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .TableT «exec:1» «exec:2» «exec:3» => (let «at» : addrtype := «exec:1»; (let lim : limits := «exec:2»; (let rt : reftype := «exec:3»; (.bind (.guard (((«exec:match:addrtype:I32AT» «at») = true))) (fun (_ : Unit) => (.bind (.call (Call.Reftype_ok C_0 rt)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.Limits_ok C_0 (4294967295 : _root_.Nat) lim)) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))))

def «Tabletype_ok:clause:1» (input0 : context) (input1 : tabletype) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .TableT «exec:1» «exec:2» «exec:3» => (let «at» : addrtype := «exec:1»; (let lim : limits := «exec:2»; (let rt : reftype := «exec:3»; (.bind (.guard (((«exec:match:addrtype:I64AT» «at») = true))) (fun (_ : Unit) => (.bind (.call (Call.Reftype_ok C_0 rt)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.Limits_ok C_0 (18446744073709551615 : _root_.Nat) lim)) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))))

def Tabletype_ok_clauses (input0 : context) (input1 : tabletype) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Tabletype_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Tabletype_ok:clause:1»  input0 input1)]

def «$array_type:clause:0» (input0 : context) (input1 : typeidx) : ExecutablePlan Call arraytype :=
  (let C : context := input0; (let x : idx := input1; (.bind (.guard ((x < (_root_.List.length (context.TYPES C))))) (fun (_ : Unit) => (match ((context.TYPES C)[x]?) with | some «exec:1» => (let «eval:0» : deftype := «exec:1»; (.bind (.call (Call.«$expanddt» «eval:0»)) (fun («exec:2» : strtype) => (let «eval:1» : strtype := «exec:2»; (let strt : strtype := «eval:1»; (.bind (.guard (((«exec:match:strtype:DefArrayT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefArrayT «exec:3» => (let arrt : arraytype := «exec:3»; (.pure ((arrt : arraytype)))) | _ => .unmatch)))))))) | none => .unmatch)))))

def «$array_type_clauses» (input0 : context) (input1 : typeidx) : List (ExecutablePlan.Clause Call _root_.Unit arraytype) :=
  [fun (_ : _root_.Unit) => («$array_type:clause:0»  input0 input1)]

def «$struct_type:clause:0» (input0 : context) (input1 : typeidx) : ExecutablePlan Call structtype :=
  (let C : context := input0; (let x : idx := input1; (.bind (.guard ((x < (_root_.List.length (context.TYPES C))))) (fun (_ : Unit) => (match ((context.TYPES C)[x]?) with | some «exec:1» => (let «eval:0» : deftype := «exec:1»; (.bind (.call (Call.«$expanddt» «eval:0»)) (fun («exec:2» : strtype) => (let «eval:1» : strtype := «exec:2»; (let strt : strtype := «eval:1»; (.bind (.guard (((«exec:match:strtype:DefStructT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefStructT «exec:3» => (let strctt : structtype := «exec:3»; (.pure ((strctt : structtype)))) | _ => .unmatch)))))))) | none => .unmatch)))))

def «$struct_type_clauses» (input0 : context) (input1 : typeidx) : List (ExecutablePlan.Clause Call _root_.Unit structtype) :=
  [fun (_ : _root_.Unit) => («$struct_type:clause:0»  input0 input1)]

def «$func_type:clause:0» (input0 : context) (input1 : typeidx) : ExecutablePlan Call functype :=
  (let C : context := input0; (let x : idx := input1; (.bind (.guard ((x < (_root_.List.length (context.TYPES C))))) (fun (_ : Unit) => (match ((context.TYPES C)[x]?) with | some «exec:1» => (let «eval:0» : deftype := «exec:1»; (.bind (.call (Call.«$expanddt» «eval:0»)) (fun («exec:2» : strtype) => (let «eval:1» : strtype := «exec:2»; (let strt : strtype := «eval:1»; (.bind (.guard (((«exec:match:strtype:DefFuncT» strt) = true))) (fun (_ : Unit) => (match strt with | .DefFuncT «exec:3» => (let ft : functype := «exec:3»; (.pure ((ft : functype)))) | _ => .unmatch)))))))) | none => .unmatch)))))

def «$func_type_clauses» (input0 : context) (input1 : typeidx) : List (ExecutablePlan.Clause Call _root_.Unit functype) :=
  [fun (_ : _root_.Unit) => («$func_type:clause:0»  input0 input1)]

def «Blocktype_ok:clause:0» (input0 : context) (input1 : SpecTec.blocktype) : ExecutablePlan Call instrtype :=
  (let C_0 : context := input0; (let blocktype : SpecTec.blocktype := input1; (.bind (.guard ((@SpecTec.blocktype.ValBlockType ((_root_.Option.none) : (_root_.Option valtype))) = blocktype)) (fun (_ : Unit) => (.pure (((@instrtype.InstrT ([] : (_root_.List valtype)) ([] : (_root_.List valtype)) ([] : (_root_.List localidx))) : instrtype)))))))

def «Blocktype_ok:clause:1» (input0 : context) (input1 : SpecTec.blocktype) : ExecutablePlan Call instrtype :=
  (let C_0 : context := input0; (let blocktype : SpecTec.blocktype := input1; (.bind (.guard (((«exec:match:blocktype:ValBlockType» blocktype) = true))) (fun (_ : Unit) => (match blocktype with | .ValBlockType «exec:1» => (let valtype? : (_root_.Option valtype) := «exec:1»; (.bind (.guard (((_root_.Option.isSome valtype?) = true))) (fun (_ : Unit) => (match valtype? with | some «exec:2» => (let t : valtype := «exec:2»; (.bind (.call (Call.Valtype_ok C_0 t)) (fun («exec:3» : _root_.Unit) => (.pure (((@instrtype.InstrT ([] : (_root_.List valtype)) ([t] : resulttype) ([] : (_root_.List localidx))) : instrtype)))))) | none => .unmatch)))) | _ => .unmatch)))))

def «Blocktype_ok:clause:2» (input0 : context) (input1 : SpecTec.blocktype) : ExecutablePlan Call instrtype :=
  (let C_0 : context := input0; (let blocktype : SpecTec.blocktype := input1; (.bind (.guard (((«exec:match:blocktype:VarBlockType» blocktype) = true))) (fun (_ : Unit) => (match blocktype with | .VarBlockType «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$func_type» C_0 x)) (fun («exec:2» : functype) => (let «eval:0» : functype := «exec:2»; (match «eval:0» with | .FuncT «exec:3» «exec:4» => (let «t_1*» : (_root_.List valtype) := «exec:3»; (let «t_2*» : (_root_.List valtype) := «exec:4»; (.pure (((@instrtype.InstrT «t_1*» «t_2*» ([] : (_root_.List localidx))) : instrtype)))))))))) | _ => .unmatch)))))

def Blocktype_ok_clauses (input0 : context) (input1 : blocktype) : List (ExecutablePlan.Clause Call _root_.Unit instrtype) :=
  [fun (_ : _root_.Unit) => («Blocktype_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Blocktype_ok:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Blocktype_ok:clause:2»  input0 input1)]

def «Catch_ok:clause:0» (input0 : context) (input1 : resulttype) (input2 : SpecTec.«catch») : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t*» : (_root_.List valtype) := input1; (let «catch» : SpecTec.«catch» := input2; (.bind (.guard (((«exec:match:catch:Catch» «catch») = true))) (fun (_ : Unit) => (match «catch» with | .Catch «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.TAGS C_0))))) (fun (_ : Unit) => (match ((context.TAGS C_0)[x]?) with | some «exec:3» => (let «eval:0» : tagtype := «exec:3»; (match «eval:0» with | .TagT «exec:4» => (let dt : deftype := «exec:4»; (.bind (.call (Call.«$expanddt» dt)) (fun («exec:5» : strtype) => (let «eval:1» : strtype := «exec:5»; (.bind (.call (Call.«$functype_of_strtype» «eval:1»)) (fun («exec:6» : functype) => (let «eval:2» : functype := «exec:6»; (match «eval:2» with | .FuncT «exec:7» «exec:8» => (let «t_1*» : (_root_.List valtype) := «exec:7»; (let «t_2*» : (_root_.List valtype) := «exec:8»; (.bind (.guard ((y < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[y]?) with | some «exec:9» => (let «eval:3» : resulttype := «exec:9»; (.bind (.call (Call.«$match_resulttype» (context.TYPES C_0) «t_1*» «eval:3»)) (fun («exec:10» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:10»; (.bind (.guard ((«eval:4» = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | none => .unmatch))))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Catch_ok:clause:1» (input0 : context) (input1 : resulttype) (input2 : SpecTec.«catch») : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t*» : (_root_.List valtype) := input1; (let «catch» : SpecTec.«catch» := input2; (.bind (.guard (((«exec:match:catch:CatchRef» «catch») = true))) (fun (_ : Unit) => (match «catch» with | .CatchRef «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.TAGS C_0))))) (fun (_ : Unit) => (match ((context.TAGS C_0)[x]?) with | some «exec:3» => (let «eval:0» : tagtype := «exec:3»; (match «eval:0» with | .TagT «exec:4» => (let dt : deftype := «exec:4»; (.bind (.call (Call.«$expanddt» dt)) (fun («exec:5» : strtype) => (let «eval:1» : strtype := «exec:5»; (.bind (.call (Call.«$functype_of_strtype» «eval:1»)) (fun («exec:6» : functype) => (let «eval:2» : functype := «exec:6»; (match «eval:2» with | .FuncT «exec:7» «exec:8» => (let «t_1*» : (_root_.List valtype) := «exec:7»; (let «t_2*» : (_root_.List valtype) := «exec:8»; (.bind (.guard ((y < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[y]?) with | some «exec:9» => (let «eval:3» : resulttype := «exec:9»; (.bind (.call (Call.«$match_resulttype» (context.TYPES C_0) («t_1*» ++ ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.ExnHT)))] : (_root_.List valtype))) «eval:3»)) (fun («exec:10» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:10»; (.bind (.guard ((«eval:4» = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | none => .unmatch))))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Catch_ok:clause:2» (input0 : context) (input1 : resulttype) (input2 : SpecTec.«catch») : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t*» : (_root_.List valtype) := input1; (let «catch» : SpecTec.«catch» := input2; (.bind (.guard (((«exec:match:catch:CatchAll» «catch») = true))) (fun (_ : Unit) => (match «catch» with | .CatchAll «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:2» => (let «eval:0» : resulttype := «exec:2»; (.bind (.call (Call.«$match_resulttype» (context.TYPES C_0) ([] : (_root_.List valtype)) «eval:0»)) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Catch_ok:clause:3» (input0 : context) (input1 : resulttype) (input2 : SpecTec.«catch») : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t*» : (_root_.List valtype) := input1; (let «catch» : SpecTec.«catch» := input2; (.bind (.guard (((«exec:match:catch:CatchAllRef» «catch») = true))) (fun (_ : Unit) => (match «catch» with | .CatchAllRef «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:2» => (let «eval:0» : resulttype := «exec:2»; (.bind (.call (Call.«$match_resulttype» (context.TYPES C_0) ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.ExnHT)))] : (_root_.List valtype)) «eval:0»)) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def Catch_ok_clauses (input0 : context) (input1 : resulttype) (input2 : «catch») : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Catch_ok:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Catch_ok:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («Catch_ok:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («Catch_ok:clause:3»  input0 input1 input2)]

def «Instr_ok:br_table:iter:4:clause:0» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List idx)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t*» : (_root_.List valtype) := input1; (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)))

def «Instr_ok:br_table:iter:4:clause:1» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List idx)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t*» : (_root_.List valtype) := input1; (match input2 with | «exec:2» :: «exec:1» => (let x : idx := «exec:2»; (let «tail:0» : (_root_.List idx) := «exec:1»; (match ((context.LABELS C_0)[x]?) with | some «exec:3» => (let «eval:5» : resulttype := «exec:3»; (.bind (.call (Call.Match_resulttype C_0 «t*» «eval:5»)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.«Instr_ok:br_table:iter:4» C_0 «t*» «tail:0»)) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))) | none => .unmatch))) | [] => .unmatch)))

def «Instr_ok:br_table:iter:4_clauses» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List idx)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Instr_ok:br_table:iter:4:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:br_table:iter:4:clause:1»  input0 input1 input2)]

def «Instr_ok:try_table:iter:0:clause:0» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List «catch»)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t_2*» : (_root_.List valtype) := input1; (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)))

def «Instr_ok:try_table:iter:0:clause:1» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List SpecTec.«catch»)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let «t_2*» : (_root_.List valtype) := input1; (match input2 with | «exec:2» :: «exec:1» => (let «catch» : SpecTec.«catch» := «exec:2»; (let «tail:0» : (_root_.List SpecTec.«catch») := «exec:1»; (.bind (.call (Call.Catch_ok C_0 «t_2*» «catch»)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«Instr_ok:try_table:iter:0» C_0 «t_2*» «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)))

def «Instr_ok:try_table:iter:0_clauses» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List «catch»)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Instr_ok:try_table:iter:0:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:try_table:iter:0:clause:1»  input0 input1 input2)]

def «Instrs_ok:clause:0» (input0 : context) (input1 : inferresulttype) (input2 : (_root_.List instr)) : ExecutablePlan Call (inferresulttype × (_root_.List idx)) :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let «instr*» : (_root_.List instr) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «instr*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (((irt, ([] : (_root_.List idx))) : (inferresulttype × (_root_.List idx))))))))))

def «Instrs_ok:clause:1» (input0 : context) (input1 : inferresulttype) (input2 : (_root_.List instr)) : ExecutablePlan Call (inferresulttype × (_root_.List idx)) :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let «instr'*» : (_root_.List instr) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «instr'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «instr'*» with | «exec:2» :: «exec:1» => (let instr_1 : instr := «exec:2»; (let «instr*» : (_root_.List instr) := «exec:1»; (.bind (.call (Call.Instr_ok C_0 irt instr_1)) (fun («exec:3» : inferinstrtype) => (let irt_1 : inferresulttype := ((«exec:3»).1).INS; (let irt_2 : inferresulttype := ((«exec:3»).1).OUTS; (let «idx*» : (_root_.List idx) := («exec:3»).2; (.bind (.call (Call.«$init_locals» C_0 «idx*»)) (fun («exec:4» : context) => (let «eval:0» : context := «exec:4»; (let C_1 : context := «eval:0»; (.bind (.call (Call.«$pop» C_0 irt_1 irt)) (fun («exec:5» : (SpecTec.ellipses × resulttype)) => (let «eval:1» : (SpecTec.ellipses × resulttype) := «exec:5»; (.bind (.call (Call.«$push» C_0 irt_2 «eval:1»)) (fun («exec:6» : (SpecTec.ellipses × resulttype)) => (let «eval:2» : (SpecTec.ellipses × resulttype) := «exec:6»; (let ellipses : SpecTec.ellipses := («eval:2»).1; (let «valtype*» : (_root_.List valtype) := («eval:2»).2; (.bind (.call (Call.Instrs_ok C_1 (ellipses, «valtype*») «instr*»)) (fun («exec:7» : (inferresulttype × (_root_.List idx))) => (let irt' : inferresulttype := («exec:7»).1; (let «idx'*» : (_root_.List idx) := («exec:7»).2; (.pure (((irt', «idx'*») : (inferresulttype × (_root_.List idx)))))))))))))))))))))))))))) | [] => .unmatch))))))

def Instrs_ok_clauses (input0 : context) (input1 : inferresulttype) (input2 : (_root_.List instr)) : List (ExecutablePlan.Clause Call _root_.Unit (inferresulttype × (_root_.List idx))) :=
  [fun (_ : _root_.Unit) => («Instrs_ok:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Instrs_ok:clause:1»  input0 input1 input2)]

def «Instr_ok:clause:0» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:UNREACHABLE» instr) = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))

def «Instr_ok:clause:1» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:NOP» instr) = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))

def «Instr_ok:clause:2» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:DROP» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$peek» (0 : _root_.Nat) irt)) (fun («exec:1» : valtype) => (let «eval:0» : valtype := «exec:1»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([«eval:0»] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))

def «Instr_ok:clause:3» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard ((@SpecTec.instr.SELECT ((_root_.Option.none) : (_root_.Option (_root_.List valtype)))) = instr)) (fun (_ : Unit) => (.bind (.call (Call.«$peek» (1 : _root_.Nat) irt)) (fun («exec:1» : valtype) => (let «eval:0» : valtype := «exec:1»; (let t : valtype := «eval:0»; (.bind (.call (Call.«$is_num_type» t)) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.call (Call.«$is_vec_type» t)) (fun («exec:3» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:3»; (.bind (.guard (((«eval:1» = true) ∨ («eval:2» = true)))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, t, (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))))))))))

def «Instr_ok:clause:4» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:SELECT» instr) = true))) (fun (_ : Unit) => (match instr with | .SELECT «exec:1» => (let «valtype*?» : (_root_.Option (_root_.List valtype)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome «valtype*?») = true))) (fun (_ : Unit) => (match «valtype*?» with | some «exec:2» => (let «t*» : (_root_.List valtype) := «exec:2»; (.bind (.guard ((1 : _root_.Nat) = (_root_.List.length «t*»))) (fun (_ : Unit) => (.bind (.call (Call.Resulttype_ok C_0 «t*»)) (fun («exec:3» : _root_.Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ((«t*» ++ «t*») ++ ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), «t*») } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:5» (input0 : context) (input1 : inferresulttype) (input2 : instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr' : instr := input2; (.bind (.guard (((«exec:match:instr:BLOCK» instr') = true))) (fun (_ : Unit) => (match instr' with | .BLOCK «exec:1» «exec:2» => (let blocktype : SpecTec.blocktype := «exec:1»; (let «instr*» : (_root_.List instr) := «exec:2»; (.bind (.call (Call.Blocktype_ok C_0 blocktype)) (fun («exec:3» : instrtype) => (match «exec:3» with | .InstrT «exec:4» «exec:5» «exec:6» => (let «t_1*» : (_root_.List valtype) := «exec:4»; (let «t_2*» : (_root_.List valtype) := «exec:5»; (let «x*» : (_root_.List idx) := «exec:6»; (.bind (.call (Call.Block_ok ({ C_0 with LABELS := (([«t_2*»] : (_root_.List resulttype)) ++ (context.LABELS C_0)) } : context) (@instrtype.InstrT «t_1*» «t_2*» «x*») «instr*»)) (fun («exec:7» : _root_.Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), «t_1*»), OUTS := ((@ellipses.NoEllipses), «t_2*») } : inferfunctype), «x*») : inferinstrtype))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:6» (input0 : context) (input1 : inferresulttype) (input2 : instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr' : instr := input2; (.bind (.guard (((«exec:match:instr:LOOP» instr') = true))) (fun (_ : Unit) => (match instr' with | .LOOP «exec:1» «exec:2» => (let blocktype : SpecTec.blocktype := «exec:1»; (let «instr*» : (_root_.List instr) := «exec:2»; (.bind (.call (Call.Blocktype_ok C_0 blocktype)) (fun («exec:3» : instrtype) => (match «exec:3» with | .InstrT «exec:4» «exec:5» «exec:6» => (let «t_1*» : (_root_.List valtype) := «exec:4»; (let «t_2*» : (_root_.List valtype) := «exec:5»; (let «x*» : (_root_.List idx) := «exec:6»; (.bind (.call (Call.Block_ok ({ C_0 with LABELS := (([«t_1*»] : (_root_.List resulttype)) ++ (context.LABELS C_0)) } : context) (@instrtype.InstrT «t_1*» «t_2*» «x*») «instr*»)) (fun («exec:7» : _root_.Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), «t_1*»), OUTS := ((@ellipses.NoEllipses), «t_2*») } : inferfunctype), «x*») : inferinstrtype))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:7» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:IF % % ELSE %» instr) = true))) (fun (_ : Unit) => (match instr with | .«IF % % ELSE %» «exec:1» «exec:2» «exec:3» => (let blocktype : SpecTec.blocktype := «exec:1»; (let «instr_t*» : (_root_.List SpecTec.instr) := «exec:2»; (let «instr_f*» : (_root_.List SpecTec.instr) := «exec:3»; (.bind (.call (Call.Blocktype_ok C_0 blocktype)) (fun («exec:4» : instrtype) => (match «exec:4» with | .InstrT «exec:5» «exec:6» «exec:7» => (let «t_1*» : (_root_.List valtype) := «exec:5»; (let «t_2*» : (_root_.List valtype) := «exec:6»; (let «x*» : (_root_.List idx) := «exec:7»; (.bind (.call (Call.Block_ok ({ C_0 with LABELS := (([«t_2*»] : (_root_.List resulttype)) ++ (context.LABELS C_0)) } : context) (@instrtype.InstrT «t_1*» «t_2*» «x*») «instr_t*»)) (fun («exec:8» : _root_.Unit) => (.bind (.call (Call.Block_ok ({ C_0 with LABELS := (([«t_2*»] : (_root_.List resulttype)) ++ (context.LABELS C_0)) } : context) (@instrtype.InstrT «t_1*» «t_2*» «x*») «instr_f*»)) (fun («exec:9» : _root_.Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), («t_1*» ++ ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), «t_2*») } : inferfunctype), «x*») : inferinstrtype)))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:8» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:BR» instr) = true))) (fun (_ : Unit) => (match instr with | .BR «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:2» => (let «eval:0» : resulttype := «exec:2»; (.pure (((({ INS := ((@ellipses.Ellipses), «eval:0»), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:9» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:BR_IF» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_IF «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:2» => (let «eval:0» : resulttype := «exec:2»; (let «t*» : (_root_.List valtype) := «eval:0»; (.pure (((({ INS := ((@ellipses.NoEllipses), («t*» ++ ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), «t*») } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:10» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:BR_TABLE» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_TABLE «exec:1» «exec:2» => (let «x*» : (_root_.List idx) := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((y < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[y]?) with | some «exec:3» => (let «eval:0» : resulttype := «exec:3»; (let n : SpecTec.n := (_root_.List.length «eval:0»); (.bind (.call (Call.«$init_valtypes» irt (0 : _root_.Nat) n)) (fun («exec:4» : (_root_.List valtype)) => (let «eval:1» : (_root_.List valtype) := «exec:4»; (let «t*» : (_root_.List valtype) := «eval:1»; (match ((context.LABELS C_0)[y]?) with | some «exec:5» => (let «eval:2» : resulttype := «exec:5»; (.bind (.call (Call.Match_resulttype C_0 «t*» «eval:2»)) (fun («exec:6» : _root_.Unit) => (.bind (.call (Call.«Instr_ok:br_table:iter:3» C_0 «x*»)) (fun («exec:7» : _root_.Unit) => (.bind (.call (Call.«Instr_ok:br_table:iter:4» C_0 «t*» «x*»)) (fun («exec:8» : _root_.Unit) => (.pure (((({ INS := ((@ellipses.Ellipses), («t*» ++ ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype)))), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))) | none => .unmatch))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:11» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:BR_ON_NULL» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_ON_NULL «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$peek_ref» (0 : _root_.Nat) irt)) (fun («exec:2» : reftype) => (let «eval:0» : reftype := «exec:2»; (match «eval:0» with | .«% %» «exec:3» «exec:4» => (let null : SpecTec.null := «exec:3»; (let ht : heaptype := «exec:4»; (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:5» => (let «eval:1» : resulttype := «exec:5»; (let «t*» : (_root_.List valtype) := «eval:1»; (.pure (((({ INS := ((@ellipses.NoEllipses), («t*» ++ ([(@valtype.RefT (@reftype.«% %» (@SpecTec.null.Null) ht))] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), («t*» ++ ([(@valtype.RefT (@reftype.«% %» (@SpecTec.null.NoNull) ht))] : (_root_.List valtype)))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))) | none => .unmatch)))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:12» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:BR_ON_NON_NULL» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_ON_NON_NULL «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$peek_ref» (0 : _root_.Nat) irt)) (fun («exec:2» : reftype) => (let «eval:0» : reftype := «exec:2»; (match «eval:0» with | .«% %» «exec:3» «exec:4» => (let null : SpecTec.null := «exec:3»; (let ht : heaptype := «exec:4»; (let t' : valtype := (@valtype.RefT (@reftype.«% %» (@SpecTec.null.NoNull) ht)); (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:5» => (let «eval:1» : resulttype := «exec:5»; (let i : SpecTec.i := (_root_.List.length «eval:1»); (.bind (.guard ((i > (0 : _root_.Nat)))) (fun (_ : Unit) => (let int : _root_.Int := ((_root_.Int.ofNat i) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:6» => (let «eval:2» : SpecTec.i := «exec:6»; (let i' : SpecTec.i := «eval:2»; (match ((context.LABELS C_0)[x]?) with | some «exec:7» => (let «eval:3» : resulttype := «exec:7»; (.bind (ExecutablePlan.require ((((0 : _root_.Nat) + i') ≤ (_root_.List.length «eval:3»))) "slice out of bounds") (fun (_ : Unit) => (let «t_h*» : (_root_.List valtype) := (_root_.List.take i' (_root_.List.drop (0 : _root_.Nat) «eval:3»)); (match ((context.LABELS C_0)[x]?) with | some «exec:8» => (let «eval:4» : resulttype := «exec:8»; (.bind (.guard ((i' < (_root_.List.length «eval:4»)))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:9» => (let «eval:5» : resulttype := «exec:9»; (match («eval:5»[i']?) with | some «exec:10» => (let «eval:6» : valtype := «exec:10»; (let t_l : valtype := «eval:6»; (.bind (.call (Call.«$match_valtype» (context.TYPES C_0) t' t_l)) (fun («exec:11» : _root_.Bool) => (let «eval:7» : _root_.Bool := «exec:11»; (.bind (.guard ((«eval:7» = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), («t_h*» ++ ([(@valtype.RefT (@reftype.«% %» (@SpecTec.null.Null) ht))] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), «t_h*») } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))) | none => .unmatch)) | none => .unmatch)))) | none => .unmatch))))) | none => .unmatch))) | none => .unmatch)))))))) | none => .unmatch))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:13» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:BR_ON_CAST» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_ON_CAST «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let rt_1 : reftype := «exec:2»; (let rt_2 : reftype := «exec:3»; (.bind (.call (Call.Reftype_ok C_0 rt_1)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.Reftype_ok C_0 rt_2)) (fun («exec:5» : _root_.Unit) => (.bind (.call (Call.«$match_reftype» (context.TYPES C_0) rt_2 rt_1)) (fun («exec:6» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:6»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:7» => (let «eval:1» : resulttype := «exec:7»; (let i : SpecTec.i := (_root_.List.length «eval:1»); (.bind (.guard ((i > (0 : _root_.Nat)))) (fun (_ : Unit) => (let int : _root_.Int := ((_root_.Int.ofNat i) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:8» => (let «eval:2» : SpecTec.i := «exec:8»; (let i' : SpecTec.i := «eval:2»; (match ((context.LABELS C_0)[x]?) with | some «exec:9» => (let «eval:3» : resulttype := «exec:9»; (.bind (ExecutablePlan.require ((((0 : _root_.Nat) + i') ≤ (_root_.List.length «eval:3»))) "slice out of bounds") (fun (_ : Unit) => (let «t_h*» : (_root_.List valtype) := (_root_.List.take i' (_root_.List.drop (0 : _root_.Nat) «eval:3»)); (match ((context.LABELS C_0)[x]?) with | some «exec:10» => (let «eval:4» : resulttype := «exec:10»; (.bind (.guard ((i' < (_root_.List.length «eval:4»)))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:11» => (let «eval:5» : resulttype := «exec:11»; (match («eval:5»[i']?) with | some «exec:12» => (let «eval:6» : valtype := «exec:12»; (let t_l : valtype := «eval:6»; (.bind (.call (Call.«$match_valtype» (context.TYPES C_0) (@valtype.RefT rt_2) t_l)) (fun («exec:13» : _root_.Bool) => (let «eval:7» : _root_.Bool := «exec:13»; (.bind (.guard ((«eval:7» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$diff_reftype» rt_1 rt_2)) (fun («exec:14» : reftype) => (let «eval:8» : reftype := «exec:14»; (.pure (((({ INS := ((@ellipses.NoEllipses), («t_h*» ++ ([(@valtype.RefT rt_1)] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), («t_h*» ++ ([(@valtype.RefT «eval:8»)] : (_root_.List valtype)))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))) | none => .unmatch)) | none => .unmatch)))) | none => .unmatch))))) | none => .unmatch))) | none => .unmatch)))))))) | none => .unmatch))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:14» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:BR_ON_CAST_FAIL» instr) = true))) (fun (_ : Unit) => (match instr with | .BR_ON_CAST_FAIL «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let rt_1 : reftype := «exec:2»; (let rt_2 : reftype := «exec:3»; (.bind (.call (Call.Reftype_ok C_0 rt_1)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.Reftype_ok C_0 rt_2)) (fun («exec:5» : _root_.Unit) => (.bind (.call (Call.«$diff_reftype» rt_1 rt_2)) (fun («exec:6» : reftype) => (let «eval:0» : reftype := «exec:6»; (let rt_1' : reftype := «eval:0»; (.bind (.call (Call.«$match_reftype» (context.TYPES C_0) rt_2 rt_1)) (fun («exec:7» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:7»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.LABELS C_0))))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:8» => (let «eval:2» : resulttype := «exec:8»; (let i : SpecTec.i := (_root_.List.length «eval:2»); (.bind (.guard ((i > (0 : _root_.Nat)))) (fun (_ : Unit) => (let int : _root_.Int := ((_root_.Int.ofNat i) - (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ int)) = true))) (fun (_ : Unit) => (match (_root_.Int.toNat? int) with | some «exec:9» => (let «eval:3» : SpecTec.i := «exec:9»; (let i' : SpecTec.i := «eval:3»; (match ((context.LABELS C_0)[x]?) with | some «exec:10» => (let «eval:4» : resulttype := «exec:10»; (.bind (ExecutablePlan.require ((((0 : _root_.Nat) + i') ≤ (_root_.List.length «eval:4»))) "slice out of bounds") (fun (_ : Unit) => (let «t_h*» : (_root_.List valtype) := (_root_.List.take i' (_root_.List.drop (0 : _root_.Nat) «eval:4»)); (match ((context.LABELS C_0)[x]?) with | some «exec:11» => (let «eval:5» : resulttype := «exec:11»; (.bind (.guard ((i' < (_root_.List.length «eval:5»)))) (fun (_ : Unit) => (match ((context.LABELS C_0)[x]?) with | some «exec:12» => (let «eval:6» : resulttype := «exec:12»; (match («eval:6»[i']?) with | some «exec:13» => (let «eval:7» : valtype := «exec:13»; (let t_l : valtype := «eval:7»; (.bind (.call (Call.«$match_valtype» (context.TYPES C_0) (@valtype.RefT rt_1') t_l)) (fun («exec:14» : _root_.Bool) => (let «eval:8» : _root_.Bool := «exec:14»; (.bind (.guard ((«eval:8» = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), («t_h*» ++ ([(@valtype.RefT rt_1)] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), («t_h*» ++ ([(@valtype.RefT rt_2)] : (_root_.List valtype)))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))) | none => .unmatch)) | none => .unmatch)))) | none => .unmatch))))) | none => .unmatch))) | none => .unmatch)))))))) | none => .unmatch))))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:15» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:CALL» instr) = true))) (fun (_ : Unit) => (match instr with | .CALL «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.FUNCS C_0))))) (fun (_ : Unit) => (match ((context.FUNCS C_0)[x]?) with | some «exec:2» => (let «eval:0» : deftype := «exec:2»; (.bind (.call (Call.«$expanddt» «eval:0»)) (fun («exec:3» : strtype) => (let «eval:1» : strtype := «exec:3»; (.bind (.call (Call.«$functype_of_strtype» «eval:1»)) (fun («exec:4» : functype) => (let «eval:2» : functype := «exec:4»; (match «eval:2» with | .FuncT «exec:5» «exec:6» => (let «t_1*» : (_root_.List valtype) := «exec:5»; (let «t_2*» : (_root_.List valtype) := «exec:6»; (.pure (((({ INS := ((@ellipses.NoEllipses), «t_1*»), OUTS := ((@ellipses.NoEllipses), «t_2*») } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:16» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:CALL_REF» instr) = true))) (fun (_ : Unit) => (match instr with | .CALL_REF «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$func_type» C_0 x)) (fun («exec:2» : functype) => (let «eval:0» : functype := «exec:2»; (match «eval:0» with | .FuncT «exec:3» «exec:4» => (let «t_1*» : (_root_.List valtype) := «exec:3»; (let «t_2*» : (_root_.List valtype) := «exec:4»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:5» => (let «eval:1» : deftype := «exec:5»; (.pure (((({ INS := ((@ellipses.NoEllipses), («t_1*» ++ ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:1»)))] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), «t_2*») } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:17» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:CALL_INDIRECT» instr) = true))) (fun (_ : Unit) => (match instr with | .CALL_INDIRECT «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:3» => (let «eval:0» : tabletype := «exec:3»; (match «eval:0» with | .TableT «exec:4» «exec:5» «exec:6» => (let «at» : addrtype := «exec:4»; (let lim : limits := «exec:5»; (let rt : reftype := «exec:6»; (.bind (.call (Call.«$func_type» C_0 y)) (fun («exec:7» : functype) => (let «eval:1» : functype := «exec:7»; (match «eval:1» with | .FuncT «exec:8» «exec:9» => (let «t_1*» : (_root_.List valtype) := «exec:8»; (let «t_2*» : (_root_.List valtype) := «exec:9»; (.bind (.call (Call.«$match_reftype» (context.TYPES C_0) rt (@reftype.«% %» (@null.Null) (@heaptype.FuncHT)))) (fun («exec:10» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:10»; (.bind (.guard ((«eval:2» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:11» : numtype) => (let «eval:3» : numtype := «exec:11»; (.pure (((({ INS := ((@ellipses.NoEllipses), («t_1*» ++ ([(@valtype.NumT «eval:3»)] : (_root_.List valtype)))), OUTS := ((@ellipses.NoEllipses), «t_2*») } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:18» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:RETURN» instr) = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.Ellipses), (context.RESULTS C_0)), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))

def «Instr_ok:clause:19» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:RETURN_CALL» instr) = true))) (fun (_ : Unit) => (match instr with | .RETURN_CALL «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.FUNCS C_0))))) (fun (_ : Unit) => (match ((context.FUNCS C_0)[x]?) with | some «exec:2» => (let «eval:0» : deftype := «exec:2»; (.bind (.call (Call.«$expanddt» «eval:0»)) (fun («exec:3» : strtype) => (let «eval:1» : strtype := «exec:3»; (.bind (.call (Call.«$functype_of_strtype» «eval:1»)) (fun («exec:4» : functype) => (let «eval:2» : functype := «exec:4»; (match «eval:2» with | .FuncT «exec:5» «exec:6» => (let «t_1*» : (_root_.List valtype) := «exec:5»; (let «t_2*» : (_root_.List valtype) := «exec:6»; (.bind (.call (Call.«$match_resulttype» (context.TYPES C_0) «t_2*» (context.RESULTS C_0))) (fun («exec:7» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:7»; (.bind (.guard ((«eval:3» = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.Ellipses), «t_1*»), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:20» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:RETURN_CALL_REF» instr) = true))) (fun (_ : Unit) => (match instr with | .RETURN_CALL_REF «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$func_type» C_0 x)) (fun («exec:2» : functype) => (let «eval:0» : functype := «exec:2»; (match «eval:0» with | .FuncT «exec:3» «exec:4» => (let «t_1*» : (_root_.List valtype) := «exec:3»; (let «t_2*» : (_root_.List valtype) := «exec:4»; (.bind (.call (Call.«$match_resulttype» (context.TYPES C_0) «t_2*» (context.RESULTS C_0))) (fun («exec:5» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:5»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:6» => (let «eval:2» : deftype := «exec:6»; (.pure (((({ INS := ((@ellipses.Ellipses), («t_1*» ++ ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:2»)))] : (_root_.List valtype)))), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:21» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:RETURN_CALL_INDIRECT» instr) = true))) (fun (_ : Unit) => (match instr with | .RETURN_CALL_INDIRECT «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:3» => (let «eval:0» : tabletype := «exec:3»; (match «eval:0» with | .TableT «exec:4» «exec:5» «exec:6» => (let «at» : addrtype := «exec:4»; (let lim : limits := «exec:5»; (let rt : reftype := «exec:6»; (.bind (.call (Call.«$func_type» C_0 y)) (fun («exec:7» : functype) => (let «eval:1» : functype := «exec:7»; (match «eval:1» with | .FuncT «exec:8» «exec:9» => (let «t_1*» : (_root_.List valtype) := «exec:8»; (let «t_2*» : (_root_.List valtype) := «exec:9»; (.bind (.call (Call.«$match_reftype» (context.TYPES C_0) rt (@reftype.«% %» (@null.Null) (@heaptype.FuncHT)))) (fun («exec:10» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:10»; (.bind (.guard ((«eval:2» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$match_resulttype» (context.TYPES C_0) «t_2*» (context.RESULTS C_0))) (fun («exec:11» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:11»; (.bind (.guard ((«eval:3» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:12» : numtype) => (let «eval:4» : numtype := «exec:12»; (.pure (((({ INS := ((@ellipses.Ellipses), («t_1*» ++ ([(@valtype.NumT «eval:4»)] : (_root_.List valtype)))), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))))))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:22» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:THROW» instr) = true))) (fun (_ : Unit) => (match instr with | .THROW «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.TAGS C_0))))) (fun (_ : Unit) => (match ((context.TAGS C_0)[x]?) with | some «exec:2» => (let «eval:0» : tagtype := «exec:2»; (match «eval:0» with | .TagT «exec:3» => (let dt : deftype := «exec:3»; (.bind (.call (Call.«$expanddt» dt)) (fun («exec:4» : strtype) => (let «eval:1» : strtype := «exec:4»; (.bind (.call (Call.«$functype_of_strtype» «eval:1»)) (fun («exec:5» : functype) => (let «eval:2» : functype := «exec:5»; (match «eval:2» with | .FuncT «exec:6» «exec:7» => (let «t_1*» : (_root_.List valtype) := «exec:6»; (let «t_2*» : (_root_.List valtype) := «exec:7»; (.pure (((({ INS := ((@ellipses.Ellipses), «t_1*»), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:23» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:THROW_REF» instr) = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.Ellipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.ExnHT)))] : (_root_.List valtype))), OUTS := ((@ellipses.Ellipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))

def «Instr_ok:clause:24» (input0 : context) (input1 : inferresulttype) (input2 : instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr' : instr := input2; (.bind (.guard (((«exec:match:instr:TRY_TABLE» instr') = true))) (fun (_ : Unit) => (match instr' with | .TRY_TABLE «exec:1» «exec:2» «exec:3» => (let blocktype : SpecTec.blocktype := «exec:1»; (let «catch*» : (_root_.List «catch») := «exec:2»; (let «instr*» : (_root_.List instr) := «exec:3»; (.bind (.call (Call.Blocktype_ok C_0 blocktype)) (fun («exec:4» : instrtype) => (match «exec:4» with | .InstrT «exec:5» «exec:6» «exec:7» => (let «t_1*» : (_root_.List valtype) := «exec:5»; (let «t_2*» : (_root_.List valtype) := «exec:6»; (let «x*» : (_root_.List idx) := «exec:7»; (let C_1 : context := ({ C_0 with LABELS := (([«t_2*»] : (_root_.List resulttype)) ++ (context.LABELS C_0)) } : context); (.bind (.call (Call.«Instr_ok:try_table:iter:0» C_0 «t_2*» «catch*»)) (fun («exec:8» : _root_.Unit) => (.bind (.call (Call.Block_ok C_1 (@instrtype.InstrT «t_1*» «t_2*» «x*») «instr*»)) (fun («exec:9» : _root_.Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), «t_1*»), OUTS := ((@ellipses.NoEllipses), «t_2*») } : inferfunctype), «x*») : inferinstrtype))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:25» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:LOCAL.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«LOCAL.GET» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.LOCALS C_0))))) (fun (_ : Unit) => (match ((context.LOCALS C_0)[x]?) with | some «exec:2» => (let «eval:0» : localtype := «exec:2»; (match «eval:0» with | .LocalT «exec:3» «exec:4» => (let init : SpecTec.init := «exec:3»; (let t : valtype := «exec:4»; (.bind (.guard (((«exec:match:init:Set» init) = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:26» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:LOCAL.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«LOCAL.SET» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.LOCALS C_0))))) (fun (_ : Unit) => (match ((context.LOCALS C_0)[x]?) with | some «exec:2» => (let «eval:0» : localtype := «exec:2»; (match «eval:0» with | .LocalT «exec:3» «exec:4» => (let init : SpecTec.init := «exec:3»; (let t : valtype := «exec:4»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([x] : (_root_.List idx))) : inferinstrtype))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:27» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:LOCAL.TEE» instr) = true))) (fun (_ : Unit) => (match instr with | .«LOCAL.TEE» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.LOCALS C_0))))) (fun (_ : Unit) => (match ((context.LOCALS C_0)[x]?) with | some «exec:2» => (let «eval:0» : localtype := «exec:2»; (match «eval:0» with | .LocalT «exec:3» «exec:4» => (let init : SpecTec.init := «exec:3»; (let t : valtype := «exec:4»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([x] : (_root_.List idx))) : inferinstrtype))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:28» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:GLOBAL.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«GLOBAL.GET» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.GLOBALS C_0))))) (fun (_ : Unit) => (match ((context.GLOBALS C_0)[x]?) with | some «exec:2» => (let «eval:0» : globaltype := «exec:2»; (match «eval:0» with | .GlobalT «exec:3» «exec:4» => (let «mut» : SpecTec.«mut» := «exec:3»; (let t : valtype := «exec:4»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:29» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:GLOBAL.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«GLOBAL.SET» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.GLOBALS C_0))))) (fun (_ : Unit) => (match ((context.GLOBALS C_0)[x]?) with | some «exec:2» => (let «eval:0» : globaltype := «exec:2»; (match «eval:0» with | .GlobalT «exec:3» «exec:4» => (let «mut» : SpecTec.«mut» := «exec:3»; (let t : valtype := «exec:4»; (.bind (.guard (((«exec:match:mut:Var» «mut») = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:30» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:TABLE.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.GET» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:2» => (let «eval:0» : tabletype := «exec:2»; (match «eval:0» with | .TableT «exec:3» «exec:4» «exec:5» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (let rt : reftype := «exec:5»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:6» : numtype) => (let «eval:1» : numtype := «exec:6»; (let t : valtype := (@valtype.NumT «eval:1»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT rt)] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:31» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:TABLE.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.SET» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:2» => (let «eval:0» : tabletype := «exec:2»; (match «eval:0» with | .TableT «exec:3» «exec:4» «exec:5» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (let rt : reftype := «exec:5»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:6» : numtype) => (let «eval:1» : numtype := «exec:6»; (let t : valtype := (@valtype.NumT «eval:1»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, (@valtype.RefT rt)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:32» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:TABLE.SIZE» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.SIZE» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:2» => (let «eval:0» : tabletype := «exec:2»; (match «eval:0» with | .TableT «exec:3» «exec:4» «exec:5» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (let rt : reftype := «exec:5»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:6» : numtype) => (let «eval:1» : numtype := «exec:6»; (let t : valtype := (@valtype.NumT «eval:1»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:33» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:TABLE.GROW» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.GROW» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:2» => (let «eval:0» : tabletype := «exec:2»; (match «eval:0» with | .TableT «exec:3» «exec:4» «exec:5» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (let rt : reftype := «exec:5»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:6» : numtype) => (let «eval:1» : numtype := «exec:6»; (let t : valtype := (@valtype.NumT «eval:1»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT rt), t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:34» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:TABLE.FILL» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.FILL» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:2» => (let «eval:0» : tabletype := «exec:2»; (match «eval:0» with | .TableT «exec:3» «exec:4» «exec:5» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (let rt : reftype := «exec:5»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:6» : numtype) => (let «eval:1» : numtype := «exec:6»; (let t : valtype := (@valtype.NumT «eval:1»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, (@valtype.RefT rt), t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:35» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:TABLE.COPY» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.COPY» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:3» => (let «eval:0» : tabletype := «exec:3»; (match «eval:0» with | .TableT «exec:4» «exec:5» «exec:6» => (let at_1 : addrtype := «exec:4»; (let lim_1 : limits := «exec:5»; (let rt_1 : reftype := «exec:6»; (.bind (.guard ((y < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[y]?) with | some «exec:7» => (let «eval:1» : tabletype := «exec:7»; (match «eval:1» with | .TableT «exec:8» «exec:9» «exec:10» => (let at_2 : addrtype := «exec:8»; (let lim_2 : limits := «exec:9»; (let rt_2 : reftype := «exec:10»; (.bind (.call (Call.«$match_reftype» (context.TYPES C_0) rt_2 rt_1)) (fun («exec:11» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:11»; (.bind (.guard ((«eval:2» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$numtype_of_addrtype» at_1)) (fun («exec:12» : numtype) => (let «eval:3» : numtype := «exec:12»; (let t_1 : valtype := (@valtype.NumT «eval:3»); (.bind (.call (Call.«$numtype_of_addrtype» at_2)) (fun («exec:13» : numtype) => (let «eval:4» : numtype := «exec:13»; (let t_2 : valtype := (@valtype.NumT «eval:4»); (.bind (.call (Call.«$min_addrtype» at_1 at_2)) (fun («exec:14» : addrtype) => (let «eval:5» : addrtype := «exec:14»; (.bind (.call (Call.«$numtype_of_addrtype» «eval:5»)) (fun («exec:15» : numtype) => (let «eval:6» : numtype := «exec:15»; (let t_min : valtype := (@valtype.NumT «eval:6»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t_1, t_2, t_min] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))))))))))))))))))) | none => .unmatch)))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:36» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:TABLE.INIT» instr) = true))) (fun (_ : Unit) => (match instr with | .«TABLE.INIT» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:3» => (let «eval:0» : tabletype := «exec:3»; (match «eval:0» with | .TableT «exec:4» «exec:5» «exec:6» => (let «at» : addrtype := «exec:4»; (let lim : limits := «exec:5»; (let rt : reftype := «exec:6»; (.bind (.guard ((y < (_root_.List.length (context.ELEMS C_0))))) (fun (_ : Unit) => (match ((context.ELEMS C_0)[y]?) with | some «exec:7» => (let «eval:1» : elemtype := «exec:7»; (let rt' : reftype := «eval:1»; (.bind (.call (Call.«$match_reftype» (context.TYPES C_0) rt' rt)) (fun («exec:8» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:8»; (.bind (.guard ((«eval:2» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:9» : numtype) => (let «eval:3» : numtype := «exec:9»; (let t : valtype := (@valtype.NumT «eval:3»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, (@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))))) | none => .unmatch)))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:37» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ELEM.DROP» instr) = true))) (fun (_ : Unit) => (match instr with | .«ELEM.DROP» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard (((x ≥ (0 : _root_.Nat)) ∧ (x < (_root_.List.length (context.ELEMS C_0)))))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))) | _ => .unmatch))))))

def «Instr_ok:clause:38» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:LOAD» instr) = true))) (fun (_ : Unit) => (match instr with | .LOAD «exec:1» «exec:2» => (let x : idx := «exec:1»; (let loadop_ : SpecTec.loadop_ := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:3» => (let «eval:0» : memtype := «exec:3»; (match «eval:0» with | .MemoryT «exec:4» «exec:5» => (let «at» : addrtype := «exec:4»; (let lim : limits := «exec:5»; (.bind (.call (Call.Loadop_ok C_0 loadop_)) (fun («exec:6» : numtype) => (let nt : numtype := «exec:6»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:7» : numtype) => (let «eval:1» : numtype := «exec:7»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:1»)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT nt)] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:39» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:STORE» instr) = true))) (fun (_ : Unit) => (match instr with | .STORE «exec:1» «exec:2» => (let x : idx := «exec:1»; (let storeop_ : SpecTec.storeop_ := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:3» => (let «eval:0» : memtype := «exec:3»; (match «eval:0» with | .MemoryT «exec:4» «exec:5» => (let «at» : addrtype := «exec:4»; (let lim : limits := «exec:5»; (.bind (.call (Call.Storeop_ok C_0 storeop_)) (fun («exec:6» : numtype) => (let nt : numtype := «exec:6»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:7» : numtype) => (let «eval:1» : numtype := «exec:7»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:1»), (@valtype.NumT nt)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:40» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.LOAD» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.LOAD» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let vloadop_ : SpecTec.vloadop_ := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:3» => (let «eval:0» : memtype := «exec:3»; (match «eval:0» with | .MemoryT «exec:4» «exec:5» => (let «at» : addrtype := «exec:4»; (let lim : limits := «exec:5»; (.bind (.call (Call.Vloadop_ok C_0 vloadop_)) (fun («exec:6» : vectype) => (let vt : vectype := «exec:6»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:7» : numtype) => (let «eval:1» : numtype := «exec:7»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:1»)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.VecT vt)] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:41» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.STORE» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.STORE» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let vstoreop_ : SpecTec.vstoreop_ := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:3» => (let «eval:0» : memtype := «exec:3»; (match «eval:0» with | .MemoryT «exec:4» «exec:5» => (let «at» : addrtype := «exec:4»; (let lim : limits := «exec:5»; (.bind (.call (Call.Vstoreop_ok C_0 vstoreop_)) (fun («exec:6» : vectype) => (let vt : vectype := «exec:6»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:7» : numtype) => (let «eval:1» : numtype := «exec:7»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:1»), (@valtype.VecT vt)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:42» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.LOAD_LANE» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.LOAD_LANE» «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let vlaneop_ : SpecTec.vlaneop_ := «exec:2»; (let int_1 : _root_.Int := «exec:3»; (let _vt : vectype := (vlaneop_).TYPE; (let _u32 : u32 := (vlaneop_).ALIGN; (let _u64 : u64 := (vlaneop_).OFFSET; (let packtype : SpecTec.packtype := (vlaneop_).PACK; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:4» => (let «eval:0» : memtype := «exec:4»; (match «eval:0» with | .MemoryT «exec:5» «exec:6» => (let «at» : addrtype := «exec:5»; (let lim : limits := «exec:6»; (.bind (.call (Call.Vlaneop_ok C_0 vlaneop_)) (fun («exec:7» : vectype) => (let vt : vectype := «exec:7»; (.bind (.call (Call.«$vec_size» vt)) (fun («exec:8» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:8»; (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:9» : _root_.Int) => (let «eval:2» : _root_.Int := «exec:9»; (.bind (ExecutablePlan.require ((«eval:2» ≠ (0 : _root_.Int))) "division by zero") (fun (_ : Unit) => (.bind (.guard ((int_1 < (_root_.Int.tdiv «eval:1» «eval:2»)))) (fun (_ : Unit) => (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:10» : numtype) => (let «eval:3» : numtype := «exec:10»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:3»), (@valtype.VecT vt)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.VecT vt)] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))))))))))))) | none => .unmatch)))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:43» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.STORE_LANE» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.STORE_LANE» «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let vlaneop_ : SpecTec.vlaneop_ := «exec:2»; (let int_1 : _root_.Int := «exec:3»; (let _vt : vectype := (vlaneop_).TYPE; (let _u32 : u32 := (vlaneop_).ALIGN; (let _u64 : u64 := (vlaneop_).OFFSET; (let packtype : SpecTec.packtype := (vlaneop_).PACK; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:4» => (let «eval:0» : memtype := «exec:4»; (match «eval:0» with | .MemoryT «exec:5» «exec:6» => (let «at» : addrtype := «exec:5»; (let lim : limits := «exec:6»; (.bind (.call (Call.Vlaneop_ok C_0 vlaneop_)) (fun («exec:7» : vectype) => (let vt : vectype := «exec:7»; (.bind (.call (Call.«$vec_size» vt)) (fun («exec:8» : _root_.Int) => (let «eval:1» : _root_.Int := «exec:8»; (.bind (.call (Call.«$pack_size» packtype)) (fun («exec:9» : _root_.Int) => (let «eval:2» : _root_.Int := «exec:9»; (.bind (ExecutablePlan.require ((«eval:2» ≠ (0 : _root_.Int))) "division by zero") (fun (_ : Unit) => (.bind (.guard ((int_1 < (_root_.Int.tdiv «eval:1» «eval:2»)))) (fun (_ : Unit) => (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:10» : numtype) => (let «eval:3» : numtype := «exec:10»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:3»), (@valtype.VecT vt)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))))))))))))) | none => .unmatch)))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:44» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:MEMORY.SIZE» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.SIZE» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:2» => (let «eval:0» : memtype := «exec:2»; (match «eval:0» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:5» : numtype) => (let «eval:1» : numtype := «exec:5»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:1»)] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:45» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:MEMORY.GROW» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.GROW» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:2» => (let «eval:0» : memtype := «exec:2»; (match «eval:0» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:5» : numtype) => (let «eval:1» : numtype := «exec:5»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:6» : numtype) => (let «eval:2» : numtype := «exec:6»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:1»)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT «eval:2»)] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:46» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:MEMORY.FILL» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.FILL» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:2» => (let «eval:0» : memtype := «exec:2»; (match «eval:0» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:5» : numtype) => (let «eval:1» : numtype := «exec:5»; (let t : valtype := (@valtype.NumT «eval:1»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, (@valtype.NumT (@numtype.I32T)), t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:47» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:MEMORY.COPY» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.COPY» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:3» => (let «eval:0» : memtype := «exec:3»; (match «eval:0» with | .MemoryT «exec:4» «exec:5» => (let at_1 : addrtype := «exec:4»; (let lim_1 : limits := «exec:5»; (.bind (.guard ((y < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[y]?) with | some «exec:6» => (let «eval:1» : memtype := «exec:6»; (match «eval:1» with | .MemoryT «exec:7» «exec:8» => (let at_2 : addrtype := «exec:7»; (let lim_2 : limits := «exec:8»; (.bind (.call (Call.«$numtype_of_addrtype» at_1)) (fun («exec:9» : numtype) => (let «eval:2» : numtype := «exec:9»; (let t_1 : valtype := (@valtype.NumT «eval:2»); (.bind (.call (Call.«$numtype_of_addrtype» at_2)) (fun («exec:10» : numtype) => (let «eval:3» : numtype := «exec:10»; (let t_2 : valtype := (@valtype.NumT «eval:3»); (.bind (.call (Call.«$min_addrtype» at_1 at_2)) (fun («exec:11» : addrtype) => (let «eval:4» : addrtype := «exec:11»; (.bind (.call (Call.«$numtype_of_addrtype» «eval:4»)) (fun («exec:12» : numtype) => (let «eval:5» : numtype := «exec:12»; (let t_min : valtype := (@valtype.NumT «eval:5»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t_1, t_2, t_min] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))))))))))))) | none => .unmatch))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:48» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:MEMORY.INIT» instr) = true))) (fun (_ : Unit) => (match instr with | .«MEMORY.INIT» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:3» => (let «eval:0» : memtype := «exec:3»; (match «eval:0» with | .MemoryT «exec:4» «exec:5» => (let «at» : addrtype := «exec:4»; (let lim : limits := «exec:5»; (.bind (.guard (((y ≥ (0 : _root_.Nat)) ∧ (y < (_root_.List.length (context.DATAS C_0)))))) (fun (_ : Unit) => (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:6» : numtype) => (let «eval:1» : numtype := «exec:6»; (let t : valtype := (@valtype.NumT «eval:1»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, (@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:49» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:DATA.DROP» instr) = true))) (fun (_ : Unit) => (match instr with | .«DATA.DROP» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard (((x ≥ (0 : _root_.Nat)) ∧ (x < (_root_.List.length (context.DATAS C_0)))))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))) | _ => .unmatch))))))

def «Instr_ok:clause:50» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:REF.NULL» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.NULL» «exec:1» => (let ht : heaptype := «exec:1»; (.bind (.call (Call.Heaptype_ok C_0 ht)) (fun («exec:2» : _root_.Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) ht))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))) | _ => .unmatch))))))

def «Instr_ok:clause:51» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:REF.FUNC» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.FUNC» «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.FUNCS C_0))))) (fun (_ : Unit) => (match ((context.FUNCS C_0)[x]?) with | some «exec:2» => (let «eval:0» : deftype := «exec:2»; (let dt : deftype := «eval:0»; (.bind (.call (Call.«$in_set» funcidx x (free.FUNCS (context.REFS C_0)))) (fun («exec:3» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.DefHT dt)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))) | none => .unmatch)))) | _ => .unmatch))))))

def «Instr_ok:clause:52» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:REF.IS_NULL» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$peek_ref» (0 : _root_.Nat) irt)) (fun («exec:1» : reftype) => (let «eval:0» : reftype := «exec:1»; (match «eval:0» with | .«% %» «exec:2» «exec:3» => (let null : SpecTec.null := «exec:2»; (let ht : heaptype := «exec:3»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@SpecTec.null.Null) ht))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))))

def «Instr_ok:clause:53» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:REF.AS_NON_NULL» instr) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$peek_ref» (0 : _root_.Nat) irt)) (fun («exec:1» : reftype) => (let «eval:0» : reftype := «exec:1»; (match «eval:0» with | .«% %» «exec:2» «exec:3» => (let null : SpecTec.null := «exec:2»; (let ht : heaptype := «exec:3»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@SpecTec.null.Null) ht))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@SpecTec.null.NoNull) ht))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))))

def «Instr_ok:clause:54» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:REF.TEST» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.TEST» «exec:1» => (let rt : reftype := «exec:1»; (match rt with | .«% %» «exec:2» «exec:3» => (let null : SpecTec.null := «exec:2»; (let ht : heaptype := «exec:3»; (.bind (.call (Call.Reftype_ok C_0 rt)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.«$top_of_heap_type» (context.TYPES C_0) ht)) (fun («exec:5» : heaptype) => (let «eval:0» : heaptype := «exec:5»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@SpecTec.null.Null) «eval:0»))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:55» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:REF.CAST» instr) = true))) (fun (_ : Unit) => (match instr with | .«REF.CAST» «exec:1» => (let rt : reftype := «exec:1»; (match rt with | .«% %» «exec:2» «exec:3» => (let null : SpecTec.null := «exec:2»; (let ht : heaptype := «exec:3»; (.bind (.call (Call.Reftype_ok C_0 rt)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.«$top_of_heap_type» (context.TYPES C_0) ht)) (fun («exec:5» : heaptype) => (let «eval:0» : heaptype := «exec:5»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@SpecTec.null.Null) «eval:0»))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» null ht))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:56» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:REF.EQ» instr) = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.EqHT))), (@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.EqHT)))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))

def «Instr_ok:clause:57» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:REF.I31» instr) = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.I31HT)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))

def «Instr_ok:clause:58» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:I31.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«I31.GET» «exec:1» => (let extension : SpecTec.extension := «exec:1»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.I31HT)))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | _ => .unmatch))))))

def «Instr_ok:clause:59» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:STRUCT.NEW» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.NEW» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let iop : initop_ := «exec:2»; (.bind (.guard (((«exec:match:initop_:Explicit» iop) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$struct_type» C_0 x)) (fun («exec:3» : structtype) => (let «eval:0» : structtype := «exec:3»; (match «eval:0» with | .StructT «exec:4» => (let «yt*» : (_root_.List fieldtype) := «exec:4»; (.bind (.call (Call.«Instr_ok:struct.new.explicit:iter:1» «yt*»)) (fun («exec:5» : (_root_.List valtype)) => (let «t*» : (_root_.List valtype) := «exec:5»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:6» => (let «eval:3» : deftype := «exec:6»; (.pure (((({ INS := ((@ellipses.NoEllipses), «t*»), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.DefHT «eval:3»)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:60» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:STRUCT.NEW» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.NEW» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let iop : initop_ := «exec:2»; (.bind (.guard (((«exec:match:initop_:Implicit» iop) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$struct_type» C_0 x)) (fun («exec:3» : structtype) => (let «eval:0» : structtype := «exec:3»; (match «eval:0» with | .StructT «exec:4» => (let «yt*» : (_root_.List fieldtype) := «exec:4»; (.bind (.call (Call.«Instr_ok:struct.new.implicit:iter:1» «yt*»)) (fun («exec:5» : _root_.Unit) => (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:6» => (let «eval:4» : deftype := «exec:6»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.DefHT «eval:4»)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:61» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:STRUCT.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.GET» «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (let extension'? : (_root_.Option SpecTec.extension) := «exec:3»; (.bind (.guard (((_root_.Option.isSome extension'?) = true))) (fun (_ : Unit) => (match extension'? with | some «exec:4» => (let extension : SpecTec.extension := «exec:4»; (.bind (.call (Call.«$struct_type» C_0 x)) (fun («exec:5» : structtype) => (let «eval:0» : structtype := «exec:5»; (match «eval:0» with | .StructT «exec:6» => (let «yt*» : (_root_.List fieldtype) := «exec:6»; (.bind (.guard ((y < (_root_.List.length «yt*»)))) (fun (_ : Unit) => (.bind (.guard ((y < (_root_.List.length «yt*»)))) (fun (_ : Unit) => (match («yt*»[y]?) with | some «exec:7» => (let «eval:1» : fieldtype := «exec:7»; (match «eval:1» with | .FieldT «exec:8» «exec:9» => (let «mut» : SpecTec.«mut» := «exec:8»; (let zt : storagetype := «exec:9»; (.bind (.call (Call.«$is_packed_storage_type» zt)) (fun («exec:10» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:10»; (.bind (.guard ((«eval:2» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:11» : valtype) => (let «eval:3» : valtype := «exec:11»; (let t : valtype := «eval:3»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:12» => (let «eval:4» : deftype := «exec:12»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:4»)))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))))))))) | none => .unmatch))))))))))) | none => .unmatch)))))) | _ => .unmatch))))))

def «Instr_ok:clause:62» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:STRUCT.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.GET» «exec:1» «exec:2» «exec:3» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (let extension? : (_root_.Option extension) := «exec:3»; (.bind (.guard (((_root_.Option.isNone extension?) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$struct_type» C_0 x)) (fun («exec:4» : structtype) => (let «eval:0» : structtype := «exec:4»; (match «eval:0» with | .StructT «exec:5» => (let «yt*» : (_root_.List fieldtype) := «exec:5»; (.bind (.guard ((y < (_root_.List.length «yt*»)))) (fun (_ : Unit) => (.bind (.guard ((y < (_root_.List.length «yt*»)))) (fun (_ : Unit) => (match («yt*»[y]?) with | some «exec:6» => (let «eval:1» : fieldtype := «exec:6»; (match «eval:1» with | .FieldT «exec:7» «exec:8» => (let «mut» : SpecTec.«mut» := «exec:7»; (let zt : storagetype := «exec:8»; (.bind (.call (Call.«$is_packed_storage_type» zt)) (fun («exec:9» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:9»; (.bind (.guard ((¬ («eval:2» = true)))) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:10» : valtype) => (let «eval:3» : valtype := «exec:10»; (let t : valtype := «eval:3»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:11» => (let «eval:4» : deftype := «exec:11»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:4»)))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))))))))) | none => .unmatch))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:63» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:STRUCT.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«STRUCT.SET» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$struct_type» C_0 x)) (fun («exec:3» : structtype) => (let «eval:0» : structtype := «exec:3»; (match «eval:0» with | .StructT «exec:4» => (let «yt*» : (_root_.List fieldtype) := «exec:4»; (.bind (.guard ((y < (_root_.List.length «yt*»)))) (fun (_ : Unit) => (.bind (.guard ((y < (_root_.List.length «yt*»)))) (fun (_ : Unit) => (match («yt*»[y]?) with | some «exec:5» => (let «eval:1» : fieldtype := «exec:5»; (match «eval:1» with | .FieldT «exec:6» «exec:7» => (let «mut» : SpecTec.«mut» := «exec:6»; (let zt : storagetype := «exec:7»; (.bind (.guard ((@SpecTec.«mut».Var) = «mut»)) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:8» : valtype) => (let «eval:2» : valtype := «exec:8»; (let t : valtype := «eval:2»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:9» => (let «eval:3» : deftype := «exec:9»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:3»))), t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))) | none => .unmatch)))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:64» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.NEW» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let iop : initop_ := «exec:2»; (.bind (.guard (((«exec:match:initop_:Explicit» iop) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (let yt : fieldtype := «exec:4»; (.bind (.call (Call.«$unpacked_field_type» yt)) (fun («exec:5» : valtype) => (let «eval:1» : valtype := «exec:5»; (let t : valtype := «eval:1»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:6» => (let «eval:2» : deftype := «exec:6»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.DefHT «eval:2»)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:65» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.NEW» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let iop : initop_ := «exec:2»; (.bind (.guard (((«exec:match:initop_:Implicit» iop) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (let yt : fieldtype := «exec:4»; (.bind (.call (Call.«$unpacked_field_type» yt)) (fun («exec:5» : valtype) => (let «eval:1» : valtype := «exec:5»; (.bind (.call (Call.«$defaultable» «eval:1»)) (fun («exec:6» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:6»; (.bind (.guard ((«eval:2» = true))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:7» => (let «eval:3» : deftype := «exec:7»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.DefHT «eval:3»)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:66» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.NEW_FIXED» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW_FIXED» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let n : SpecTec.n := «exec:2»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (let yt : fieldtype := «exec:4»; (.bind (.call (Call.«$unpacked_field_type» yt)) (fun («exec:5» : valtype) => (let «eval:1» : valtype := «exec:5»; (.bind (.call (Call.«$make_» valtype «eval:1» n)) (fun («exec:6» : (_root_.List valtype)) => (let «eval:2» : (_root_.List valtype) := «exec:6»; (let «t*» : (_root_.List valtype) := «eval:2»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:7» => (let «eval:3» : deftype := «exec:7»; (.pure (((({ INS := ((@ellipses.NoEllipses), «t*»), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.DefHT «eval:3»)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:67» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.NEW_ELEM» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW_ELEM» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (let yt : fieldtype := «exec:4»; (.bind (.guard ((y < (_root_.List.length (context.ELEMS C_0))))) (fun (_ : Unit) => (match ((context.ELEMS C_0)[y]?) with | some «exec:5» => (let «eval:1» : elemtype := «exec:5»; (let rt : reftype := «eval:1»; (.bind (.call (Call.«$unpacked_field_type» yt)) (fun («exec:6» : valtype) => (let «eval:2» : valtype := «exec:6»; (.bind (.call (Call.«$match_valtype» (context.TYPES C_0) (@valtype.RefT rt) «eval:2»)) (fun («exec:7» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:7»; (.bind (.guard ((«eval:3» = true))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:8» => (let «eval:4» : deftype := «exec:8»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.DefHT «eval:4»)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))) | none => .unmatch)))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:68» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.NEW_DATA» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.NEW_DATA» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (let yt : fieldtype := «exec:4»; (.bind (.guard ((y < (_root_.List.length (context.DATAS C_0))))) (fun (_ : Unit) => (match ((context.DATAS C_0)[y]?) with | some «exec:5» => (let «eval:1» : datatype := «exec:5»; (.bind (.guard ((@datatype.OK) = «eval:1»)) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_field_type» yt)) (fun («exec:6» : valtype) => (let «eval:2» : valtype := «exec:6»; (let t : valtype := «eval:2»; (.bind (.call (Call.«$is_num_type» t)) (fun («exec:7» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:7»; (.bind (.call (Call.«$is_vec_type» t)) (fun («exec:8» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:8»; (.bind (.guard (((«eval:3» = true) ∨ («eval:4» = true)))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:9» => (let «eval:5» : deftype := «exec:9»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.NoNull) (@heaptype.DefHT «eval:5»)))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))))))))))) | none => .unmatch)))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:69» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.GET» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let extension'? : (_root_.Option SpecTec.extension) := «exec:2»; (.bind (.guard (((_root_.Option.isSome extension'?) = true))) (fun (_ : Unit) => (match extension'? with | some «exec:3» => (let extension : SpecTec.extension := «exec:3»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:4» : arraytype) => (let «eval:0» : arraytype := «exec:4»; (match «eval:0» with | .ArrayT «exec:5» => (match «exec:5» with | .FieldT «exec:6» «exec:7» => (let «mut» : SpecTec.«mut» := «exec:6»; (let zt : storagetype := «exec:7»; (.bind (.call (Call.«$is_packed_storage_type» zt)) (fun («exec:8» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:8»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:9» : valtype) => (let «eval:2» : valtype := «exec:9»; (let t : valtype := «eval:2»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:10» => (let «eval:3» : deftype := «exec:10»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:3»))), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Instr_ok:clause:70» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.GET» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.GET» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let extension? : (_root_.Option extension) := «exec:2»; (.bind (.guard (((_root_.Option.isNone extension?) = true))) (fun (_ : Unit) => (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (match «exec:4» with | .FieldT «exec:5» «exec:6» => (let «mut» : SpecTec.«mut» := «exec:5»; (let zt : storagetype := «exec:6»; (.bind (.call (Call.«$is_packed_storage_type» zt)) (fun («exec:7» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:7»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:8» : valtype) => (let «eval:2» : valtype := «exec:8»; (let t : valtype := «eval:2»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:9» => (let «eval:3» : deftype := «exec:9»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:3»))), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:71» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.SET» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.SET» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:2» : arraytype) => (let «eval:0» : arraytype := «exec:2»; (match «eval:0» with | .ArrayT «exec:3» => (match «exec:3» with | .FieldT «exec:4» «exec:5» => (let «mut» : SpecTec.«mut» := «exec:4»; (let zt : storagetype := «exec:5»; (.bind (.guard (((«exec:match:mut:Var» «mut») = true))) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:6» : valtype) => (let «eval:1» : valtype := «exec:6»; (let t : valtype := «eval:1»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:7» => (let «eval:2» : deftype := «exec:7»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:2»))), (@valtype.NumT (@numtype.I32T)), t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:72» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.LEN» instr) = true))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.ArrayHT)))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))

def «Instr_ok:clause:73» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.COPY» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.COPY» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (match «exec:4» with | .FieldT «exec:5» «exec:6» => (let mut_1 : «mut» := «exec:5»; (let zt_1 : storagetype := «exec:6»; (.bind (.call (Call.«$array_type» C_0 y)) (fun («exec:7» : arraytype) => (let «eval:1» : arraytype := «exec:7»; (match «eval:1» with | .ArrayT «exec:8» => (match «exec:8» with | .FieldT «exec:9» «exec:10» => (let mut_2 : «mut» := «exec:9»; (let zt_2 : storagetype := «exec:10»; (.bind (.guard ((@«mut».Var) = mut_1)) (fun (_ : Unit) => (.bind (.call (Call.«$match_storagetype» (context.TYPES C_0) zt_2 zt_1)) (fun («exec:11» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:11»; (.bind (.guard ((«eval:2» = true))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (.bind (.guard ((y < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:12» => (let «eval:3» : deftype := «exec:12»; (match ((context.TYPES C_0)[y]?) with | some «exec:13» => (let «eval:4» : deftype := «exec:13»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:3»))), (@valtype.NumT (@numtype.I32T)), (@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:4»))), (@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)) | none => .unmatch)))))))))))))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:74» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.FILL» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.FILL» «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:2» : arraytype) => (let «eval:0» : arraytype := «exec:2»; (match «eval:0» with | .ArrayT «exec:3» => (match «exec:3» with | .FieldT «exec:4» «exec:5» => (let «mut» : SpecTec.«mut» := «exec:4»; (let zt : storagetype := «exec:5»; (.bind (.guard ((@SpecTec.«mut».Var) = «mut»)) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:6» : valtype) => (let «eval:1» : valtype := «exec:6»; (let t : valtype := «eval:1»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:7» => (let «eval:2» : deftype := «exec:7»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:2»))), (@valtype.NumT (@numtype.I32T)), t, (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:75» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.INIT_DATA» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.INIT_DATA» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (match «exec:4» with | .FieldT «exec:5» «exec:6» => (let «mut» : SpecTec.«mut» := «exec:5»; (let zt : storagetype := «exec:6»; (.bind (.guard ((@SpecTec.«mut».Var) = «mut»)) (fun (_ : Unit) => (.bind (.guard ((y < (_root_.List.length (context.DATAS C_0))))) (fun (_ : Unit) => (match ((context.DATAS C_0)[y]?) with | some «exec:7» => (let «eval:1» : datatype := «exec:7»; (.bind (.guard ((@datatype.OK) = «eval:1»)) (fun (_ : Unit) => (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:8» : valtype) => (let «eval:2» : valtype := «exec:8»; (let t : valtype := «eval:2»; (.bind (.call (Call.«$is_num_type» t)) (fun («exec:9» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:9»; (.bind (.call (Call.«$is_vec_type» t)) (fun («exec:10» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:10»; (.bind (.guard (((«eval:3» = true) ∨ («eval:4» = true)))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:11» => (let «eval:5» : deftype := «exec:11»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:5»))), (@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch)))))))))))))))))) | none => .unmatch)))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:76» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:ARRAY.INIT_ELEM» instr) = true))) (fun (_ : Unit) => (match instr with | .«ARRAY.INIT_ELEM» «exec:1» «exec:2» => (let x : idx := «exec:1»; (let y : idx := «exec:2»; (.bind (.call (Call.«$array_type» C_0 x)) (fun («exec:3» : arraytype) => (let «eval:0» : arraytype := «exec:3»; (match «eval:0» with | .ArrayT «exec:4» => (match «exec:4» with | .FieldT «exec:5» «exec:6» => (let «mut» : SpecTec.«mut» := «exec:5»; (let zt : storagetype := «exec:6»; (.bind (.guard ((@SpecTec.«mut».Var) = «mut»)) (fun (_ : Unit) => (.bind (.guard ((y < (_root_.List.length (context.ELEMS C_0))))) (fun (_ : Unit) => (match ((context.ELEMS C_0)[y]?) with | some «exec:7» => (let «eval:1» : elemtype := «exec:7»; (let rt : reftype := «eval:1»; (.bind (.call (Call.«$unpacked_storage_type» zt)) (fun («exec:8» : valtype) => (let «eval:2» : valtype := «exec:8»; (.bind (.call (Call.«$match_valtype» (context.TYPES C_0) (@valtype.RefT rt) «eval:2»)) (fun («exec:9» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:9»; (.bind (.guard ((«eval:3» = true))) (fun (_ : Unit) => (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:10» => (let «eval:4» : deftype := «exec:10»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» (@null.Null) (@heaptype.DefHT «eval:4»))), (@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T)), (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))) | none => .unmatch))))))))))))) | none => .unmatch)))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:77» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:EXTERN.CONVERT» instr) = true))) (fun (_ : Unit) => (match instr with | .«EXTERN.CONVERT» «exec:1» => (let eop : externop_ := «exec:1»; (.bind (.call (Call.«$type_externop» eop)) (fun («exec:2» : (heaptype × heaptype)) => (let «eval:0» : (heaptype × heaptype) := «exec:2»; (let ht_1 : heaptype := («eval:0»).1; (let ht_2 : heaptype := («eval:0»).2; (.bind (.call (Call.«$peek_ref» (0 : _root_.Nat) irt)) (fun («exec:3» : reftype) => (let «eval:1» : reftype := «exec:3»; (match «eval:1» with | .«% %» «exec:4» «exec:5» => (let null : SpecTec.null := «exec:4»; (let ht : heaptype := «exec:5»; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» null ht_1))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.RefT (@reftype.«% %» null ht_2))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:78» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:CONST» instr) = true))) (fun (_ : Unit) => (match instr with | .CONST «exec:1» => (let num : num_ := «exec:1»; (.bind (.call (Call.«$type_num» i32 i64 f32 f64 num)) (fun («exec:2» : numtype) => (let «eval:0» : numtype := «exec:2»; (let t : valtype := (@valtype.NumT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:79» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:TEST» instr) = true))) (fun (_ : Unit) => (match instr with | .TEST «exec:1» => (let top : testop_ := «exec:1»; (.bind (.call (Call.«$type_num» itestop itestop ftestop ftestop top)) (fun («exec:2» : numtype) => (let «eval:0» : numtype := «exec:2»; (let t : valtype := (@valtype.NumT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:80» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:COMPARE» instr) = true))) (fun (_ : Unit) => (match instr with | .COMPARE «exec:1» => (let rop : relop_ := «exec:1»; (.bind (.call (Call.«$type_num» irelop irelop frelop frelop rop)) (fun («exec:2» : numtype) => (let «eval:0» : numtype := «exec:2»; (let t : valtype := (@valtype.NumT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:81» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:UNARY» instr) = true))) (fun (_ : Unit) => (match instr with | .UNARY «exec:1» => (let uop : unop_ := «exec:1»; (.bind (.call (Call.Unop_ok uop)) (fun («exec:2» : _root_.Unit) => (.bind (.call (Call.«$type_num» iunop iunop funop funop uop)) (fun («exec:3» : numtype) => (let «eval:0» : numtype := «exec:3»; (let t : valtype := (@valtype.NumT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:82» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:BINOP» instr) = true))) (fun (_ : Unit) => (match instr with | .BINOP «exec:1» => (let bop : binop_ := «exec:1»; (.bind (.call (Call.«$type_num» ibinop ibinop fbinop fbinop bop)) (fun («exec:2» : numtype) => (let «eval:0» : numtype := «exec:2»; (let t : valtype := (@valtype.NumT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:83» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:CONVERT» instr) = true))) (fun (_ : Unit) => (match instr with | .CONVERT «exec:1» => (let cop : cvtop_ := «exec:1»; (.bind (.call (Call.«$type_cvtop» cop)) (fun («exec:2» : (numtype × numtype)) => (let «eval:0» : (numtype × numtype) := «exec:2»; (let nt_1 : numtype := («eval:0»).1; (let nt_2 : numtype := («eval:0»).2; (.pure (((({ INS := ((@ellipses.NoEllipses), ([(@valtype.NumT nt_1)] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT nt_2)] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:84» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.CONST» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.CONST» «exec:1» => (let vec : vec_ := «exec:1»; (.bind (.call (Call.«$type_vecop» v128 vec)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:85» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.TEST» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.TEST» «exec:1» => (let vtop : vtestop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vtestop vtop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:86» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.UNARY» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.UNARY» «exec:1» => (let vuop : vunop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vunop vuop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:87» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.BINARY» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.BINARY» «exec:1» => (let vbop : vbinop_ := «exec:1»; (.bind (.call (Call.Vecbinop_ok vbop)) (fun («exec:2» : _root_.Unit) => (.bind (.call (Call.«$type_vecop» vbinop vbop)) (fun («exec:3» : vectype) => (let «eval:0» : vectype := «exec:3»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:88» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.TERNARY» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.TERNARY» «exec:1» => (let vterop : vternop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vternop vterop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, t, t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:89» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.COMPARE» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.COMPARE» «exec:1» => (let vrop : vrelop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vrelop vrop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:90» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.CONVERT» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.CONVERT» «exec:1» => (let vcvop : vcvtop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vcvtop vcvop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:91» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.SHIFT» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.SHIFT» «exec:1» => (let vshop : vshiftop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vshiftop vshop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, (@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:92» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.BITMASK» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.BITMASK» «exec:1» => (let vbitop : vbitmaskop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vbitmaskop vbitop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:93» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.TESTBITS» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.TESTBITS» «exec:1» => (let vvtop : vvtestop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vvtestop vvtop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([(@valtype.NumT (@numtype.I32T))] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:94» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.UNARYBITS» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.UNARYBITS» «exec:1» => (let vvuop : vvunop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vvunop vvuop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:95» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.BINARYBITS» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.BINARYBITS» «exec:1» => (let vvbop : vvbinop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vvbinop vvbop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:96» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.TERNARYBITS» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.TERNARYBITS» «exec:1» => (let vvterop : vvternop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vvternop vvterop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t : valtype := (@valtype.VecT «eval:0»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t, t, t] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))) | _ => .unmatch))))))

def «Instr_ok:clause:97» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.SPLAT» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.SPLAT» «exec:1» => (let vspop : vsplatop_ := «exec:1»; (.bind (.call (Call.«$type_vec_lane» vnsplatop vnsplatop vnsplatop vnsplatop vnsplatop vnsplatop vspop)) (fun («exec:2» : numtype) => (let «eval:0» : numtype := «exec:2»; (let t_1 : valtype := (@valtype.NumT «eval:0»); (.bind (.call (Call.«$type_vecop» vsplatop vspop)) (fun («exec:3» : vectype) => (let «eval:1» : vectype := «exec:3»; (let t_2 : valtype := (@valtype.VecT «eval:1»); (.pure (((({ INS := ((@ellipses.NoEllipses), ([t_1] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t_2] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:98» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.EXTRACT» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.EXTRACT» «exec:1» => (let vexop : vextractop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vextractop vexop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t_1 : valtype := (@valtype.VecT «eval:0»); (.bind (.call (Call.«$type_vec_lane» (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void) vexop)) (fun («exec:3» : numtype) => (let «eval:1» : numtype := «exec:3»; (let t_2 : valtype := (@valtype.NumT «eval:1»); (.bind (.call (Call.«$lane_extractop» vexop)) (fun («exec:4» : _root_.Int) => (let «eval:2» : _root_.Int := «exec:4»; (.bind (.call (Call.«$num_lanes» (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void) vexop)) (fun («exec:5» : _root_.Int) => (let «eval:3» : _root_.Int := «exec:5»; (.bind (.guard ((«eval:2» < «eval:3»))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([t_1] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t_2] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))))))))))) | _ => .unmatch))))))

def «Instr_ok:clause:99» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) : ExecutablePlan Call inferinstrtype :=
  (let C_0 : context := input0; (let irt : inferresulttype := input1; (let instr : SpecTec.instr := input2; (.bind (.guard (((«exec:match:instr:VEC.REPLACE» instr) = true))) (fun (_ : Unit) => (match instr with | .«VEC.REPLACE» «exec:1» => (let vrepop : vreplaceop_ := «exec:1»; (.bind (.call (Call.«$type_vecop» vreplaceop vrepop)) (fun («exec:2» : vectype) => (let «eval:0» : vectype := «exec:2»; (let t_1 : valtype := (@valtype.VecT «eval:0»); (.bind (.call (Call.«$type_vec_lane» vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vrepop)) (fun («exec:3» : numtype) => (let «eval:1» : numtype := «exec:3»; (let t_2 : valtype := (@valtype.NumT «eval:1»); (.bind (.call (Call.«$lane_replaceop» vrepop)) (fun («exec:4» : _root_.Int) => (let «eval:2» : _root_.Int := «exec:4»; (.bind (.call (Call.«$num_lanes» vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vrepop)) (fun («exec:5» : _root_.Int) => (let «eval:3» : _root_.Int := «exec:5»; (.bind (.guard ((«eval:2» < «eval:3»))) (fun (_ : Unit) => (.pure (((({ INS := ((@ellipses.NoEllipses), ([t_1, t_2] : (_root_.List valtype))), OUTS := ((@ellipses.NoEllipses), ([t_1] : (_root_.List valtype))) } : inferfunctype), ([] : (_root_.List localidx))) : inferinstrtype)))))))))))))))))))) | _ => .unmatch))))))

def Instr_ok_clauses (input0 : context) (input1 : inferresulttype) (input2 : instr) : List (ExecutablePlan.Clause Call _root_.Unit inferinstrtype) :=
  [fun (_ : _root_.Unit) => («Instr_ok:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:4»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:5»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:6»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:7»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:8»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:9»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:10»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:11»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:12»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:13»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:14»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:15»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:16»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:17»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:18»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:19»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:20»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:21»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:22»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:23»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:24»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:25»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:26»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:27»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:28»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:29»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:30»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:31»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:32»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:33»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:34»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:35»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:36»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:37»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:38»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:39»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:40»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:41»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:42»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:43»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:44»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:45»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:46»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:47»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:48»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:49»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:50»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:51»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:52»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:53»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:54»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:55»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:56»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:57»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:58»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:59»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:60»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:61»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:62»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:63»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:64»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:65»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:66»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:67»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:68»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:69»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:70»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:71»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:72»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:73»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:74»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:75»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:76»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:77»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:78»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:79»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:80»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:81»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:82»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:83»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:84»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:85»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:86»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:87»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:88»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:89»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:90»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:91»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:92»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:93»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:94»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:95»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:96»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:97»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:98»  input0 input1 input2), fun (_ : _root_.Unit) => («Instr_ok:clause:99»  input0 input1 input2)]

def «Block_ok:clause:0» (input0 : context) (input1 : instrtype) (input2 : const) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (match input1 with | .InstrT «exec:1» «exec:2» «exec:3» => (let «t_1*» : (_root_.List valtype) := «exec:1»; (let «t_2*» : (_root_.List valtype) := «exec:2»; (let «x*» : (_root_.List idx) := «exec:3»; (let «instr*» : (_root_.List instr) := input2; (.bind (.call (Call.«$stack» «t_1*»)) (fun («exec:4» : (SpecTec.ellipses × resulttype)) => (let «eval:0» : (SpecTec.ellipses × resulttype) := «exec:4»; (.bind (.call (Call.Instrs_ok C_0 «eval:0» «instr*»)) (fun («exec:5» : (inferresulttype × (_root_.List idx))) => (let irt : inferresulttype := («exec:5»).1; (let «x'*» : (_root_.List idx) := («exec:5»).2; (.bind (.call (Call.«$stack» «t_2*»)) (fun («exec:6» : (SpecTec.ellipses × resulttype)) => (let «eval:1» : (SpecTec.ellipses × resulttype) := «exec:6»; (.bind (.call (Call.«$pop» C_0 «eval:1» irt)) (fun («exec:7» : (SpecTec.ellipses × resulttype)) => (let «eval:2» : (SpecTec.ellipses × resulttype) := «exec:7»; (let ellipses : SpecTec.ellipses := («eval:2»).1; (let «t'*» : (_root_.List valtype) := («eval:2»).2; (.bind (.guard (([] : (_root_.List valtype)) = «t'*»)) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))))))))))))))))

def Block_ok_clauses (input0 : context) (input1 : instrtype) (input2 : const) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Block_ok:clause:0»  input0 input1 input2)]

def «Type_ok:clause:0» (input0 : context) (input1 : SpecTec.type) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let type : SpecTec.type := input1; (.bind (.call (Call.Rectype_ok C_0 type)) (fun («exec:1» : context) => (let C_1 : context := «exec:1»; (.pure ((C_1 : context))))))))

def Type_ok_clauses (input0 : context) (input1 : type) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Type_ok:clause:0»  input0 input1)]

def «Types_ok:clause:0» (input0 : context) (input1 : (_root_.List type)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «ty*» : (_root_.List type) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ty*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ty*» with | «exec:2» :: «exec:1» => (let type_1 : type := «exec:2»; (let «type*» : (_root_.List type) := «exec:1»; (.bind (.call (Call.Type_ok C_0 type_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Types_ok C_1 «type*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Types_ok:clause:1» (input0 : context) (input1 : (_root_.List type)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «ty*» : (_root_.List type) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ty*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Types_ok_clauses (input0 : context) (input1 : (_root_.List type)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Types_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Types_ok:clause:1»  input0 input1)]

def «Import_ok:clause:0» (input0 : context) (input1 : «import») : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let _name : name := (input1).MODULENAME; (let _name' : name := (input1).ITEMNAME; (let importdesc : SpecTec.importdesc := (input1).IDESC; (.bind (.guard (((«exec:match:importdesc:FuncImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .FuncImport «exec:1» => (let x : idx := «exec:1»; (.bind (.call (Call.«$func_type» C_0 x)) (fun («exec:2» : functype) => (let «eval:0» : functype := «exec:2»; (let ft : functype := «eval:0»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:3» => (let «eval:1» : deftype := «exec:3»; (let C_1 : context := ({ C_0 with FUNCS := ((context.FUNCS C_0) ++ ([«eval:1»] : (_root_.List deftype))) } : context); (.pure ((C_1 : context))))) | none => .unmatch)))))))) | _ => .unmatch)))))))

def «Import_ok:clause:1» (input0 : context) (input1 : «import») : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let _name : name := (input1).MODULENAME; (let _name' : name := (input1).ITEMNAME; (let importdesc : SpecTec.importdesc := (input1).IDESC; (.bind (.guard (((«exec:match:importdesc:GlobalImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .GlobalImport «exec:1» => (let gt : globaltype := «exec:1»; (.bind (.call (Call.Globaltype_ok C_0 gt)) (fun («exec:2» : _root_.Unit) => (let C_1 : context := ({ C_0 with GLOBALS := ((context.GLOBALS C_0) ++ ([gt] : (_root_.List globaltype))) } : context); (.pure ((C_1 : context))))))) | _ => .unmatch)))))))

def «Import_ok:clause:2» (input0 : context) (input1 : «import») : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let _name : name := (input1).MODULENAME; (let _name' : name := (input1).ITEMNAME; (let importdesc : SpecTec.importdesc := (input1).IDESC; (.bind (.guard (((«exec:match:importdesc:TableImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .TableImport «exec:1» => (let tt : tabletype := «exec:1»; (.bind (.call (Call.Tabletype_ok C_0 tt)) (fun («exec:2» : _root_.Unit) => (let C_1 : context := ({ C_0 with TABLES := ((context.TABLES C_0) ++ ([tt] : (_root_.List tabletype))) } : context); (.pure ((C_1 : context))))))) | _ => .unmatch)))))))

def «Import_ok:clause:3» (input0 : context) (input1 : «import») : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let _name : name := (input1).MODULENAME; (let _name' : name := (input1).ITEMNAME; (let importdesc : SpecTec.importdesc := (input1).IDESC; (.bind (.guard (((«exec:match:importdesc:MemImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .MemImport «exec:1» => (let mt : memtype := «exec:1»; (.bind (.call (Call.Memtype_ok C_0 mt)) (fun («exec:2» : _root_.Unit) => (let C_1 : context := ({ C_0 with MEMS := ((context.MEMS C_0) ++ ([mt] : (_root_.List memtype))) } : context); (.pure ((C_1 : context))))))) | _ => .unmatch)))))))

def «Import_ok:clause:4» (input0 : context) (input1 : «import») : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let _name : name := (input1).MODULENAME; (let _name' : name := (input1).ITEMNAME; (let importdesc : SpecTec.importdesc := (input1).IDESC; (.bind (.guard (((«exec:match:importdesc:TagImport» importdesc) = true))) (fun (_ : Unit) => (match importdesc with | .TagImport «exec:1» => (let x : idx := «exec:1»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:2» => (let «eval:0» : deftype := «exec:2»; (.bind (.call (Call.Tagtype_ok C_0 (@tagtype.TagT «eval:0»))) (fun («exec:3» : _root_.Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:4» => (let «eval:1» : deftype := «exec:4»; (let C_1 : context := ({ C_0 with TAGS := ((context.TAGS C_0) ++ ([(@tagtype.TagT «eval:1»)] : (_root_.List tagtype))) } : context); (.pure ((C_1 : context))))) | none => .unmatch)))) | none => .unmatch)))) | _ => .unmatch)))))))

def Import_ok_clauses (input0 : context) (input1 : «import») : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Import_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Import_ok:clause:1»  input0 input1), fun (_ : _root_.Unit) => («Import_ok:clause:2»  input0 input1), fun (_ : _root_.Unit) => («Import_ok:clause:3»  input0 input1), fun (_ : _root_.Unit) => («Import_ok:clause:4»  input0 input1)]

def «Imports_ok:clause:0» (input0 : context) (input1 : (_root_.List «import»)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «im*» : (_root_.List «import») := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «im*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «im*» with | «exec:2» :: «exec:1» => (let import_1 : «import» := «exec:2»; (let «import*» : (_root_.List «import») := «exec:1»; (.bind (.call (Call.Import_ok C_0 import_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Imports_ok C_1 «import*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Imports_ok:clause:1» (input0 : context) (input1 : (_root_.List «import»)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «im*» : (_root_.List «import») := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «im*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Imports_ok_clauses (input0 : context) (input1 : (_root_.List «import»)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Imports_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Imports_ok:clause:1»  input0 input1)]

def «Func_ok:clause:0» (input0 : context) (input1 : func) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let x : idx := (input1).FTYPE; (let «local*» : (_root_.List «local») := (input1).LOCALS; (let «instr*» : (_root_.List instr) := (input1).BODY; (.bind (.call (Call.«$func_type» C_0 x)) (fun («exec:1» : functype) => (let «eval:0» : functype := «exec:1»; (let ft : functype := «eval:0»; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:2» => (let «eval:1» : deftype := «exec:2»; (let C_1 : context := ({ C_0 with FUNCS := ((context.FUNCS C_0) ++ ([«eval:1»] : (_root_.List deftype))) } : context); (.pure ((C_1 : context))))) | none => .unmatch)))))))))))

def Func_ok_clauses (input0 : context) (input1 : func) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Func_ok:clause:0»  input0 input1)]

def «Funcs_ok:clause:0» (input0 : context) (input1 : (_root_.List func)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «func'*» : (_root_.List func) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «func'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «func'*» with | «exec:2» :: «exec:1» => (let func_1 : func := «exec:2»; (let «func*» : (_root_.List func) := «exec:1»; (.bind (.call (Call.Func_ok C_0 func_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Funcs_ok C_1 «func*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Funcs_ok:clause:1» (input0 : context) (input1 : (_root_.List func)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «func*» : (_root_.List func) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «func*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Funcs_ok_clauses (input0 : context) (input1 : (_root_.List func)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Funcs_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Funcs_ok:clause:1»  input0 input1)]

def «Tag_ok:clause:0» (input0 : context) (input1 : tag) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let x : idx := (input1).TGTYPE; (.bind (.guard ((x < (_root_.List.length (context.TYPES C_0))))) (fun (_ : Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:1» => (let «eval:0» : deftype := «exec:1»; (.bind (.call (Call.Tagtype_ok C_0 (@tagtype.TagT «eval:0»))) (fun («exec:2» : _root_.Unit) => (match ((context.TYPES C_0)[x]?) with | some «exec:3» => (let «eval:1» : deftype := «exec:3»; (let C_1 : context := ({ C_0 with TAGS := ((context.TAGS C_0) ++ ([(@tagtype.TagT «eval:1»)] : (_root_.List tagtype))) } : context); (.pure ((C_1 : context))))) | none => .unmatch)))) | none => .unmatch)))))

def Tag_ok_clauses (input0 : context) (input1 : tag) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Tag_ok:clause:0»  input0 input1)]

def «Tags_ok:clause:0» (input0 : context) (input1 : (_root_.List tag)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «tag'*» : (_root_.List tag) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tag'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tag'*» with | «exec:2» :: «exec:1» => (let tag_1 : tag := «exec:2»; (let «tag*» : (_root_.List tag) := «exec:1»; (.bind (.call (Call.Tag_ok C_0 tag_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Tags_ok C_1 «tag*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Tags_ok:clause:1» (input0 : context) (input1 : (_root_.List tag)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «tag*» : (_root_.List tag) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tag*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Tags_ok_clauses (input0 : context) (input1 : (_root_.List tag)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Tags_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Tags_ok:clause:1»  input0 input1)]

def «Start_ok:clause:0» (input0 : context) (input1 : (_root_.Option start)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let start? : (_root_.Option start) := input1; (.bind (.guard (((_root_.Option.isSome start?) = true))) (fun (_ : Unit) => (match start? with | some «exec:1» => (let x : idx := («exec:1»).SFUNC; (.bind (.guard ((x < (_root_.List.length (context.FUNCS C_0))))) (fun (_ : Unit) => (match ((context.FUNCS C_0)[x]?) with | some «exec:2» => (let «eval:0» : deftype := «exec:2»; (.bind (.call (Call.«$expanddt» «eval:0»)) (fun («exec:3» : strtype) => (let «eval:1» : strtype := «exec:3»; (.bind (.call (Call.«$functype_of_strtype» «eval:1»)) (fun («exec:4» : functype) => (let «eval:2» : functype := «exec:4»; (match «eval:2» with | .FuncT «exec:5» «exec:6» => (match «exec:5» with | [] => (match «exec:6» with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch))))))))) | none => .unmatch)))) | none => .unmatch)))))

def «Start_ok:clause:1» (input0 : context) (input1 : (_root_.Option start)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let start? : (_root_.Option start) := input1; (.bind (.guard (((_root_.Option.isNone start?) = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))

def Start_ok_clauses (input0 : context) (input1 : (_root_.Option start)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Start_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Start_ok:clause:1»  input0 input1)]

def «Const_ok:clause:0» (input0 : context) (input1 : valtype) (input2 : const) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let t : valtype := input1; (let «instr*» : (_root_.List instr) := input2; (.bind (.call (Call.«Const_ok:rule:iter:0» C_0 «instr*»)) (fun («exec:1» : _root_.Unit) => (.bind (.call (Call.Block_ok C_0 (@instrtype.InstrT ([] : (_root_.List valtype)) ([t] : (_root_.List valtype)) ([] : (_root_.List localidx))) «instr*»)) (fun («exec:2» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))

def Const_ok_clauses (input0 : context) (input1 : valtype) (input2 : const) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Const_ok:clause:0»  input0 input1 input2)]

def «Table_ok:clause:0» (input0 : context) (input1 : table) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let tt : tabletype := (input1).TTYPE; (let const : SpecTec.const := (input1).TINIT; (match tt with | .TableT «exec:1» «exec:2» «exec:3» => (let «at» : addrtype := «exec:1»; (let lim : limits := «exec:2»; (let rt : reftype := «exec:3»; (.bind (.call (Call.Tabletype_ok C_0 tt)) (fun («exec:4» : _root_.Unit) => (.bind (.call (Call.Const_ok C_0 (@valtype.RefT rt) const)) (fun («exec:5» : _root_.Unit) => (let C_1 : context := ({ C_0 with TABLES := ((context.TABLES C_0) ++ ([tt] : (_root_.List tabletype))) } : context); (.pure ((C_1 : context)))))))))))))))

def Table_ok_clauses (input0 : context) (input1 : table) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Table_ok:clause:0»  input0 input1)]

def «Tables_ok:clause:0» (input0 : context) (input1 : (_root_.List table)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «tab*» : (_root_.List table) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tab*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tab*» with | «exec:2» :: «exec:1» => (let table_1 : table := «exec:2»; (let «table*» : (_root_.List table) := «exec:1»; (.bind (.call (Call.Table_ok C_0 table_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Tables_ok C_1 «table*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Tables_ok:clause:1» (input0 : context) (input1 : (_root_.List table)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «tab*» : (_root_.List table) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tab*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Tables_ok_clauses (input0 : context) (input1 : (_root_.List table)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Tables_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Tables_ok:clause:1»  input0 input1)]

def «Global_ok:clause:0» (input0 : context) (input1 : global) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let gt : globaltype := (input1).GTYPE; (let const : SpecTec.const := (input1).GINIT; (match gt with | .GlobalT «exec:1» «exec:2» => (let «mut» : SpecTec.«mut» := «exec:1»; (let t : valtype := «exec:2»; (.bind (.call (Call.Globaltype_ok C_0 gt)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.Const_ok C_0 t const)) (fun («exec:4» : _root_.Unit) => (let C_1 : context := ({ C_0 with GLOBALS := ((context.GLOBALS C_0) ++ ([gt] : (_root_.List globaltype))) } : context); (.pure ((C_1 : context))))))))))))))

def Global_ok_clauses (input0 : context) (input1 : global) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Global_ok:clause:0»  input0 input1)]

def «Globals_ok:clause:0» (input0 : context) (input1 : (_root_.List global)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «glob*» : (_root_.List global) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «glob*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «glob*» with | «exec:2» :: «exec:1» => (let global_1 : global := «exec:2»; (let «global*» : (_root_.List global) := «exec:1»; (.bind (.call (Call.Global_ok C_0 global_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Globals_ok C_1 «global*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Globals_ok:clause:1» (input0 : context) (input1 : (_root_.List global)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «glob*» : (_root_.List global) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «glob*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Globals_ok_clauses (input0 : context) (input1 : (_root_.List global)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Globals_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Globals_ok:clause:1»  input0 input1)]

def «Elem_ok:rule:iter:0:clause:0» (input0 : context) (input1 : reftype) (input2 : (_root_.List const)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let rt : reftype := input1; (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)))

def «Elem_ok:rule:iter:0:clause:1» (input0 : context) (input1 : reftype) (input2 : (_root_.List SpecTec.const)) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let rt : reftype := input1; (match input2 with | «exec:2» :: «exec:1» => (let const : SpecTec.const := «exec:2»; (let «tail:0» : (_root_.List SpecTec.const) := «exec:1»; (.bind (.call (Call.Const_ok C_0 (@valtype.RefT rt) const)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«Elem_ok:rule:iter:0» C_0 rt «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)))

def «Elem_ok:rule:iter:0_clauses» (input0 : context) (input1 : reftype) (input2 : (_root_.List const)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Elem_ok:rule:iter:0:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Elem_ok:rule:iter:0:clause:1»  input0 input1 input2)]

def «Elemmode_ok:clause:0» (input0 : context) (input1 : reftype) (input2 : SpecTec.elemmode) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let rt : reftype := input1; (let elemmode : SpecTec.elemmode := input2; (.bind (.guard (((«exec:match:elemmode:Passive» elemmode) = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))

def «Elemmode_ok:clause:1» (input0 : context) (input1 : reftype) (input2 : SpecTec.elemmode) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let rt : reftype := input1; (let elemmode : SpecTec.elemmode := input2; (.bind (.guard (((«exec:match:elemmode:Active» elemmode) = true))) (fun (_ : Unit) => (match elemmode with | .Active «exec:1» => (let x : idx := («exec:1»).INDEX; (let const : SpecTec.const := («exec:1»).OFFSET; (.bind (.guard ((x < (_root_.List.length (context.TABLES C_0))))) (fun (_ : Unit) => (match ((context.TABLES C_0)[x]?) with | some «exec:2» => (let «eval:0» : tabletype := «exec:2»; (match «eval:0» with | .TableT «exec:3» «exec:4» «exec:5» => (let «at» : addrtype := «exec:3»; (let lim : limits := «exec:4»; (let rt' : reftype := «exec:5»; (.bind (.call (Call.«$match_reftype» (context.TYPES C_0) rt rt')) (fun («exec:6» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:6»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:7» : numtype) => (let «eval:2» : numtype := «exec:7»; (.bind (.call (Call.Const_ok C_0 (@valtype.NumT «eval:2») const)) (fun («exec:8» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))))) | none => .unmatch))))) | _ => .unmatch))))))

def «Elemmode_ok:clause:2» (input0 : context) (input1 : reftype) (input2 : SpecTec.elemmode) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let rt : reftype := input1; (let elemmode : SpecTec.elemmode := input2; (.bind (.guard (((«exec:match:elemmode:Declarative» elemmode) = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))

def Elemmode_ok_clauses (input0 : context) (input1 : reftype) (input2 : elemmode) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Elemmode_ok:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Elemmode_ok:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («Elemmode_ok:clause:2»  input0 input1 input2)]

def «Elem_ok:clause:0» (input0 : context) (input1 : elem) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let rt : reftype := (input1).ETYPE; (let «const*» : (_root_.List const) := (input1).EINIT; (let elemmode : SpecTec.elemmode := (input1).EMODE; (.bind (.call (Call.Reftype_ok C_0 rt)) (fun («exec:1» : _root_.Unit) => (.bind (.call (Call.«Elem_ok:rule:iter:0» C_0 rt «const*»)) (fun («exec:2» : _root_.Unit) => (.bind (.call (Call.Elemmode_ok C_0 rt elemmode)) (fun («exec:3» : _root_.Unit) => (let C_1 : context := ({ C_0 with ELEMS := ((context.ELEMS C_0) ++ ([rt] : (_root_.List reftype))) } : context); (.pure ((C_1 : context))))))))))))))

def Elem_ok_clauses (input0 : context) (input1 : elem) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Elem_ok:clause:0»  input0 input1)]

def «Elems_ok:clause:0» (input0 : context) (input1 : (_root_.List elem)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «elem'*» : (_root_.List elem) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «elem'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «elem'*» with | «exec:2» :: «exec:1» => (let elem_1 : elem := «exec:2»; (let «elem*» : (_root_.List elem) := «exec:1»; (.bind (.call (Call.Elem_ok C_0 elem_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Elems_ok C_1 «elem*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Elems_ok:clause:1» (input0 : context) (input1 : (_root_.List elem)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «elem*» : (_root_.List elem) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «elem*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Elems_ok_clauses (input0 : context) (input1 : (_root_.List elem)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Elems_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Elems_ok:clause:1»  input0 input1)]

def «Datamode_ok:clause:0» (input0 : context) (input1 : SpecTec.datamode) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let datamode : SpecTec.datamode := input1; (.bind (.guard (((«exec:match:datamode:Passive» datamode) = true))) (fun (_ : Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))

def «Datamode_ok:clause:1» (input0 : context) (input1 : SpecTec.datamode) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let datamode : SpecTec.datamode := input1; (.bind (.guard (((«exec:match:datamode:Active» datamode) = true))) (fun (_ : Unit) => (match datamode with | .Active «exec:1» => (let x : idx := («exec:1»).INDEX; (let const : SpecTec.const := («exec:1»).OFFSET; (.bind (.guard ((x < (_root_.List.length (context.MEMS C_0))))) (fun (_ : Unit) => (match ((context.MEMS C_0)[x]?) with | some «exec:2» => (let «eval:0» : memtype := «exec:2»; (match «eval:0» with | .MemoryT «exec:3» «exec:4» => (let «at» : addrtype := «exec:3»; (let _lim : limits := «exec:4»; (.bind (.call (Call.«$numtype_of_addrtype» «at»)) (fun («exec:5» : numtype) => (let «eval:1» : numtype := «exec:5»; (.bind (.call (Call.Const_ok C_0 (@valtype.NumT «eval:1») const)) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | none => .unmatch))))) | _ => .unmatch)))))

def Datamode_ok_clauses (input0 : context) (input1 : datamode) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Datamode_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Datamode_ok:clause:1»  input0 input1)]

def «Data_ok:clause:0» (input0 : context) (input1 : data) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let _text : _root_.String := (input1).DINIT; (let datamode : SpecTec.datamode := (input1).DMODE; (.bind (.call (Call.Datamode_ok C_0 datamode)) (fun («exec:1» : _root_.Unit) => (let C_1 : context := ({ C_0 with DATAS := ((context.DATAS C_0) ++ ([(@datatype.OK)] : (_root_.List datatype))) } : context); (.pure ((C_1 : context)))))))))

def Data_ok_clauses (input0 : context) (input1 : data) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Data_ok:clause:0»  input0 input1)]

def «Datas_ok:clause:0» (input0 : context) (input1 : (_root_.List data)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «data'*» : (_root_.List data) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «data'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «data'*» with | «exec:2» :: «exec:1» => (let data_1 : data := «exec:2»; (let «data*» : (_root_.List data) := «exec:1»; (.bind (.call (Call.Data_ok C_0 data_1)) (fun («exec:3» : context) => (let C_1 : context := «exec:3»; (.bind (.call (Call.Datas_ok C_1 «data*»)) (fun («exec:4» : context) => (let C_2 : context := «exec:4»; (.pure ((C_2 : context))))))))))) | [] => .unmatch)))))

def «Datas_ok:clause:1» (input0 : context) (input1 : (_root_.List data)) : ExecutablePlan Call context :=
  (let C_0 : context := input0; (let «data*» : (_root_.List data) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «data*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((C_0 : context)))))))

def Datas_ok_clauses (input0 : context) (input1 : (_root_.List data)) : List (ExecutablePlan.Clause Call _root_.Unit context) :=
  [fun (_ : _root_.Unit) => («Datas_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Datas_ok:clause:1»  input0 input1)]

def «Local_ok:clause:0» (input0 : context) (input1 : «local») : ExecutablePlan Call localtype :=
  (let C : context := input0; (let t : valtype := (input1).LTYPE; (.bind (.call (Call.Valtype_ok C t)) (fun («exec:1» : _root_.Unit) => (.bind (.call (Call.«$defaultable» t)) (fun («exec:2» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:2»; (.bind (.guard (true = «eval:0»)) (fun (_ : Unit) => (.pure (((@localtype.LocalT (@init.Set) t) : localtype))))))))))))

def «Local_ok:clause:1» (input0 : context) (input1 : «local») : ExecutablePlan Call localtype :=
  (let C : context := input0; (let t : valtype := (input1).LTYPE; (.bind (.call (Call.Valtype_ok C t)) (fun («exec:1» : _root_.Unit) => (.bind (.call (Call.«$defaultable» t)) (fun («exec:2» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:2»; (.bind (.guard (false = «eval:0»)) (fun (_ : Unit) => (.pure (((@localtype.LocalT (@init.Unset) t) : localtype))))))))))))

def Local_ok_clauses (input0 : context) (input1 : «local») : List (ExecutablePlan.Clause Call _root_.Unit localtype) :=
  [fun (_ : _root_.Unit) => («Local_ok:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Local_ok:clause:1»  input0 input1)]

def «Funcbody_ok:rule:iter:1:clause:0» (input0 : context) (input1 : (_root_.List «local»)) : ExecutablePlan Call (_root_.List localtype) :=
  (let C_0 : context := input0; (match input1 with | [] => (.pure ((([] : (_root_.List localtype)) : (_root_.List localtype)))) | _ :: _ => .unmatch))

def «Funcbody_ok:rule:iter:1:clause:1» (input0 : context) (input1 : (_root_.List SpecTec.«local»)) : ExecutablePlan Call (_root_.List localtype) :=
  (let C_0 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let «local» : SpecTec.«local» := «exec:2»; (let «tail:0» : (_root_.List SpecTec.«local») := «exec:1»; (.bind (.call (Call.Local_ok C_0 «local»)) (fun («exec:3» : SpecTec.localtype) => (let localtype : SpecTec.localtype := «exec:3»; (.bind (.call (Call.«Funcbody_ok:rule:iter:1» C_0 «tail:0»)) (fun («exec:4» : (_root_.List SpecTec.localtype)) => (let «tail:1» : (_root_.List SpecTec.localtype) := «exec:4»; (.pure (((localtype :: «tail:1») : (_root_.List SpecTec.localtype)))))))))))) | [] => .unmatch))

def «Funcbody_ok:rule:iter:1_clauses» (input0 : context) (input1 : (_root_.List «local»)) : List (ExecutablePlan.Clause Call _root_.Unit (_root_.List localtype)) :=
  [fun (_ : _root_.Unit) => («Funcbody_ok:rule:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Funcbody_ok:rule:iter:1:clause:1»  input0 input1)]

def «Funcbody_ok:clause:0» (input0 : context) (input1 : func) : ExecutablePlan Call _root_.Unit :=
  (let C_0 : context := input0; (let x : idx := (input1).FTYPE; (let «local*» : (_root_.List «local») := (input1).LOCALS; (let «instr*» : (_root_.List instr) := (input1).BODY; (.bind (.call (Call.«$func_type» C_0 x)) (fun («exec:1» : functype) => (let «eval:0» : functype := «exec:1»; (match «eval:0» with | .FuncT «exec:2» «exec:3» => (let «t_1*» : (_root_.List valtype) := «exec:2»; (let «t_2*» : (_root_.List valtype) := «exec:3»; (.bind (.call (Call.«Funcbody_ok:rule:iter:1» C_0 «local*»)) (fun («exec:4» : (_root_.List localtype)) => (let «localtype*» : (_root_.List localtype) := «exec:4»; (.bind (.call (Call.«Funcbody_ok:rule:iter:2» «t_1*»)) (fun («exec:5» : (_root_.List localtype)) => (let «localtype'*» : (_root_.List localtype) := «exec:5»; (let C_1 : context := ({ C_0 with LOCALS := («localtype'*» ++ «localtype*») } : context); (let C_2 : context := ({ C_1 with RESULTS := «t_2*» } : context); (let C_3 : context := ({ C_2 with LABELS := ([«t_2*»] : (_root_.List (_root_.List valtype))) } : context); (.bind (.call (Call.Block_ok C_3 (@instrtype.InstrT ([] : (_root_.List valtype)) «t_2*» ([] : (_root_.List localidx))) «instr*»)) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))))))))))))))

def Funcbody_ok_clauses (input0 : context) (input1 : func) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Funcbody_ok:clause:0»  input0 input1)]

def «Module_ok:rule:iter:2:clause:0» (input0 : context) (input1 : (_root_.List func)) : ExecutablePlan Call _root_.Unit :=
  (let C_8 : context := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))

def «Module_ok:rule:iter:2:clause:1» (input0 : context) (input1 : (_root_.List SpecTec.func)) : ExecutablePlan Call _root_.Unit :=
  (let C_8 : context := input0; (match input1 with | «exec:2» :: «exec:1» => (let func : SpecTec.func := «exec:2»; (let «tail:0» : (_root_.List SpecTec.func) := «exec:1»; (.bind (.call (Call.Funcbody_ok C_8 func)) (fun («exec:3» : _root_.Unit) => (.bind (.call (Call.«Module_ok:rule:iter:2» C_8 «tail:0»)) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))

def «Module_ok:rule:iter:2_clauses» (input0 : context) (input1 : (_root_.List func)) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Module_ok:rule:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Module_ok:rule:iter:2:clause:1»  input0 input1)]

def «Module_ok:clause:0» (input0 : SpecTec.module) : ExecutablePlan Call _root_.Unit :=
  (let module : SpecTec.module := input0; (let module' : SpecTec.module := ({ ({ module with FUNCS := ([] : (_root_.List func)) } : SpecTec.module) with START := ((_root_.Option.none) : (_root_.Option start)) } : SpecTec.module); (.bind (.call (Call.«$free_module» module')) (fun («exec:1» : SpecTec.free) => (let «eval:0» : SpecTec.free := «exec:1»; (let free : SpecTec.free := «eval:0»; (.bind (.call (Call.«$empty_context»)) (fun («exec:2» : context) => (let «eval:1» : context := «exec:2»; (let C : context := ({ «eval:1» with REFS := free } : context); (.bind (.call (Call.Types_ok C (SpecTec.module.TYPES module))) (fun («exec:3» : context) => (let C_0 : context := «exec:3»; (.bind (.call (Call.Imports_ok C_0 (SpecTec.module.IMPORTS module))) (fun («exec:4» : context) => (let C_1 : context := «exec:4»; (.bind (.call (Call.Funcs_ok C_1 (SpecTec.module.FUNCS module))) (fun («exec:5» : context) => (let C_2 : context := «exec:5»; (.bind (.call (Call.Tables_ok C_2 (SpecTec.module.TABLES module))) (fun («exec:6» : context) => (let C_3 : context := «exec:6»; (.bind (.call (Call.Mems_ok C_3 (SpecTec.module.MEMS module))) (fun («exec:7» : context) => (let C_4 : context := «exec:7»; (.bind (.call (Call.Globals_ok C_4 (SpecTec.module.GLOBALS module))) (fun («exec:8» : context) => (let C_5 : context := «exec:8»; (.bind (.call (Call.Tags_ok C_5 (SpecTec.module.TAGS module))) (fun («exec:9» : context) => (let C_6 : context := «exec:9»; (.bind (.call (Call.Elems_ok C_6 (SpecTec.module.ELEMS module))) (fun («exec:10» : context) => (let C_7 : context := «exec:10»; (.bind (.call (Call.Datas_ok C_7 (SpecTec.module.DATAS module))) (fun («exec:11» : context) => (let C_8 : context := «exec:11»; (let «func*» : (_root_.List func) := (SpecTec.module.FUNCS module); (.bind (.call (Call.«Module_ok:rule:iter:2» C_8 «func*»)) (fun («exec:12» : _root_.Unit) => (.bind (.call (Call.Start_ok C_8 (SpecTec.module.START module))) (fun («exec:13» : _root_.Unit) => (.bind (.call (Call.Exports_ok C_8 (@set.«`{ % `}» name ([] : (_root_.List name))) (SpecTec.module.EXPORTS module))) (fun («exec:14» : SpecTec.nameset) => (let nameset : SpecTec.nameset := «exec:14»; (.pure (((_root_.Unit.unit) : _root_.Unit))))))))))))))))))))))))))))))))))))))))))))))))

def Module_ok_clauses (input0 : module) : List (ExecutablePlan.Clause Call _root_.Unit _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Module_ok:clause:0»  input0)]
def body {α : Type} (request : Call α) : ExecutablePlan Call α :=
  match request with
  | @Call.«$min_» input0 input1 =>  ExecutablePlan.firstSuccess («$min__clauses» input0 input1) ()
  | @Call.«$rev_» X input0 =>  ExecutablePlan.firstSuccess («$rev__clauses» X input0) ()
  | @Call.«$make_» X_T input0 input1 =>  ExecutablePlan.firstSuccess («$make__clauses» X_T input0 input1) ()
  | @Call.«$empty_set» K =>  ExecutablePlan.firstSuccess («$empty_set_clauses» K) ()
  | @Call.«$in_set» K_T eq_K_T input0 input1 => letI : _root_.DecidableEq K_T := eq_K_T; ExecutablePlan.firstSuccess («$in_set_clauses» K_T input0 input1) ()
  | @Call.«$map_set» X Y compare_Y input0 input1 => letI : _root_.SpecTecCompareKey Y := compare_Y; ExecutablePlan.firstSuccess («$map_set_clauses» X Y input0 input1) ()
  | @Call.«$range» input0 =>  ExecutablePlan.firstSuccess («$range_clauses» input0) ()
  | @Call.«$rolldt'» input0 input1 =>  ExecutablePlan.firstSuccess («$rolldt'_clauses» input0 input1) ()
  | @Call.«$min_addrtype» input0 input1 =>  ExecutablePlan.firstSuccess («$min_addrtype_clauses» input0 input1) ()
  | @Call.«$num_size» input0 =>  ExecutablePlan.firstSuccess («$num_size_clauses» input0) ()
  | @Call.«$vec_size» input0 =>  ExecutablePlan.firstSuccess («$vec_size_clauses» input0) ()
  | @Call.«$type_vecop» A input0 =>  ExecutablePlan.firstSuccess («$type_vecop_clauses» A input0) ()
  | @Call.«$free_empty»  =>  ExecutablePlan.firstSuccess («$free_empty_clauses» ) ()
  | @Call.«$fold_left» X_T Y input0 input1 input2 =>  ExecutablePlan.firstSuccess («$fold_left_clauses» X_T Y input0 input1 input2) ()
  | @Call.«$free_union» input0 input1 =>  ExecutablePlan.firstSuccess («$free_union_clauses» input0 input1) ()
  | @Call.«$free_unions» input0 =>  ExecutablePlan.firstSuccess («$free_unions_clauses» input0) ()
  | @Call.«$add_minus_one» input0 =>  ExecutablePlan.firstSuccess («$add_minus_one_clauses» input0) ()
  | @Call.«$free_idx» input0 =>  ExecutablePlan.firstSuccess («$free_idx_clauses» input0) ()
  | @Call.«$free_shift» input0 =>  ExecutablePlan.firstSuccess («$free_shift_clauses» input0) ()
  | @Call.«$free_list» X input0 input1 =>  ExecutablePlan.firstSuccess («$free_list_clauses» X input0 input1) ()
  | @Call.«$free_opt» X_T input0 input1 =>  ExecutablePlan.firstSuccess («$free_opt_clauses» X_T input0 input1) ()
  | @Call.«$free_packtype» input0 =>  ExecutablePlan.firstSuccess («$free_packtype_clauses» input0) ()
  | @Call.«$free_numtype» input0 =>  ExecutablePlan.firstSuccess («$free_numtype_clauses» input0) ()
  | @Call.«$free_vectype» input0 =>  ExecutablePlan.firstSuccess («$free_vectype_clauses» input0) ()
  | @Call.«$update_types» input0 =>  ExecutablePlan.firstSuccess («$update_types_clauses» input0) ()
  | @Call.«$update_globals» input0 =>  ExecutablePlan.firstSuccess («$update_globals_clauses» input0) ()
  | @Call.«$update_tables» input0 =>  ExecutablePlan.firstSuccess («$update_tables_clauses» input0) ()
  | @Call.«$update_mems» input0 =>  ExecutablePlan.firstSuccess («$update_mems_clauses» input0) ()
  | @Call.«$update_tags» input0 =>  ExecutablePlan.firstSuccess («$update_tags_clauses» input0) ()
  | @Call.«$update_funcs» input0 =>  ExecutablePlan.firstSuccess («$update_funcs_clauses» input0) ()
  | @Call.«$free_start» input0 =>  ExecutablePlan.firstSuccess («$free_start_clauses» input0) ()
  | @Call.«$update_elems» input0 =>  ExecutablePlan.firstSuccess («$update_elems_clauses» input0) ()
  | @Call.«$update_datas» input0 =>  ExecutablePlan.firstSuccess («$update_datas_clauses» input0) ()
  | @Call.«$update_locals» input0 =>  ExecutablePlan.firstSuccess («$update_locals_clauses» input0) ()
  | @Call.«$update_labels» input0 =>  ExecutablePlan.firstSuccess («$update_labels_clauses» input0) ()
  | @Call.«$update_label» input0 =>  ExecutablePlan.firstSuccess («$update_label_clauses» input0) ()
  | @Call.«$free_memtype» input0 =>  ExecutablePlan.firstSuccess («$free_memtype_clauses» input0) ()
  | @Call.«$free_mem» input0 =>  ExecutablePlan.firstSuccess («$free_mem_clauses» input0) ()
  | @Call.«$match_numtype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_numtype_clauses» input0 input1 input2) ()
  | @Call.«$match_vectype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_vectype_clauses» input0 input1 input2) ()
  | @Call.«$match_packtype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_packtype_clauses» input0 input1 input2) ()
  | @Call.«$empty_context»  =>  ExecutablePlan.firstSuccess («$empty_context_clauses» ) ()
  | @Call.«$stack» input0 =>  ExecutablePlan.firstSuccess («$stack_clauses» input0) ()
  | @Call.«$peek» input0 input1 =>  ExecutablePlan.firstSuccess («$peek_clauses» input0 input1) ()
  | @Call.«$local» input0 input1 =>  ExecutablePlan.firstSuccess («$local_clauses» input0 input1) ()
  | @Call.«$init_local» input0 input1 =>  ExecutablePlan.firstSuccess («$init_local_clauses» input0 input1) ()
  | @Call.«$init_locals» input0 input1 =>  ExecutablePlan.firstSuccess («$init_locals_clauses» input0 input1) ()
  | @Call.«$init_valtypes» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$init_valtypes_clauses» input0 input1 input2) ()
  | @Call.Numtype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Numtype_ok_clauses input0 input1) ()
  | @Call.Vectype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Vectype_ok_clauses input0 input1) ()
  | @Call.Limits_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Limits_ok_clauses input0 input1 input2) ()
  | @Call.«Instr_ok:br_table:iter:3» input0 input1 =>  ExecutablePlan.firstSuccess («Instr_ok:br_table:iter:3_clauses» input0 input1) ()
  | @Call.«$check_lane_index» input0 =>  ExecutablePlan.firstSuccess («$check_lane_index_clauses» input0) ()
  | @Call.«Funcbody_ok:rule:iter:2» input0 =>  ExecutablePlan.firstSuccess («Funcbody_ok:rule:iter:2_clauses» input0) ()
  | @Call.«$numtype_of_addrtype» input0 =>  ExecutablePlan.firstSuccess («$numtype_of_addrtype_clauses» input0) ()
  | @Call.Memtype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Memtype_ok_clauses input0 input1) ()
  | @Call.Vstoreop_ok input0 input1 =>  ExecutablePlan.firstSuccess (Vstoreop_ok_clauses input0 input1) ()
  | @Call.Mem_ok input0 input1 =>  ExecutablePlan.firstSuccess (Mem_ok_clauses input0 input1) ()
  | @Call.Mems_ok input0 input1 =>  ExecutablePlan.firstSuccess (Mems_ok_clauses input0 input1) ()
  | @Call.«$free_catch» input0 =>  ExecutablePlan.firstSuccess («$free_catch_clauses» input0) ()
  | @Call.«$push» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$push_clauses» input0 input1 input2) ()
  | @Call.«$free_exportdesc» input0 =>  ExecutablePlan.firstSuccess («$free_exportdesc_clauses» input0) ()
  | @Call.«$free_export» input0 =>  ExecutablePlan.firstSuccess («$free_export_clauses» input0) ()
  | @Call.Export_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Export_ok_clauses input0 input1 input2) ()
  | @Call.Exports_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Exports_ok_clauses input0 input1 input2) ()
  | @Call.«$type_externop» input0 =>  ExecutablePlan.firstSuccess («$type_externop_clauses» input0) ()
  | @Call.«$is_const» input0 input1 =>  ExecutablePlan.firstSuccess («$is_const_clauses» input0 input1) ()
  | @Call.«Const_ok:rule:iter:0» input0 input1 =>  ExecutablePlan.firstSuccess («Const_ok:rule:iter:0_clauses» input0 input1) ()
  | @Call.«$type_lane» A B C D E F input0 =>  ExecutablePlan.firstSuccess («$type_lane_clauses» A B C D E F input0) ()
  | @Call.«$type_vec_lane» A_T B_T C_T D_T E_T F_T input0 =>  ExecutablePlan.firstSuccess («$type_vec_lane_clauses» A_T B_T C_T D_T E_T F_T input0) ()
  | @Call.«$lane_extractop» input0 =>  ExecutablePlan.firstSuccess («$lane_extractop_clauses» input0) ()
  | @Call.«$lane_replaceop» input0 =>  ExecutablePlan.firstSuccess («$lane_replaceop_clauses» input0) ()
  | @Call.«$num_lanes» A B C D E F input0 =>  ExecutablePlan.firstSuccess («$num_lanes_clauses» A B C D E F input0) ()
  | @Call.«$diff_reftype» input0 input1 =>  ExecutablePlan.firstSuccess («$diff_reftype_clauses» input0 input1) ()
  | @Call.«$match_null» input0 input1 =>  ExecutablePlan.firstSuccess («$match_null_clauses» input0 input1) ()
  | @Call.«$type_num» A_T B_T C_T D_T input0 =>  ExecutablePlan.firstSuccess («$type_num_clauses» A_T B_T C_T D_T input0) ()
  | @Call.«$type_cvtop» input0 =>  ExecutablePlan.firstSuccess («$type_cvtop_clauses» input0) ()
  | @Call.«$check_uop_extends» input0 =>  ExecutablePlan.firstSuccess («$check_uop_extends_clauses» input0) ()
  | @Call.«$pack_size» input0 =>  ExecutablePlan.firstSuccess («$pack_size_clauses» input0) ()
  | @Call.Pack_ok input0 input1 =>  ExecutablePlan.firstSuccess (Pack_ok_clauses input0 input1) ()
  | @Call.Unop_ok input0 =>  ExecutablePlan.firstSuccess (Unop_ok_clauses input0) ()
  | @Call.Loadop_ok input0 input1 =>  ExecutablePlan.firstSuccess (Loadop_ok_clauses input0 input1) ()
  | @Call.Storeop_ok input0 input1 =>  ExecutablePlan.firstSuccess (Storeop_ok_clauses input0 input1) ()
  | @Call.Vloadop_ok input0 input1 =>  ExecutablePlan.firstSuccess (Vloadop_ok_clauses input0 input1) ()
  | @Call.Vlaneop_ok input0 input1 =>  ExecutablePlan.firstSuccess (Vlaneop_ok_clauses input0 input1) ()
  | @Call.«$unpacked_storage_type» input0 =>  ExecutablePlan.firstSuccess («$unpacked_storage_type_clauses» input0) ()
  | @Call.«$unpacked_field_type» input0 =>  ExecutablePlan.firstSuccess («$unpacked_field_type_clauses» input0) ()
  | @Call.«$is_packed_storage_type» input0 =>  ExecutablePlan.firstSuccess («$is_packed_storage_type_clauses» input0) ()
  | @Call.«Instr_ok:struct.new.explicit:iter:1» input0 =>  ExecutablePlan.firstSuccess («Instr_ok:struct.new.explicit:iter:1_clauses» input0) ()
  | @Call.«$functype_of_strtype» input0 =>  ExecutablePlan.firstSuccess («$functype_of_strtype_clauses» input0) ()
  | @Call.«$abs_of_str_type» input0 =>  ExecutablePlan.firstSuccess («$abs_of_str_type_clauses» input0) ()
  | @Call.«$s_unroll» input0 input1 =>  ExecutablePlan.firstSuccess («$s_unroll_clauses» input0 input1) ()
  | @Call.«$s_roll» input0 input1 =>  ExecutablePlan.firstSuccess («$s_roll_clauses» input0 input1) ()
  | @Call.«$free_typevar» input0 =>  ExecutablePlan.firstSuccess («$free_typevar_clauses» input0) ()
  | @Call.«$subst_of» input0 input1 =>  ExecutablePlan.firstSuccess («$subst_of_clauses» input0 input1) ()
  | @Call.«$is_num_type» input0 =>  ExecutablePlan.firstSuccess («$is_num_type_clauses» input0) ()
  | @Call.«$peek_ref» input0 input1 =>  ExecutablePlan.firstSuccess («$peek_ref_clauses» input0 input1) ()
  | @Call.«$is_vec_type» input0 =>  ExecutablePlan.firstSuccess («$is_vec_type_clauses» input0) ()
  | @Call.«$defaultable» input0 =>  ExecutablePlan.firstSuccess («$defaultable_clauses» input0) ()
  | @Call.«Instr_ok:struct.new.implicit:iter:1» input0 =>  ExecutablePlan.firstSuccess («Instr_ok:struct.new.implicit:iter:1_clauses» input0) ()
  | @Call.«$check_vbop_shuffle» input0 =>  ExecutablePlan.firstSuccess («$check_vbop_shuffle_clauses» input0) ()
  | @Call.Vecbinop_ok input0 =>  ExecutablePlan.firstSuccess (Vecbinop_ok_clauses input0) ()
  | @Call.«$subst_heaptype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_heaptype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_subtype:case_1:iter:0» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_subtype:case_1:iter:0_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_reftype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_reftype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_valtype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_valtype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_resulttype:case_1:iter:0» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_resulttype:case_1:iter:0_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_resulttype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_resulttype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_functype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_functype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_storagetype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_storagetype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_fieldtype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_fieldtype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_structtype:case_1:iter:0» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_structtype:case_1:iter:0_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_structtype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_structtype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_arraytype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_arraytype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_strtype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_strtype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_subtype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_subtype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_rectype:case_1:iter:0» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_rectype:case_1:iter:0_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_rectype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_rectype_clauses» X_T input0 input1 input2) ()
  | @Call.«$subst_deftype» X_T input0 input1 input2 =>  ExecutablePlan.firstSuccess («$subst_deftype_clauses» X_T input0 input1 input2) ()
  | @Call.«$rollrt» input0 input1 =>  ExecutablePlan.firstSuccess («$rollrt_clauses» input0 input1) ()
  | @Call.«$unrollrt» input0 =>  ExecutablePlan.firstSuccess («$unrollrt_clauses» input0) ()
  | @Call.«$rolldt» input0 input1 =>  ExecutablePlan.firstSuccess («$rolldt_clauses» input0 input1) ()
  | @Call.«$unrolldt» input0 =>  ExecutablePlan.firstSuccess («$unrolldt_clauses» input0) ()
  | @Call.«$expanddt» input0 =>  ExecutablePlan.firstSuccess («$expanddt_clauses» input0) ()
  | @Call.«$free_heaptype» input0 =>  ExecutablePlan.firstSuccess («$free_heaptype_clauses» input0) ()
  | @Call.«$free_reftype» input0 =>  ExecutablePlan.firstSuccess («$free_reftype_clauses» input0) ()
  | @Call.«$free_valtype» input0 =>  ExecutablePlan.firstSuccess («$free_valtype_clauses» input0) ()
  | @Call.«$free_functype» input0 =>  ExecutablePlan.firstSuccess («$free_functype_clauses» input0) ()
  | @Call.«$free_storagetype» input0 =>  ExecutablePlan.firstSuccess («$free_storagetype_clauses» input0) ()
  | @Call.«$free_fieldtype» input0 =>  ExecutablePlan.firstSuccess («$free_fieldtype_clauses» input0) ()
  | @Call.«$free_structtype» input0 =>  ExecutablePlan.firstSuccess («$free_structtype_clauses» input0) ()
  | @Call.«$free_arraytype» input0 =>  ExecutablePlan.firstSuccess («$free_arraytype_clauses» input0) ()
  | @Call.«$free_strtype» input0 =>  ExecutablePlan.firstSuccess («$free_strtype_clauses» input0) ()
  | @Call.«$free_subtype» input0 =>  ExecutablePlan.firstSuccess («$free_subtype_clauses» input0) ()
  | @Call.«$free_rectype» input0 =>  ExecutablePlan.firstSuccess («$free_rectype_clauses» input0) ()
  | @Call.«$free_type_» input0 =>  ExecutablePlan.firstSuccess («$free_type__clauses» input0) ()
  | @Call.«$free_globaltype» input0 =>  ExecutablePlan.firstSuccess («$free_globaltype_clauses» input0) ()
  | @Call.«$free_blocktype» input0 =>  ExecutablePlan.firstSuccess («$free_blocktype_clauses» input0) ()
  | @Call.«$free_instr» input0 =>  ExecutablePlan.firstSuccess («$free_instr_clauses» input0) ()
  | @Call.«$free_block» input0 =>  ExecutablePlan.firstSuccess («$free_block_clauses» input0) ()
  | @Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» input0 =>  ExecutablePlan.firstSuccess («$free_list:specialized:627ab0672e3a767978c05fd35fc5a959_clauses» input0) ()
  | @Call.«$free_const» input0 =>  ExecutablePlan.firstSuccess («$free_const_clauses» input0) ()
  | @Call.«$free_global» input0 =>  ExecutablePlan.firstSuccess («$free_global_clauses» input0) ()
  | @Call.«$free_tabletype» input0 =>  ExecutablePlan.firstSuccess («$free_tabletype_clauses» input0) ()
  | @Call.«$free_table» input0 =>  ExecutablePlan.firstSuccess («$free_table_clauses» input0) ()
  | @Call.«$free_elemmode» input0 input1 =>  ExecutablePlan.firstSuccess («$free_elemmode_clauses» input0 input1) ()
  | @Call.«$free_elem» input0 =>  ExecutablePlan.firstSuccess («$free_elem_clauses» input0) ()
  | @Call.«$free_datamode» input0 input1 =>  ExecutablePlan.firstSuccess («$free_datamode_clauses» input0 input1) ()
  | @Call.«$free_data» input0 =>  ExecutablePlan.firstSuccess («$free_data_clauses» input0) ()
  | @Call.«$free_importdesc» input0 =>  ExecutablePlan.firstSuccess («$free_importdesc_clauses» input0) ()
  | @Call.«$free_import» input0 =>  ExecutablePlan.firstSuccess («$free_import_clauses» input0) ()
  | @Call.«$free_module» input0 =>  ExecutablePlan.firstSuccess («$free_module_clauses» input0) ()
  | @Call.«$match_deftype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_deftype_clauses» input0 input1 input2) ()
  | @Call.«$match_heaptype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_heaptype_clauses» input0 input1 input2) ()
  | @Call.«$match_heaptype_exists» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_heaptype_exists_clauses» input0 input1 input2) ()
  | @Call.«$match_reftype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_reftype_clauses» input0 input1 input2) ()
  | @Call.«$match_valtype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_valtype_clauses» input0 input1 input2) ()
  | @Call.«$match_storagetype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_storagetype_clauses» input0 input1 input2) ()
  | @Call.«$match_fieldtype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_fieldtype_clauses» input0 input1 input2) ()
  | @Call.«$match_arraytype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_arraytype_clauses» input0 input1 input2) ()
  | @Call.«$match_structtype:case_1:iter:0» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_structtype:case_1:iter:0_clauses» input0 input1 input2) ()
  | @Call.«$match_structtype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_structtype_clauses» input0 input1 input2) ()
  | @Call.«$match_resulttype:case_1:iter:0» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_resulttype:case_1:iter:0_clauses» input0 input1 input2) ()
  | @Call.«$match_resulttype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_resulttype_clauses» input0 input1 input2) ()
  | @Call.«$match_functype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_functype_clauses» input0 input1 input2) ()
  | @Call.«$match_strtype» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$match_strtype_clauses» input0 input1 input2) ()
  | @Call.«$top_of_str_type» input0 input1 =>  ExecutablePlan.firstSuccess («$top_of_str_type_clauses» input0 input1) ()
  | @Call.«$top_of_heap_type» input0 input1 =>  ExecutablePlan.firstSuccess («$top_of_heap_type_clauses» input0 input1) ()
  | @Call.«Match_resulttype:rule:iter:0» input0 input1 input2 =>  ExecutablePlan.firstSuccess («Match_resulttype:rule:iter:0_clauses» input0 input1 input2) ()
  | @Call.Match_resulttype input0 input1 input2 =>  ExecutablePlan.firstSuccess (Match_resulttype_clauses input0 input1 input2) ()
  | @Call.«$pop» input0 input1 input2 =>  ExecutablePlan.firstSuccess («$pop_clauses» input0 input1 input2) ()
  | @Call.Heaptype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Heaptype_ok_clauses input0 input1) ()
  | @Call.Reftype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Reftype_ok_clauses input0 input1) ()
  | @Call.Valtype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Valtype_ok_clauses input0 input1) ()
  | @Call.«Resulttype_ok:rule:iter:0» input0 input1 =>  ExecutablePlan.firstSuccess («Resulttype_ok:rule:iter:0_clauses» input0 input1) ()
  | @Call.Resulttype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Resulttype_ok_clauses input0 input1) ()
  | @Call.Functype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Functype_ok_clauses input0 input1) ()
  | @Call.«Subtype_ok:rule:iter:0» input0 input1 =>  ExecutablePlan.firstSuccess («Subtype_ok:rule:iter:0_clauses» input0 input1) ()
  | @Call.Storagetype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Storagetype_ok_clauses input0 input1) ()
  | @Call.Fieldtype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Fieldtype_ok_clauses input0 input1) ()
  | @Call.«Structtype_ok:rule:iter:0» input0 input1 =>  ExecutablePlan.firstSuccess («Structtype_ok:rule:iter:0_clauses» input0 input1) ()
  | @Call.Structtype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Structtype_ok_clauses input0 input1) ()
  | @Call.Arraytype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Arraytype_ok_clauses input0 input1) ()
  | @Call.Strtype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Strtype_ok_clauses input0 input1) ()
  | @Call.Subtype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Subtype_ok_clauses input0 input1) ()
  | @Call.Subtype_sub_ok' input0 input1 input2 input3 =>  ExecutablePlan.firstSuccess (Subtype_sub_ok'_clauses input0 input1 input2 input3) ()
  | @Call.«Subtype_sub_ok:rule:iter:0» input0 input1 input2 input3 =>  ExecutablePlan.firstSuccess («Subtype_sub_ok:rule:iter:0_clauses» input0 input1 input2 input3) ()
  | @Call.Subtype_sub_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Subtype_sub_ok_clauses input0 input1 input2) ()
  | @Call.«Rectype_ok:rule:iter:2» input0 input1 =>  ExecutablePlan.firstSuccess («Rectype_ok:rule:iter:2_clauses» input0 input1) ()
  | @Call.«Rectype_ok:rule:iter:5» input0 input1 =>  ExecutablePlan.firstSuccess («Rectype_ok:rule:iter:5_clauses» input0 input1) ()
  | @Call.«Rectype_ok:rule:iter:6» input0 input1 input2 input3 =>  ExecutablePlan.firstSuccess («Rectype_ok:rule:iter:6_clauses» input0 input1 input2 input3) ()
  | @Call.Rectype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Rectype_ok_clauses input0 input1) ()
  | @Call.Globaltype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Globaltype_ok_clauses input0 input1) ()
  | @Call.Tagtype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Tagtype_ok_clauses input0 input1) ()
  | @Call.Tabletype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Tabletype_ok_clauses input0 input1) ()
  | @Call.«$array_type» input0 input1 =>  ExecutablePlan.firstSuccess («$array_type_clauses» input0 input1) ()
  | @Call.«$struct_type» input0 input1 =>  ExecutablePlan.firstSuccess («$struct_type_clauses» input0 input1) ()
  | @Call.«$func_type» input0 input1 =>  ExecutablePlan.firstSuccess («$func_type_clauses» input0 input1) ()
  | @Call.Blocktype_ok input0 input1 =>  ExecutablePlan.firstSuccess (Blocktype_ok_clauses input0 input1) ()
  | @Call.Catch_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Catch_ok_clauses input0 input1 input2) ()
  | @Call.«Instr_ok:br_table:iter:4» input0 input1 input2 =>  ExecutablePlan.firstSuccess («Instr_ok:br_table:iter:4_clauses» input0 input1 input2) ()
  | @Call.«Instr_ok:try_table:iter:0» input0 input1 input2 =>  ExecutablePlan.firstSuccess («Instr_ok:try_table:iter:0_clauses» input0 input1 input2) ()
  | @Call.Instrs_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Instrs_ok_clauses input0 input1 input2) ()
  | @Call.Instr_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Instr_ok_clauses input0 input1 input2) ()
  | @Call.Block_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Block_ok_clauses input0 input1 input2) ()
  | @Call.Type_ok input0 input1 =>  ExecutablePlan.firstSuccess (Type_ok_clauses input0 input1) ()
  | @Call.Types_ok input0 input1 =>  ExecutablePlan.firstSuccess (Types_ok_clauses input0 input1) ()
  | @Call.Import_ok input0 input1 =>  ExecutablePlan.firstSuccess (Import_ok_clauses input0 input1) ()
  | @Call.Imports_ok input0 input1 =>  ExecutablePlan.firstSuccess (Imports_ok_clauses input0 input1) ()
  | @Call.Func_ok input0 input1 =>  ExecutablePlan.firstSuccess (Func_ok_clauses input0 input1) ()
  | @Call.Funcs_ok input0 input1 =>  ExecutablePlan.firstSuccess (Funcs_ok_clauses input0 input1) ()
  | @Call.Tag_ok input0 input1 =>  ExecutablePlan.firstSuccess (Tag_ok_clauses input0 input1) ()
  | @Call.Tags_ok input0 input1 =>  ExecutablePlan.firstSuccess (Tags_ok_clauses input0 input1) ()
  | @Call.Start_ok input0 input1 =>  ExecutablePlan.firstSuccess (Start_ok_clauses input0 input1) ()
  | @Call.Const_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Const_ok_clauses input0 input1 input2) ()
  | @Call.Table_ok input0 input1 =>  ExecutablePlan.firstSuccess (Table_ok_clauses input0 input1) ()
  | @Call.Tables_ok input0 input1 =>  ExecutablePlan.firstSuccess (Tables_ok_clauses input0 input1) ()
  | @Call.Global_ok input0 input1 =>  ExecutablePlan.firstSuccess (Global_ok_clauses input0 input1) ()
  | @Call.Globals_ok input0 input1 =>  ExecutablePlan.firstSuccess (Globals_ok_clauses input0 input1) ()
  | @Call.«Elem_ok:rule:iter:0» input0 input1 input2 =>  ExecutablePlan.firstSuccess («Elem_ok:rule:iter:0_clauses» input0 input1 input2) ()
  | @Call.Elemmode_ok input0 input1 input2 =>  ExecutablePlan.firstSuccess (Elemmode_ok_clauses input0 input1 input2) ()
  | @Call.Elem_ok input0 input1 =>  ExecutablePlan.firstSuccess (Elem_ok_clauses input0 input1) ()
  | @Call.Elems_ok input0 input1 =>  ExecutablePlan.firstSuccess (Elems_ok_clauses input0 input1) ()
  | @Call.Datamode_ok input0 input1 =>  ExecutablePlan.firstSuccess (Datamode_ok_clauses input0 input1) ()
  | @Call.Data_ok input0 input1 =>  ExecutablePlan.firstSuccess (Data_ok_clauses input0 input1) ()
  | @Call.Datas_ok input0 input1 =>  ExecutablePlan.firstSuccess (Datas_ok_clauses input0 input1) ()
  | @Call.Local_ok input0 input1 =>  ExecutablePlan.firstSuccess (Local_ok_clauses input0 input1) ()
  | @Call.«Funcbody_ok:rule:iter:1» input0 input1 =>  ExecutablePlan.firstSuccess («Funcbody_ok:rule:iter:1_clauses» input0 input1) ()
  | @Call.Funcbody_ok input0 input1 =>  ExecutablePlan.firstSuccess (Funcbody_ok_clauses input0 input1) ()
  | @Call.«Module_ok:rule:iter:2» input0 input1 =>  ExecutablePlan.firstSuccess («Module_ok:rule:iter:2_clauses» input0 input1) ()
  | @Call.Module_ok input0 =>  ExecutablePlan.firstSuccess (Module_ok_clauses input0) ()

def program : ExecutableProgram Call := ⟨body, fun _ _ => False⟩
end properties.wasm_module_ok.PositiveRuntime
