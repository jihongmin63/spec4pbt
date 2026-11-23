From Coq Require Import String List.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.

Record State := { next_fresh : nat }.
Inductive ErrorKind := ALAbort | ExternalAbort | HostConversion | HostInvalidArgument | StructureError | NumericTrap.
Record ExecutionError := { error_kind : ErrorKind; error_detail : string }.
Inductive Outcome (A : Type) :=
| Success : A -> Outcome A
| Unmatch : Outcome A
| Error : ExecutionError -> Outcome A.
Arguments Success {A} _.
Arguments Unmatch {A}.
Arguments Error {A} _.

(* Recursive source calls are data. In particular, Call never contains an Eval
   proof, a fuel bound, or an arbitrary equality on Coq functions. *)
Inductive Action (Call : Type -> Type) : Type -> Type :=
| Return : forall A, A -> Action Call A
| Invoke : forall A, Call A -> Action Call A
| Bind : forall A B, Action Call A -> (A -> Action Call B) -> Action Call B
| OrElse : forall A, Action Call A -> Action Call A -> Action Call A
| Unmatched : forall A, Action Call A
| Raise : forall A, ExecutionError -> Action Call A
| Fresh : Action Call nat
| Choose : forall A, Action Call A
| Negate : forall A, Action Call A -> Action Call unit.
Arguments Return {Call A} _.
Arguments Invoke {Call A} _.
Arguments Bind {Call A B} _ _.
Arguments OrElse {Call A} _ _.
Arguments Unmatched {Call A}.
Arguments Raise {Call A} _.
Arguments Fresh {Call}.
Arguments Choose {Call A}.
Arguments Negate {Call A} _.

Section Evaluation.
  Context {Call : Type -> Type}.
  Variable Body : forall A, Call A -> Action Call A.

  (* Only an explicit Unmatch enables another clause. Local bindings are the
     continuations themselves; State carries only the fresh counter. *)
  Inductive Eval : forall A, Action Call A -> State -> Outcome A -> State -> Prop :=
  | eval_return : forall A (value : A) state,
      Eval (Return value) state (Success value) state
  | eval_invoke : forall A (call : Call A) before outcome after,
      Eval (Body call) before outcome after ->
      Eval (Invoke call) before outcome after
  | eval_bind_success : forall A B (left : Action Call A) (right : A -> Action Call B)
                               before middle after value outcome,
      Eval left before (Success value) middle ->
      Eval (right value) middle outcome after ->
      Eval (Bind left right) before outcome after
  | eval_bind_unmatch : forall A B (left : Action Call A) (right : A -> Action Call B) before after,
      Eval left before Unmatch after -> Eval (Bind left right) before Unmatch after
  | eval_bind_error : forall A B (left : Action Call A) (right : A -> Action Call B) before after err,
      Eval left before (Error err) after -> Eval (Bind left right) before (Error err) after
  | eval_or_success : forall A (left right : Action Call A) before after value,
      Eval left before (Success value) after ->
      Eval (OrElse left right) before (Success value) after
  | eval_or_unmatch : forall A (left right : Action Call A) before middle after outcome,
      Eval left before Unmatch middle -> Eval right middle outcome after ->
      Eval (OrElse left right) before outcome after
  | eval_or_error : forall A (left right : Action Call A) before after err,
      Eval left before (Error err) after -> Eval (OrElse left right) before (Error err) after
  | eval_unmatched : forall A state, Eval (@Unmatched Call A) state Unmatch state
  | eval_raise : forall A err state, Eval (@Raise Call A err) state (Error err) state
  | eval_fresh : forall state,
      Eval Fresh state (Success (next_fresh state)) {| next_fresh := S (next_fresh state) |}
  | eval_choose : forall A (value : A) state, Eval Choose state (Success value) state
  | eval_negate_success : forall A (action : Action Call A) before after value,
      Eval action before (Success value) after -> Eval (Negate action) before Unmatch after
  | eval_negate_unmatch : forall A (action : Action Call A) before after,
      Eval action before Unmatch after -> Eval (Negate action) before (Success tt) after
  | eval_negate_error : forall A (action : Action Call A) before after err,
      Eval action before (Error err) after -> Eval (Negate action) before (Error err) after.
End Evaluation.
Arguments Eval {Call} Body {A} _ _ _ _.

Definition Guard {Call} (condition : bool) : Action Call unit :=
  if condition then Return tt else Unmatched.
Fixpoint Alternatives {Call A} (actions : list (Action Call A)) : Action Call A :=
  match actions with [] => Unmatched | action :: rest => OrElse action (Alternatives rest) end.
Fixpoint Traverse {Call A B} (f : A -> Action Call B) (xs : list A) : Action Call (list B) :=
  match xs with
  | [] => Return []
  | x :: rest => Bind (f x) (fun y => Bind (Traverse f rest) (fun ys => Return (y :: ys)))
  end.
Definition Holds {Call A} (Body : forall T, Call T -> Action Call T)
    (call : Call A) (result : A) : Prop :=
  exists final, Eval Body (Invoke call) {| next_fresh := 0 |} (Success result) final.

(* Dependent inversion over a Type-indexed Action otherwise exposes equality of
   sigma packages. These observation lemmas avoid any UIP/functional extensionality
   assumption: their motive follows the action's actual result type. *)
Definition terminal_constraint {Call A} (action : Action Call A) : Outcome A -> Prop :=
  match action in Action _ T return Outcome T -> Prop with
  | Return value => fun outcome => outcome = Success value
  | Raise err => fun outcome => outcome = Error err
  | _ => fun _ => True
  end.
Lemma eval_terminal {Call} (Body : forall T, Call T -> Action Call T)
    A (action : Action Call A) before outcome after :
  Eval Body action before outcome after -> terminal_constraint action outcome.
Proof. intro H. destruct H; cbn; auto. Qed.
Definition alternative_constraint {Call A} (action : Action Call A) : Outcome A -> Prop :=
  match action in Action _ T return Outcome T -> Prop with
  | OrElse first_action _ => terminal_constraint first_action
  | _ => fun _ => True
  end.
Lemma eval_alternative_terminal {Call} (Body : forall T, Call T -> Action Call T)
    A (action : Action Call A) before outcome after :
  Eval Body action before outcome after -> alternative_constraint action outcome.
Proof.
  intro H. destruct H; cbn; try exact I.
  - now apply (eval_terminal H).
  - pose proof (eval_terminal H) as constraint.
    destruct left; cbn in *; try exact I; discriminate.
  - now apply (eval_terminal H).
Qed.
