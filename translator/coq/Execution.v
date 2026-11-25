From Coq Require Import String List.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.

Record State := { next_fresh : nat }.
Inductive ErrorKind := ALAbort | ExternalAbort | HostConversion | HostInvalidArgument | StructureError | NumericTrap.
Record ExecutionError := { error_kind : ErrorKind; error_detail : string }.
(* The Testing Theorems tactic cannot reify a universe-polymorphic Outcome
   premise: it emits an undeclared universe for even a concrete Outcome nat.
   Outcome has no need for universe polymorphism; keep the rest of this runtime
   polymorphic for builtin Action results. *)
Unset Universe Polymorphism.
Inductive Outcome (A : Type) :=
| Success : A -> Outcome A
| Unmatch : Outcome A
| Error : ExecutionError -> Outcome A.
Arguments Success {A} _.
Arguments Unmatch {A}.
Arguments Error {A} _.
Set Universe Polymorphism.

(* Builtin results still use Action; direct relations inspect its Return and
   error constructors. *)
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
