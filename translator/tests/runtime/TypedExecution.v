From Coq Require Import String List Arith.
From ALCoq Require Import Execution.
Import ListNotations.
Open Scope string_scope.

(* These cases catch fallback after success/error, state rollback, and
   treating an extern output as a deterministic default. *)
Inductive Ref := PlusOne | ThroughMutual.
Inductive TestCall : Type -> Type :=
| GetNat : TestCall nat
| GetText : TestCall string
| MutualLeft : nat -> TestCall nat
| MutualRight : nat -> TestCall nat
| ApplyRef : Ref -> nat -> TestCall nat.

Definition testBody {A} (c : TestCall A) : Action TestCall A :=
  match c in TestCall T return Action TestCall T with
  | GetNat => Return 7
  | GetText => Return "typed"
  | MutualLeft n => match n with
                   | O => Return 10
                   | S k => Invoke (MutualRight k)
                   end
  | MutualRight n => match n with
                    | O => Return 20
                    | S k => Invoke (MutualLeft k)
                    end
  | ApplyRef r n => match r with
                    | PlusOne => Return (S n)
                    | ThroughMutual => Invoke (MutualLeft n)
                    end
  end.
Definition s0 := {| next_fresh := 0 |}.
Definition s1 := {| next_fresh := 1 |}.
Definition err := {| error_kind := ALAbort; error_detail := "stop" |}.
Definition run {A} := @Eval TestCall (@testBody) A.

Example nat_result : run (Invoke GetNat) s0 (Success 7) s0.
Proof. apply eval_invoke. apply eval_return. Qed.
Example text_result : run (Invoke GetText) s0 (Success "typed") s0.
Proof. apply eval_invoke. apply eval_return. Qed.
Example mutual_recursion : run (Invoke (MutualLeft 2)) s0 (Success 10) s0.
Proof. repeat apply eval_invoke. apply eval_return. Qed.
Example callback_identity : run (Invoke (ApplyRef ThroughMutual 1)) s0 (Success 20) s0.
Proof. repeat apply eval_invoke. apply eval_return. Qed.

Example first_success : run (OrElse (Return 1) (Return 9)) s0 (Success 1) s0.
Proof. apply eval_or_success. apply eval_return. Qed.
Example no_second_success : ~ run (OrElse (Return 1) (Return 9)) s0 (Success 9) s0.
Proof. intro H. pose proof (eval_alternative_terminal H) as impossible. discriminate impossible. Qed.
Example only_unmatch_falls_back :
  run (OrElse (Unmatched : Action TestCall nat) (Return 9)) s0 (Success 9) s0.
Proof. eapply eval_or_unmatch; constructor. Qed.
Example errors_propagate :
  run (OrElse (Raise err : Action TestCall nat) (Return 9)) s0 (Error err) s0.
Proof. apply eval_or_error. constructor. Qed.
Example error_blocks_otherwise :
  ~ run (OrElse (Raise err : Action TestCall nat) (Return 9)) s0 (Success 9) s0.
Proof. intro H. pose proof (eval_alternative_terminal H) as impossible. discriminate impossible. Qed.
Example fresh_not_rolled_back :
  run (OrElse (Bind Fresh (fun _ => Unmatched)) Fresh) s0 (Success 1) {| next_fresh := 2 |}.
Proof.
  eapply eval_or_unmatch with (middle := s1).
  - eapply eval_bind_success with (value := 0) (middle := s1); constructor.
  - constructor.
Qed.
Example extern_zero : run (Choose : Action TestCall nat) s0 (Success 0) s0.
Proof. constructor. Qed.
Example extern_seven : run (Choose : Action TestCall nat) s0 (Success 7) s0.
Proof. constructor. Qed.
Example negate_success : run (Negate (Return 3)) s0 Unmatch s0.
Proof. eapply eval_negate_success. constructor. Qed.
Example negate_unmatch : run (Negate (Unmatched : Action TestCall nat)) s0 (Success tt) s0.
Proof. apply eval_negate_unmatch. constructor. Qed.
Example negate_error : run (Negate (Raise err : Action TestCall nat)) s0 (Error err) s0.
Proof. apply eval_negate_error. constructor. Qed.
(* Failed arguments must not enter the negated invocation. *)
Example negation_argument_failure :
  run (Bind (Unmatched : Action TestCall nat) (fun n => Negate (Invoke (MutualLeft n))))
      s0 Unmatch s0.
Proof. apply eval_bind_unmatch. constructor. Qed.
Print Assumptions first_success.
Print Assumptions fresh_not_rolled_back.
Print Assumptions callback_identity.
