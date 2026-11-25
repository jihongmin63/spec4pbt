From Coq Require Import List String Arith ZArith.
From ALCoq Require Import Execution Values.
From ALCoq.Builtins Require Import P4 Common.
From P4Spec.Generated Require Import Calls InductiveRelations.
Import ListNotations.
Open Scope string_scope.
Set Universe Polymorphism.

Definition returned {Call A} (action : Action Call A) : option A :=
  match action in Action _ T return option T with
  | Return value => Some value
  | _ => None
  end.

Lemma map_identity {A} (xs : list A) : map (fun x => x) xs = xs.
Proof. induction xs; simpl; congruence. Qed.

Lemma max_empty s o t :
  g_p4_dec_max_x5f_nat_execute [] s o t <-> o = Unmatch /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; cbn [P4.max_nat] in *;
      try discriminate; split; reflexivity.
  - intros [-> ->]. apply direct_case_4. reflexivity.
Qed.

Lemma max_nonempty x xs s o t :
  g_p4_dec_max_x5f_nat_execute (x :: xs) s o t <->
  o = Success (fold_left Nat.max xs x) /\ t = s.
Proof.
  split.
  - intro H. inversion H; subst; cbn [P4.max_nat] in *;
      try discriminate.
    rewrite map_identity in H0.
    apply (f_equal (@returned Call nat)) in H0. cbn in H0.
    injection H0 as E. subst. split; reflexivity.
  - intros [-> ->]. apply direct_case_3.
    cbn [P4.max_nat]. rewrite map_identity. reflexivity.
Qed.

Lemma text_direct input s o t :
  g_p4_dec_text_x5f_to_x5f_int_execute input s o t <->
  match parse_integer input with
  | Some value => o = Success value /\ t = s
  | None => o = Error {| error_kind := HostConversion;
                         error_detail := "Bigint.of_string" |} /\ t = s
  end.
Proof.
  destruct (parse_integer input) as [value|] eqn:parsed; split.
  - intro H. inversion H; subst; unfold P4.text_to_int, host_error in *;
      rewrite parsed in *; try discriminate.
    apply (f_equal (@returned Call Z)) in H0. cbn in H0.
    injection H0 as E. subst. split; reflexivity.
  - intros [-> ->]. apply direct_case_9.
    unfold P4.text_to_int. now rewrite parsed.
  - intro H. inversion H; subst; unfold P4.text_to_int, host_error in *;
      rewrite parsed in *; try discriminate.
    apply (f_equal (fun a => match a in Action _ T return option ExecutionError with
                            | Raise err => Some err | _ => None end)) in H0.
    cbn in H0. injection H0 as E. subst. split; reflexivity.
  - intros [-> ->]. apply direct_case_12.
    unfold P4.text_to_int, host_error. now rewrite parsed.
Qed.

Print Assumptions max_empty.
Print Assumptions max_nonempty.
Print Assumptions text_direct.
Print Assumptions map_identity.
