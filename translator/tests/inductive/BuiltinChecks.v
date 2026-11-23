From Coq Require Import List String Arith ZArith.
From ALCoq Require Import Execution.
From ALCoq.Builtins Require Import P4 Common.
From P4Spec.Generated Require Import Calls Bodies_0000 Program InductiveRelations.
Import ListNotations.

Definition observation {A} (a : Action Call A) (s : State)
    (o : Outcome A) (t : State) : Prop :=
  match a in Action _ T return Outcome T -> Prop with
  | Return value => fun o => o = Success value /\ t = s
  | Unmatched => fun o => o = Unmatch /\ t = s
  | Raise err => fun o => o = Error err /\ t = s
  | Invoke call => fun o => Eval (@Body) (Body call) s o t
  | Bind left_action continuation => fun o =>
      (exists value middle, Eval (@Body) left_action s (Success value) middle /\
                            Eval (@Body) (continuation value) middle o t) \/
      (o = Unmatch /\ Eval (@Body) left_action s Unmatch t) \/
      (exists err, o = Error err /\ Eval (@Body) left_action s (Error err) t)
  | _ => fun _ => True
  end o.

Lemma observe : forall (A : Set) (a : Action Call A) s o t,
  Eval (@Body) a s o t -> observation a s o t.
Proof. intros A a s o t H; destruct H; cbn; eauto 8. Qed.

Lemma invoke_body : forall (A : Set) (call : Call A) s o t,
  Eval (@Body) (Invoke call) s o t <-> Eval (@Body) (Body call) s o t.
Proof.
  intros; split; [intro H; now apply observe in H | intro H; now constructor].
Qed.

Lemma bind_return_identity {A : Set} (a : Action Call A) s o t :
  Eval (@Body) (Bind a (fun x => Return x)) s o t <->
  Eval (@Body) a s o t.
Proof.
  split.
  - intro H. apply observe in H. cbn [observation] in H.
    destruct H as [[value [middle [L R]]] | [[-> L] | [err [-> L]]]].
    + apply observe in R. cbn [observation] in R.
      destruct R as [E T]. inversion E; subst; exact L.
    + exact L.
    + exact L.
  - intro H. destruct o as [value | | err].
    + eapply eval_bind_success; [exact H | constructor].
    + now apply eval_bind_unmatch.
    + now apply eval_bind_error.
Qed.

Lemma max_direct xs s o t :
  g_p4_dec_max_x5f_nat_execute xs s o t <->
  Eval (@Body) (@P4.max_nat Call (map (fun x => x) xs)) s o t.
Proof.
  split.
  - intro H. inversion H; subst; clear H;
      match goal with E : P4.max_nat _ = _ |- _ => rewrite E; constructor end.
  - intro H. destruct (map (fun x => x) xs) as [| head tail] eqn:E.
    + cbn [P4.max_nat] in H. apply observe in H.
      cbn [observation] in H. destruct H as [-> ->]. apply direct_case_4.
      unfold P4.max_nat. now rewrite E.
    + cbn [P4.max_nat] in H. apply observe in H.
      cbn [observation] in H. destruct H as [-> ->]. eapply direct_case_3.
      unfold P4.max_nat. now rewrite E.
Qed.

Theorem max_builtin_equivalent xs s o t :
  Eval (@Body) (Invoke (C_g_p4_dec_max_x5f_nat xs)) s o t <->
  g_p4_dec_max_x5f_nat_execute xs s o t.
Proof.
  rewrite invoke_body.
  cbn [Body].
  unfold B_g_p4_dec_max_x5f_nat.
  rewrite bind_return_identity.
  symmetry. apply max_direct.
Qed.

Lemma text_direct input s o t :
  g_p4_dec_text_x5f_to_x5f_int_execute input s o t <->
  Eval (@Body) (@P4.text_to_int Call input) s o t.
Proof.
  split.
  - intro H. inversion H; subst; clear H;
      match goal with E : P4.text_to_int _ = _ |- _ => rewrite E; constructor end.
  - intro H. destruct (parse_integer input) as [value |] eqn:E.
    + unfold P4.text_to_int in H. rewrite E in H. apply observe in H.
      cbn [observation] in H. destruct H as [-> ->]. eapply direct_case_9.
      unfold P4.text_to_int. now rewrite E.
    + unfold P4.text_to_int in H. rewrite E in H. unfold host_error in H.
      apply observe in H. cbn [observation] in H.
      destruct H as [-> ->]. eapply direct_case_12.
      unfold P4.text_to_int, host_error. now rewrite E.
Qed.

Theorem text_builtin_equivalent input s o t :
  Eval (@Body) (Invoke (C_g_p4_dec_text_x5f_to_x5f_int input)) s o t <->
  g_p4_dec_text_x5f_to_x5f_int_execute input s o t.
Proof.
  rewrite invoke_body. cbn [Body]. unfold B_g_p4_dec_text_x5f_to_x5f_int.
  rewrite bind_return_identity. symmetry. apply text_direct.
Qed.

Print Assumptions max_builtin_equivalent.
Print Assumptions text_builtin_equivalent.
