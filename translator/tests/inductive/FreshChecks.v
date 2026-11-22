From Coq Require Import String Arith.
From ALCoq Require Import Execution Values.
From ALCoq.Builtins Require Import P4.
From P4Spec.Generated Require Import Calls Bodies_0000 Program InductiveRelations Relations_0000.
Open Scope string_scope.

Definition state n : State := {| next_fresh := n |}.

Definition observation {A} (a : Action Call A) (s : State)
    (o : Outcome A) (t : State) : Prop :=
  match a in Action _ T return Outcome T -> Prop with
  | Return value => fun o => o = Success value /\ t = s
  | Fresh => fun o => o = Success (next_fresh s) /\ t = state (S (next_fresh s))
  | Invoke call => fun o => Eval (@Body) (Body call) s o t
  | Bind first_action continuation => fun o =>
      (exists value middle, Eval (@Body) first_action s (Success value) middle /\
                            Eval (@Body) (continuation value) middle o t) \/
      (o = Unmatch /\ Eval (@Body) first_action s Unmatch t) \/
      (exists err, o = Error err /\ Eval (@Body) first_action s (Error err) t)
  | _ => fun _ => True
  end o.

Lemma observe : forall (A : Set) (a : Action Call A) s o t,
  Eval (@Body) a s o t -> observation a s o t.
Proof. intros A a s o t H; destruct H; cbn; eauto 8. Qed.

Lemma return_value : forall (A : Set) (value : A) s o t,
  Eval (@Body) (Return value) s o t <-> o = Success value /\ t = s.
Proof. intros; split; [intro H; now apply observe in H | intros [-> ->]; constructor]. Qed.

Lemma fresh_value s o t :
  Eval (@Body) Fresh s o t <->
  o = Success (next_fresh s) /\ t = state (S (next_fresh s)).
Proof. split; [intro H; now apply observe in H | intros [-> ->]; constructor]. Qed.

Lemma invoke_body : forall (A : Set) (call : Call A) s o t,
  Eval (@Body) (Invoke call) s o t <-> Eval (@Body) (Body call) s o t.
Proof. intros; split; [intro H; now apply observe in H | intro H; now constructor]. Qed.

Lemma fresh_text_eval s o t :
  Eval (@Body) (@P4.fresh_typeId Call) s o t <->
  o = Success (String.append "FRESH__" (print_nat (next_fresh s))) /\
  t = state (S (next_fresh s)).
Proof.
  unfold P4.fresh_typeId. split.
  - intro H. apply observe in H. cbn [observation] in H.
    destruct H as [[value [middle [L R]]] | [[E L] | [err [E L]]]];
      apply fresh_value in L; destruct L as [V M]; try discriminate.
    inversion V; subst value middle. now apply return_value in R.
  - intros [-> ->]. eapply eval_bind_success.
    + apply eval_fresh.
    + apply eval_return.
Qed.

Lemma fresh_builtin_direct s o t :
  g_p4_dec_fresh_x5f_typeId_execute s o t <->
  o = Success (String.append "FRESH__" (print_nat (next_fresh s))) /\
  t = state (S (next_fresh s)).
Proof.
  split.
  - intro H. inversion H; subst; auto.
  - intros [-> ->]. constructor.
Qed.

Lemma fresh_builtin_eval s o t :
  Eval (@Body) (Invoke C_g_p4_dec_fresh_x5f_typeId) s o t <->
  o = Success (String.append "FRESH__" (print_nat (next_fresh s))) /\
  t = state (S (next_fresh s)).
Proof.
  rewrite invoke_body. cbn [Body B_g_p4_dec_fresh_x5f_typeId]. split.
  - intro H. apply observe in H. cbn [observation] in H.
    destruct H as [[value [middle [L R]]] | [[E L] | [err [E L]]]];
      apply fresh_text_eval in L; destruct L as [V M]; try discriminate.
    inversion V; subst value middle. now apply return_value in R.
  - intros [-> ->]. eapply eval_bind_success.
    + apply fresh_text_eval. split; reflexivity.
    + apply eval_return.
Qed.

Theorem fresh_builtin_equivalent s o t :
  Eval (@Body) (Invoke C_g_p4_dec_fresh_x5f_typeId) s o t <->
  g_p4_dec_fresh_x5f_typeId_execute s o t.
Proof. rewrite fresh_builtin_eval, fresh_builtin_direct. reflexivity. Qed.

Theorem failed_clause_consumes_fresh n s :
  g_p4_rel_Paths_execute n (state s)
    (Success (String.append "FRESH__" (print_nat (S s))))
    (state (S (S s))).
Proof.
  eapply direct_case_8.
  - apply direct_case_2.
  - eapply direct_case_13.
    + reflexivity.
    + eapply direct_case_24.
      * apply direct_case_2.
      * apply direct_case_26.
Qed.

Theorem public_paths_uses_direct n : g_p4_rel_Paths n "FRESH__1".
Proof.
  unfold g_p4_rel_Paths.
  exists (state 2).
  exact (failed_clause_consumes_fresh n 0).
Qed.

Print Assumptions failed_clause_consumes_fresh.
Print Assumptions public_paths_uses_direct.
Print Assumptions fresh_builtin_equivalent.
