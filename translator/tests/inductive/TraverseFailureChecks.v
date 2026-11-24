From Coq Require Import String List Arith.
From ALCoq Require Import Execution Values.
From ALCoq.Builtins Require Import P4.
From P4Spec.Generated Require Import Calls Bodies_0000 Program InductiveRelations.
Import ListNotations.
Open Scope string_scope.

Definition state n : State := {| next_fresh := n |}.

Lemma first_step_succeeds :
  g_p4_dec_step_execute 0 (state 0) (Success 0) (state 1).
Proof.
  eapply direct_case_8.
  - apply direct_case_2; reflexivity.
  - apply direct_case_10; reflexivity.
Qed.

Lemma second_step_unmatches :
  g_p4_dec_step_execute 1 (state 1) Unmatch (state 2).
Proof.
  eapply direct_case_8.
  - apply direct_case_2; reflexivity.
  - apply direct_case_12. reflexivity.
Qed.

Lemma remaining_list_unmatches :
  g_p4_dec_each_x5f_step_traverse_1_at_1 [1; 2]
    (state 1) Unmatch (state 2).
Proof.
  eapply direct_case_24.
  - reflexivity.
  - apply second_step_unmatches.
  - apply direct_case_32.
Qed.

Lemma first_failure_stops_iteration :
  g_p4_dec_each_x5f_step_execute [0; 1; 2]
    (state 0) Unmatch (state 2).
Proof.
  apply direct_case_38.
  eapply direct_case_24.
  - reflexivity.
  - apply first_step_succeeds.
  - eapply direct_case_29. apply remaining_list_unmatches.
Qed.

Print Assumptions first_failure_stops_iteration.

Definition observation {A} (a : Action Call A) (s : State)
    (o : Outcome A) (t : State) : Prop :=
  match a in Action _ T return Outcome T -> Prop with
  | Return v => fun o => o = Success v /\ t = s
  | Fresh => fun o => o = Success (next_fresh s) /\ t = state (S (next_fresh s))
  | Invoke c => fun o => Eval (@Body) (Body c) s o t
  | Unmatched => fun o => o = Unmatch /\ t = s
  | Bind a k => fun o =>
      (exists v m, Eval (@Body) a s (Success v) m /\
        Eval (@Body) (k v) m o t) \/
      (o = Unmatch /\ Eval (@Body) a s Unmatch t) \/
      (exists err, o = Error err /\ Eval (@Body) a s (Error err) t)
  | OrElse a b => fun o =>
      (exists v, o = Success v /\ Eval (@Body) a s (Success v) t) \/
      (exists m, Eval (@Body) a s Unmatch m /\ Eval (@Body) b m o t) \/
      (exists err, o = Error err /\ Eval (@Body) a s (Error err) t)
  | _ => fun _ => True
  end o.

Lemma observe : forall (A : Set) (a : Action Call A) s o t,
  Eval (@Body) a s o t -> observation a s o t.
Proof. intros A a s o t H; destruct H; cbn; eauto 8. Qed.

Lemma return_value : forall (A : Set) (v : A) s o t,
  Eval (@Body) (Return v) s o t <-> o = Success v /\ t = s.
Proof.
  intros; split.
  - intro H. now apply observe in H.
  - intros [-> ->]. constructor.
Qed.

Lemma bind_cases : forall (A B : Set) (left : Action Call A)
    (right : A -> Action Call B) s o t,
  Eval (@Body) (Bind left right) s o t <->
    (exists value middle, Eval (@Body) left s (Success value) middle /\
       Eval (@Body) (right value) middle o t) \/
    (o = Unmatch /\ Eval (@Body) left s Unmatch t) \/
    (exists err, o = Error err /\ Eval (@Body) left s (Error err) t).
Proof.
  intros; split.
  - intro H. now apply observe in H.
  - intros [[value [middle [L R]]] | [[-> L] | [err [-> L]]]];
      eauto using eval_bind_success, eval_bind_unmatch, eval_bind_error.
Qed.

Lemma eval_step_action x s o t :
  Eval (@Body) (Bind (Return x)
      (fun value => Invoke (C_g_p4_dec_step value))) s o t <->
  Eval (@Body) (Invoke (C_g_p4_dec_step x)) s o t.
Proof.
  rewrite bind_cases. split.
  - intros [[value [middle [L R]]] | [[_ L] | [err [_ L]]]];
      apply return_value in L; destruct L as [V M]; try discriminate.
    inversion V; subst; exact R.
  - intro H. left. exists x, s. split; [apply return_value; auto | exact H].
Qed.

Lemma fresh_value s o t :
  Eval (@Body) Fresh s o t <->
  o = Success (next_fresh s) /\ t = state (S (next_fresh s)).
Proof. split; [intro H; now apply observe in H | intros [-> ->]; constructor]. Qed.

Lemma invoke_body : forall (A : Set) (c : Call A) s o t,
  Eval (@Body) (Invoke c) s o t <-> Eval (@Body) (Body c) s o t.
Proof. intros; split; [intro H; now apply observe in H | intro H; now constructor]. Qed.

Lemma unmatched_value : forall (A : Set) s (o : Outcome A) t,
  Eval (@Body) Unmatched s o t <-> o = Unmatch /\ t = s.
Proof. intros; split; [intro H; now apply observe in H | intros [-> ->]; constructor]. Qed.

Lemma or_cases : forall (A : Set) (a b : Action Call A) s o t,
  Eval (@Body) (OrElse a b) s o t <->
    (exists v, o = Success v /\ Eval (@Body) a s (Success v) t) \/
    (exists m, Eval (@Body) a s Unmatch m /\ Eval (@Body) b m o t) \/
    (exists err, o = Error err /\ Eval (@Body) a s (Error err) t).
Proof.
  intros; split.
  - intro H. now apply observe in H.
  - intros [[v [-> L]] | [[m [L R]] | [err [-> L]]]];
      eauto using eval_or_success, eval_or_unmatch, eval_or_error.
Qed.

Lemma bind_known {A B : Set} (a : Action Call A) (k : A -> Action Call B)
    (value : A) (middle : State) s o t :
  (forall outcome final,
      Eval (@Body) a s outcome final <->
      outcome = Success value /\ final = middle) ->
  Eval (@Body) (Bind a k) s o t <-> Eval (@Body) (k value) middle o t.
Proof.
  intro known. rewrite bind_cases. split.
  - intros [[v [m [L R]]] | [[_ L] | [err [_ L]]]];
      apply known in L; destruct L as [V M]; try discriminate.
    inversion V; subst; exact R.
  - intro H. left. exists value, middle. split; [apply known; auto | exact H].
Qed.

Lemma bind_return {A B : Set} (v : A) (k : A -> Action Call B) s o t :
  Eval (@Body) (Bind (Return v) k) s o t <-> Eval (@Body) (k v) s o t.
Proof.
  apply bind_known. intros outcome final. apply return_value.
Qed.

Lemma fresh_text_eval s o t :
  Eval (@Body) (@P4.fresh_typeId Call) s o t <->
  o = Success (String.append "FRESH__" (print_nat (next_fresh s))) /\
  t = state (S (next_fresh s)).
Proof.
  unfold P4.fresh_typeId. rewrite bind_known with
    (value := next_fresh s) (middle := state (S (next_fresh s))).
  - apply return_value.
  - intros outcome final. apply fresh_value.
Qed.

Lemma fresh_call_eval s o t :
  Eval (@Body) (Invoke C_g_p4_dec_fresh_x5f_typeId) s o t <->
  o = Success (String.append "FRESH__" (print_nat (next_fresh s))) /\
  t = state (S (next_fresh s)).
Proof.
  rewrite invoke_body.
  change (Eval (@Body)
    (Bind (@P4.fresh_typeId Call) (fun v : string => Return v)) s o t <->
    o = Success (String.append "FRESH__" (print_nat (next_fresh s))) /\
    t = state (S (next_fresh s))).
  rewrite bind_known with
    (value := String.append "FRESH__" (print_nat (next_fresh s)))
    (middle := state (S (next_fresh s))).
  - apply return_value.
  - intros outcome final. apply fresh_text_eval.
Qed.

Lemma bind_unmatched {A B : Set} (k : A -> Action Call B) s o t :
  Eval (@Body) (Bind Unmatched k) s o t <-> o = Unmatch /\ t = s.
Proof.
  rewrite bind_cases. split.
  - intros [[v [m [L _]]] | [[E L] | [err [E L]]]];
      apply unmatched_value in L; destruct L as [V T]; try discriminate.
    now subst.
  - intros [-> ->]. right. left. split; [reflexivity | constructor].
Qed.

Lemma or_unmatched_identity {A : Set} (a : Action Call A) s o t :
  Eval (@Body) (OrElse a Unmatched) s o t <-> Eval (@Body) a s o t.
Proof.
  rewrite or_cases. split.
  - intros [[v [E L]] | [[m [L R]] | [err [E L]]]]; subst.
    + exact L.
    + apply unmatched_value in R. destruct R as [E T]. subst. exact L.
    + exact L.
  - intro H. destruct o as [v | | err].
    + left. eexists. split; [reflexivity | exact H].
    + right. left. exists t. split; [exact H | constructor].
    + right. right. eexists. split; [reflexivity | exact H].
Qed.

Definition step_clause (n : nat) : Action Call nat :=
  Bind
    (Bind (Return "FRESH__0") (fun expected =>
      Bind (Invoke C_g_p4_dec_fresh_x5f_typeId) (fun actual =>
        Return (equal_value text_ops expected actual))))
    (fun text_ok => Bind (Guard text_ok) (fun _ =>
      Bind (Bind (Return n) (fun value =>
        Bind (Return 0%nat) (fun zero =>
          Return (equal_value nat_ops value zero))))
        (fun number_ok => Bind (Guard number_ok) (fun _ => Return n)))).

Definition step_result n s : Outcome nat :=
  if andb
      (equal_value text_ops "FRESH__0"
        (String.append "FRESH__" (print_nat (next_fresh s))))
      (equal_value nat_ops n 0%nat)
  then Success n else Unmatch.

Lemma step_clause_eval n s o t :
  Eval (@Body) (step_clause n) s o t <->
  o = step_result n s /\ t = state (S (next_fresh s)).
Proof.
  unfold step_clause, step_result.
  rewrite bind_known with
    (value := equal_value text_ops "FRESH__0"
      (String.append "FRESH__" (print_nat (next_fresh s))))
    (middle := state (S (next_fresh s))).
  2: {
    intros outcome final. rewrite bind_return.
    rewrite bind_known with
      (value := String.append "FRESH__" (print_nat (next_fresh s)))
      (middle := state (S (next_fresh s))).
    - apply return_value.
    - intros result final'. apply fresh_call_eval.
  }
  destruct (equal_value text_ops "FRESH__0"
    (String.append "FRESH__" (print_nat (next_fresh s)))) eqn:Etext;
    cbn [andb Guard].
  - rewrite bind_return.
    rewrite bind_known with (value := equal_value nat_ops n 0%nat)
      (middle := state (S (next_fresh s))).
    2: {
      intros outcome final. rewrite bind_return.
      rewrite bind_return. apply return_value.
    }
    destruct (equal_value nat_ops n 0%nat); cbn [Guard].
    + rewrite bind_return. apply return_value.
    + apply bind_unmatched.
  - apply bind_unmatched.
Qed.

Lemma step_eval n s o t :
  Eval (@Body) (Invoke (C_g_p4_dec_step n)) s o t <->
  o = step_result n s /\ t = state (S (next_fresh s)).
Proof.
  rewrite invoke_body.
  change (Eval (@Body) (OrElse (step_clause n) Unmatched) s o t <->
    o = step_result n s /\ t = state (S (next_fresh s))).
  rewrite or_unmatched_identity. apply step_clause_eval.
Qed.

Lemma step_direct n s o t :
  g_p4_dec_step_execute n s o t <->
  o = step_result n s /\ t = state (S (next_fresh s)).
Proof.
  destruct s as [counter]. split.
  - intro H. inversion H; subst; clear H.
    match goal with
    | F : g_p4_dec_fresh_x5f_typeId_execute _ _ _ |- _ =>
        inversion F; subst; clear F
    end.
    match goal with
    | A : g_p4_dec_step_after_call_1_at_1 _ _ _ _ _ _ |- _ =>
        inversion A; subst; clear A
    end;
      unfold g_p4_dec_fresh_x5f_typeId_fresh_text in *;
      unfold step_result; cbn [String.append next_fresh] in *;
      repeat match goal with
      | E : equal_value _ _ _ = _ |- _ => rewrite E
      end;
      cbn [andb]; split; reflexivity.
  - intros [-> ->]. unfold step_result. cbn [next_fresh].
    destruct (equal_value text_ops "FRESH__0"
      (String.append "FRESH__" (print_nat counter))) eqn:Etext;
      destruct (equal_value nat_ops n 0%nat) eqn:Enum;
      cbn [andb].
    all: eapply direct_case_8.
    all: try solve [apply direct_case_2; reflexivity].
    all: first [apply direct_case_10; assumption
               | apply direct_case_11; assumption
               | apply direct_case_12; assumption].
Qed.

Theorem step_equivalent n s o t :
  Eval (@Body) (Invoke (C_g_p4_dec_step n)) s o t <->
  g_p4_dec_step_execute n s o t.
Proof. rewrite step_eval, step_direct. reflexivity. Qed.

(* This isolates the Traverse translation: any proof of the called relation's
   equivalence lifts through every successful, Unmatch, and Error iteration,
   preserving the state at which evaluation stopped. *)
Theorem traverse_equivalent_given_step
    (step_equivalent : forall n s o t,
      Eval (@Body) (Invoke (C_g_p4_dec_step n)) s o t <->
      g_p4_dec_step_execute n s o t) :
  forall xs s o t,
    Eval (@Body)
      (Traverse (fun x : nat => Bind (Return x)
        (fun value => Invoke (C_g_p4_dec_step value))) xs) s o t <->
    g_p4_dec_each_x5f_step_traverse_1_at_1 xs s o t.
Proof.
  induction xs as [|x xs IH]; intros s o t; split; intro H.
  - cbn [Traverse] in H. apply return_value in H.
    destruct H as [-> ->]. constructor.
  - inversion H; subst. cbn [Traverse]. constructor.
  - cbn [Traverse] in H. apply bind_cases in H.
    destruct H as [[value [middle [L R]]] | [[-> L] | [err [-> L]]]].
    + apply eval_step_action in L. apply step_equivalent in L.
      apply bind_cases in R.
      destruct R as [[rest [final [R T]]] | [[-> R] | [err [-> R]]]].
      * apply return_value in T. destruct T as [V E]. inversion V; subst.
        eapply direct_case_24; [reflexivity | exact L | ].
        eapply direct_case_28. apply IH. exact R.
      * eapply direct_case_24; [reflexivity | exact L | ].
        eapply direct_case_29. apply IH. exact R.
      * eapply direct_case_24; [reflexivity | exact L | ].
        eapply direct_case_31. apply IH. exact R.
    + apply eval_step_action in L. apply step_equivalent in L.
      eapply direct_case_24; [reflexivity | exact L | constructor].
    + apply eval_step_action in L. apply step_equivalent in L.
      eapply direct_case_24; [reflexivity | exact L | constructor].
  - inversion H; subst; clear H.
    match goal with
    | A : g_p4_dec_each_x5f_step_after_call_1_at_1 _ _ _ _ _ |- _ =>
        inversion A; subst; clear A
    end.
    + apply bind_cases. left. eexists; eexists. split.
      * apply eval_step_action. apply step_equivalent; eassumption.
      * apply bind_cases. left. eexists; eexists. split.
        -- apply IH; eassumption.
        -- apply return_value. split; reflexivity.
    + apply bind_cases. left. eexists; eexists. split.
      * apply eval_step_action. apply step_equivalent; eassumption.
      * apply bind_cases. right. left. split.
        -- reflexivity.
        -- apply IH; eassumption.
    + apply bind_cases. left. eexists; eexists. split.
      * apply eval_step_action. apply step_equivalent; eassumption.
      * apply bind_cases. right. right. eexists. split.
        -- reflexivity.
        -- apply IH; eassumption.
    + apply bind_cases. right. left. split.
      * reflexivity.
      * apply eval_step_action. apply step_equivalent; eassumption.
    + apply bind_cases. right. right. eexists. split.
      * reflexivity.
      * apply eval_step_action. apply step_equivalent; eassumption.
Qed.

Lemma each_direct xs s o t :
  g_p4_dec_each_x5f_step_execute xs s o t <->
  g_p4_dec_each_x5f_step_traverse_1_at_1 xs s o t.
Proof.
  split.
  - intro H. inversion H; subst; assumption.
  - intro H. destruct o as [value | | err].
    + eapply direct_case_37. exact H.
    + eapply direct_case_38. exact H.
    + eapply direct_case_40. exact H.
Qed.

Lemma each_eval xs s o t :
  Eval (@Body) (Invoke (C_g_p4_dec_each_x5f_step xs)) s o t <->
  Eval (@Body)
    (Traverse (fun x : nat => Bind (Return x)
      (fun value => Invoke (C_g_p4_dec_step value))) xs) s o t.
Proof.
  rewrite invoke_body.
  change (Eval (@Body)
    (OrElse (Traverse (fun x : nat => Bind (Return x)
      (fun value => Invoke (C_g_p4_dec_step value))) xs) Unmatched)
    s o t <->
    Eval (@Body)
      (Traverse (fun x : nat => Bind (Return x)
        (fun value => Invoke (C_g_p4_dec_step value))) xs) s o t).
  apply or_unmatched_identity.
Qed.

Theorem each_equivalent xs s o t :
  Eval (@Body) (Invoke (C_g_p4_dec_each_x5f_step xs)) s o t <->
  g_p4_dec_each_x5f_step_execute xs s o t.
Proof.
  rewrite each_eval, each_direct.
  apply traverse_equivalent_given_step.
  exact step_equivalent.
Qed.

Corollary first_failure_eval :
  Eval (@Body) (Invoke (C_g_p4_dec_each_x5f_step [0; 1; 2]))
    (state 0) Unmatch (state 2).
Proof. apply each_equivalent. exact first_failure_stops_iteration. Qed.

Print Assumptions each_equivalent.
Print Assumptions first_failure_eval.
