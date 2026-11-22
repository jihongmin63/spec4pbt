From Coq Require Import Arith List.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import Calls Program.
Import ListNotations.

Definition state n := {| next_fresh := n |}.

Definition observation {A} (a : Action Call A) (s : State)
    (o : Outcome A) (t : State) : Prop :=
  match a in Action _ T return Outcome T -> Prop with
  | Return v => fun o => o = Success v /\ t = s
  | Fresh => fun o => o = Success (next_fresh s) /\ t = state (S (next_fresh s))
  | Unmatched => fun o => o = Unmatch /\ t = s
  | Invoke c => fun o => Eval (@Body) (Body c) s o t
  | Bind l r => fun o =>
      (exists v m, Eval (@Body) l s (Success v) m /\ Eval (@Body) (r v) m o t) \/
      (o = Unmatch /\ Eval (@Body) l s Unmatch t) \/
      (exists e, o = Error e /\ Eval (@Body) l s (Error e) t)
  | OrElse l r => fun o =>
      (exists v, o = Success v /\ Eval (@Body) l s (Success v) t) \/
      (exists m, Eval (@Body) l s Unmatch m /\ Eval (@Body) r m o t) \/
      (exists e, o = Error e /\ Eval (@Body) l s (Error e) t)
  | Negate inner => fun o =>
      (o = Unmatch /\ exists v, Eval (@Body) inner s (Success v) t) \/
      (o = Success tt /\ Eval (@Body) inner s Unmatch t) \/
      (exists e, o = Error e /\ Eval (@Body) inner s (Error e) t)
  | _ => fun _ => True
  end o.

Lemma observe : forall (A : Set) (a : Action Call A) s o t,
  Eval (@Body) a s o t -> observation a s o t.
Proof. intros A a s o t H; destruct H; cbn; eauto 8. Qed.

Lemma return_value : forall (A : Set) (v : A) s o t,
  Eval (@Body) (Return v) s o t <-> o = Success v /\ t = s.
Proof. intros; split; [intro H; now apply observe in H | intros [-> ->]; constructor]. Qed.

Lemma raise_value : forall (A : Set) err s (o : Outcome A) t,
  Eval (@Body) (Raise err) s o t <-> o = Error err /\ t = s.
Proof.
  intros; split.
  - intro H. inversion H; subst; auto.
  - intros [-> ->]. constructor.
Qed.

Lemma unmatched_value : forall (A : Set) s (o : Outcome A) t,
  Eval (@Body) Unmatched s o t <-> o = Unmatch /\ t = s.
Proof.
  intros; split.
  - intro H. inversion H; subst; auto.
  - intros [-> ->]. constructor.
Qed.

Lemma invoke_body : forall (A : Set) (c : Call A) s o t,
  Eval (@Body) (Invoke c) s o t <-> Eval (@Body) (Body c) s o t.
Proof. intros; split; [intro H; now apply observe in H | intro H; now constructor]. Qed.

Lemma bind_return : forall (A B : Set) (v : A) (k : A -> Action Call B) s o t,
  Eval (@Body) (Bind (Return v) k) s o t <-> Eval (@Body) (k v) s o t.
Proof.
  intros; split.
  - intro H; apply observe in H; cbn [observation] in H.
    destruct H as [[v0 [m [L R]]] | [[E L] | [e [E L]]]];
      apply return_value in L; destruct L as [V M].
    + inversion V; subst v0; subst m; exact R.
    + discriminate V.
    + discriminate V.
  - intro H. eapply eval_bind_success; [apply eval_return | exact H].
Qed.

Lemma bind_cases : forall (A B : Set) (l : Action Call A)
    (r : A -> Action Call B) s o t,
  Eval (@Body) (Bind l r) s o t <->
  (exists v m, Eval (@Body) l s (Success v) m /\ Eval (@Body) (r v) m o t) \/
  (o = Unmatch /\ Eval (@Body) l s Unmatch t) \/
  (exists e, o = Error e /\ Eval (@Body) l s (Error e) t).
Proof.
  intros; split; [intro H; now apply observe in H | ].
  intros [[v [m [L R]]] | [[-> L] | [e [-> L]]]];
    eauto using eval_bind_success, eval_bind_unmatch, eval_bind_error.
Qed.

Lemma or_cases : forall (A : Set) (l r : Action Call A) s o t,
  Eval (@Body) (OrElse l r) s o t <->
  (exists v, o = Success v /\ Eval (@Body) l s (Success v) t) \/
  (exists m, Eval (@Body) l s Unmatch m /\ Eval (@Body) r m o t) \/
  (exists e, o = Error e /\ Eval (@Body) l s (Error e) t).
Proof.
  intros; split; [intro H; now apply observe in H | ].
  intros [[v [-> L]] | [[m [L R]] | [e [-> L]]]];
    eauto using eval_or_success, eval_or_unmatch, eval_or_error.
Qed.

Lemma or_left_success : forall (A : Set) (left right : Action Call A)
    (value : A) s o t,
  (forall result final,
    Eval (@Body) left s result final <-> result = Success value /\ final = s) ->
  Eval (@Body) (OrElse left right) s o t <-> o = Success value /\ t = s.
Proof.
  intros A left right value s o t left_value; split.
  - intro H. apply or_cases in H.
    destruct H as [[v [-> H]] | [[middle [H _]] | [e [-> H]]]].
    + apply left_value in H. destruct H as [V T]. now inversion V; subst.
    + apply left_value in H. destruct H as [V _]. discriminate V.
    + apply left_value in H. destruct H as [V _]. discriminate V.
  - intros [-> ->]. apply eval_or_success. apply left_value.
    split; reflexivity.
Qed.

Lemma or_left_error : forall (A : Set) (left right : Action Call A)
    (err : ExecutionError) s o t,
  (forall result final,
    Eval (@Body) left s result final <-> result = Error err /\ final = s) ->
  Eval (@Body) (OrElse left right) s o t <-> o = Error err /\ t = s.
Proof.
  intros A left right err s o t left_value; split.
  - intro H. apply or_cases in H.
    destruct H as [[v [-> H]] | [[middle [H _]] | [e [-> H]]]].
    + apply left_value in H. destruct H as [V _]. discriminate V.
    + apply left_value in H. destruct H as [V _]. discriminate V.
    + apply left_value in H. destruct H as [V T]. now inversion V; subst.
  - intros [-> ->]. apply eval_or_error. apply left_value.
    split; reflexivity.
Qed.

Lemma or_left_unmatch : forall (A : Set) (left right : Action Call A) s o t,
  (forall result final,
    Eval (@Body) left s result final <-> result = Unmatch /\ final = s) ->
  Eval (@Body) (OrElse left right) s o t <-> Eval (@Body) right s o t.
Proof.
  intros A left right s o t left_value; split.
  - intro H. apply or_cases in H.
    destruct H as [[v [_ H]] | [[middle [H R]] | [e [_ H]]]].
    + apply left_value in H. destruct H as [V _]. discriminate V.
    + apply left_value in H. destruct H as [_ T]. now subst middle.
    + apply left_value in H. destruct H as [V _]. discriminate V.
  - intro H. eapply eval_or_unmatch.
    + apply left_value. split; reflexivity.
    + exact H.
Qed.

Lemma bind_unmatched : forall (A B : Set) (k : A -> Action Call B) s o t,
  Eval (@Body) (Bind Unmatched k) s o t <-> o = Unmatch /\ t = s.
Proof.
  intros. rewrite bind_cases. split.
  - intros [[v [m [L _]]] | [[E L] | [e [E L]]]];
      apply unmatched_value in L; destruct L as [V T]; try discriminate.
    now subst.
  - intros [-> ->]. right. left. split; [reflexivity | constructor].
Qed.

Lemma negate_unmatched : forall (A : Set) (inner : Action Call A) s o t,
  (forall result final,
    Eval (@Body) inner s result final <-> result = Unmatch /\ final = s) ->
  Eval (@Body) (Negate inner) s o t <-> o = Success tt /\ t = s.
Proof.
  intros A inner s o t only_unmatch. split.
  - intro H. apply observe in H. cbn [observation] in H.
    destruct H as [[_ [v H]] | [[E H] | [e [_ H]]]];
      apply only_unmatch in H; destruct H as [V T]; try discriminate.
    now split.
  - intros [-> ->]. apply eval_negate_unmatch.
    apply only_unmatch. split; reflexivity.
Qed.
