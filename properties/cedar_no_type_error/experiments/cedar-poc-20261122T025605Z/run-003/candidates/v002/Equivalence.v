Require Import String List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Import ListNotations.

Theorem equivalent : forall x : Original.Input,
  Property.candidates.v001.Candidate.predicate x <->
  Property.candidates.v002.Candidate.predicate x.
Proof.
  intro x; split.
  - intro H. apply Property.candidates.v002.Candidate.General. exact H.
  - intro H. destruct H as [id | i H].
    + eapply Property.candidates.v001.Candidate.Build.
      * apply WfS with (acts :=
          [(MkEntityUID (MkName "Action" []) id,
            MkActionSchemaEntry
              [MkName "EntityType1" []] [MkName "EntityType2" []] [])]).
        -- unfold Original.entity_names.
           apply WfETSCons.
           ++ apply DNFound. reflexivity.
           ++ apply NIECons.
              ** discriminate.
              ** apply NIENil.
           ++ apply WfETSingle; constructor.
           ++ apply WfETSSingle.
              ** apply DNRest.
                 --- discriminate.
                 --- apply DNFound. reflexivity.
              ** apply WfETSingle; constructor.
        -- apply WfACTSSingle. apply WfACTSingle.
           ++ unfold Original.entity_names.
              apply DNFound. reflexivity.
           ++ unfold Original.entity_names.
              apply DNRest.
              ** discriminate.
              ** apply DNFound. reflexivity.
           ++ apply WfAttrsNil.
        -- reflexivity.
      * apply ASTESingle. apply ASTRTSingle. apply ATRTSingle.
      * apply MkEnvsSingle.
      * apply WfBoolType.
      * apply TLitOther.
        -- discriminate.
        -- apply TTrue.
    + exact H.
Qed.
