(** Executable semantics for Prelude.replicate on the translated Int domain.
    The upstream GHC.List version depends on opaque natlike_rec2 and cannot
    supply executable fuel. Relating this bridge to machine Int remains a
    library correspondence obligation, separate from generator correctness. *)
From Stdlib Require Import ZArith List.

Definition replicate {A : Type} (count : Z) (value : A) : list A :=
  List.repeat value (Z.to_nat count).
