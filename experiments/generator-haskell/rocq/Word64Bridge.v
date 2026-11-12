(** Manually supplied semantics for the two wrapping Word64 operations used by
    Generator.hs. The supported generator inputs keep all other Word64 operands
    in [0, 2^64); GHC's finite-word representation is mapped to binary naturals.
    This bridge is executable library code, not a translator equivalence proof. *)
From Stdlib Require Import NArith.

Definition Word64 : Type := N.
Definition modulus : N := 18446744073709551616%N.
Definition add (left right : Word64) : Word64 :=
  N.modulo (N.add left right) modulus.
Definition multiply (left right : Word64) : Word64 :=
  N.modulo (N.mul left right) modulus.
