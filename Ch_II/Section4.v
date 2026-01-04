Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Functor
  Natural.
Require Import Category.Construction.Fun.
From Category.Instance Require PreOrder.

Generalizable All Variables.

(* TODO : Ex1. *)

(* TODO : Ex2. *)

(* TODO : Ex3. *)

Module Ex4. Section Ex4.
  Import PreOrder.
  Context `(P : @PreOrder X R) `{S : crelation Y} (Q : @PreOrder Y S).

  Lemma ex4 : PreOrder (hom[Fun[P,Q]]).
  Proof.
    construct; ss; natural_transform; ss.
    etransitivity; [apply X0|apply X1].
  Qed.
End Ex4. End Ex4.

(* TODO : Ex5. *)

(* TODO : Ex6. *)

(* TODO : Ex7. *)

(* TODO : Ex8. *)