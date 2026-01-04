Require Import Category.Lib.
From Category.Theory Require Import
  Category.
Require Import Category.Construction.Product.
Require Import Category.Facts.Setoid.
From Category.Instance Require PreOrder.

Generalizable All Variables.

(* TODO : Ex1. *)

Module Ex2. Section Ex2.
  Import PreOrder.
  Context `(P1 : @PreOrder X1 R1) `(P2 : @PreOrder X2 R2).

  Definition C : Category := P1 × P2.

  Lemma ex2 : @PreOrder C hom[C].
  Proof. construct; ss; intuition; etransitivity; eauto. Qed.
End Ex2. End Ex2.

Module Ex3. Section Ex3.
  (* Print ProductCategory. *)
  (* Print ProductFunctor. *)
  (* Check ProductFunctor_Unique. *)
End Ex3. End Ex3.

(* TODO : Ex4. *)

(* TODO : Ex5. *)