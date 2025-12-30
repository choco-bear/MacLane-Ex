Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Morphisms.
From Category.Instance Require Two Sets Grp.

Generalizable All Variables.

Module Ex1. Section Ex1.
  Import Two.

  Lemma Epic_TwoF : Epic (TwoF : TwoA ~{_2}~> TwoB).
  Proof.
    construct; destruct z; auto with two_laws.
    now rewrite (TwoHom_inv g1), (TwoHom_inv g2).
  Qed.

  Lemma Monic_TwoF : Monic (TwoF : TwoA ~{_2}~> TwoB).
  Proof.
    construct; destruct z; auto with two_laws.
    now rewrite (TwoHom_inv g1), (TwoHom_inv g2).
  Qed.

  Lemma TwoF_has_no_inverse
    : ¬ (∃ f : TwoB ~{_2}~> TwoA, f ∘ TwoF ≡ id).
  Proof. intros [f _]. exact (TwoHom_inv f). Qed.
End Ex1. End Ex1.

(* TODO : Ex2. *)

(* TODO : Ex3. *)

(* TODO : Ex4. *)

(* TODO : Ex5. *)

(* TODO : Ex6. *)

(* TODO : Ex7. *)

(* TODO : Ex8. *)

(* TODO : Ex9. *)