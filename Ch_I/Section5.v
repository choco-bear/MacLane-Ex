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

Module Ex2. Section Ex2.
  (* Check monic_compose. *)
  (* Check epic_compose. *)
End Ex2. End Ex2.

Module Ex3. Section Ex3.
  Import Sets.

  (* Check monic_erase. *)

  Local Notation "'{*}'" := (unit_setoid : Sets).
  Local Notation "'ℕ'" := (eq_Setoid nat : Sets).
  Program Definition f : ℕ ~> {*} := {| morphism := λ _, ttt |}.
  Program Definition g : {*} ~> ℕ := {| morphism := λ _, 0%nat |}.
  Program Definition h : {*} ~> ℕ := {| morphism := λ _, 1%nat |}.

  Lemma Ex3 : Monic (f ∘ g) ∧ ¬ Monic f.
  Proof.
    split.
    - construct. now destruct (g1 a), (g2 a).
    - ii. pose (monic _ g h). assert (¬ g ≡ h).
      { intro. pose (X0 ttt); inversion e0. }
      now apply X0, e.
  Qed.
End Ex3. End Ex3.

(* TODO : Ex4. *)

(* TODO : Ex5. *)

(* TODO : Ex6. *)

(* TODO : Ex7. *)

(* TODO : Ex8. *)

(* TODO : Ex9. *)