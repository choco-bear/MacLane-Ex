Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Morphisms.
Require Import Category.Facts.Setoid.
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

Module Ex6. Section Ex6.
  Import Sets.
  (* Check Idempotent_Split. *)
End Ex6. End Ex6.

Module Ex7. Section Ex7.
  (* Check has_right_inverse_regular. *)
  (* Check has_left_inverse_regular. *)
  (* Check from_nonempty_is_regular. *)
End Ex7. End Ex7.

Module Ex8. Section Ex8.
  Import Sets.

  Record CObj :=
    { X :> Sets 
    ; e : X 
    ; t : X ~> X
    
    ; CObj_to_type :> Type := X : Type
    }.
  Arguments e {c}.
  Arguments t {c}.

  Record CHom (X X' : CObj) :=
    { f :> X ~{Sets}~> X'
    ; proper_e : f e ≡ e
    ; natural : f ∘ t ≡ t ∘ f

    ; CHom_to_fun :> X → X' := f : X → X'
    }.
  Arguments f {X X'}.

  Program Instance CHom_Setoid {X X' : CObj}
    : Setoid (CHom X X') := {| equiv := λ φ ψ, ∀ x, φ x ≡ ψ x |}.
  Next Obligation. by equivalence; etransitivity. Qed.

  Program Definition CHom_id {X : CObj} : CHom X X := {| f := SetoidMorphism_id |}.

  Program Definition CHom_compose {X Y Z : CObj} (φ : CHom Y Z) (ψ : CHom X Y)
    : CHom X Z := {| f := SetoidMorphism_compose (f φ) (f ψ) |}.
  Next Obligation. now rewrite !proper_e. Qed.
  Next Obligation. now rewrite (@natural X0 Y ψ a), (@natural Y Z φ (ψ a)). Qed.

  Program Definition C : Category :=
    {|  obj := CObj
      ; hom := CHom

      ; id      := @CHom_id
      ; compose := @CHom_compose
    |}.
  Next Obligation. (* TODO *) Admitted.
  Next Obligation. (* TODO *) Admitted.
  Next Obligation. (* TODO *) Admitted.
  Next Obligation. (* TODO *) Admitted.
  Next Obligation. (* TODO *) Admitted.

  (* TODO : {| X := nat_setoid ; e := O ; t := {| morphism := S |} |} is initial. *)
End Ex8. End Ex8.

(* TODO : Ex9. *)