Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Functor.Setoid
  Functor.Cat
  Functor.Curry.
(* From Category.Facts Require . *)
From Category.Construction Require Product Fun Opposite.
From Category.Instance Require Cat.

Generalizable All Variables.
Set Universe Polymorphism.

Notation "'NatId'" := NaturalTransform_id (at level 0, only parsing) : natural_scope.
Notation "'NatId[' F ']'" :=
  (@NaturalTransform_id _ _ F%functor) (at level 0, format "NatId[ F ]") : natural_scope.
Notation "'NatId{' C '⟶' D '}[' F ']'" :=
  (@NaturalTransform_id C%category D%category F%functor) (at level 0, only parsing) : natural_scope.

(* TODO : Ex1. *)
Module Ex1. Section Ex1.
  Import Product Fun Instance.Cat Construction.Opposite.
  
  Notation "'Cat(A×B,C)'" := (Fun[-,-] ◯ (↥(-×-) ◯ Fst × Snd)).
  Notation "'Cat(A,C^B)'" := (Fun[-,-] ◯ (Fst ◯ Fst × (Fun[-,-] ◯ (Snd ◯ Fst × Snd)))).

  Obligation Tactic := idtac.
  Program Definition NatCurry : Cat(A×B,C) ⟹ Cat(A,C^B) :=
    {| component := λ`(a,b,c) : obj[Cat^op × Cat^op × Cat], @CurryFunctor a b c |}.
  Next Obligation.
    Fail timeout 10 cat_simpl. (* WTF? *)
    Fail timeout 1 (ss; simplify; ss). (* Even this fails. *)
    timeout 2 (ss; simplify; ss). (* But this succeeds. *)
  Admitted.

  Theorem ex1 : Cat(A×B,C) ≅[Fun[Cat^op × Cat^op × Cat, Cat]] Cat(A,C^B).
  Proof.
    construct.
    - natural_transform; simplify.
      + do 2 cat. srapply FromAFunctor; try exact curry. construct.
        * 
  Admitted.
End Ex1. End Ex1.

(* TODO : Ex2. *)

(* TODO : Ex3. *)

(* TODO : Ex4. *)

(* TODO : Ex5. *)

(* TODO : Ex6. *)