Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Isomorphism
  Functor
  Natural.
From Category.Construction Require Product Fun.
From Category.Instance Require PreOrder Discrete Cat.

Generalizable All Variables.

(* TODO : Ex1. *)

Module Ex2. Section Ex2.
  Import Fun Product Discrete Cat.
  Context (B : Category) (X : Type) {FIN : FinType X}.

  Lemma ex2 : Fun[Cat[X],B] ≅[Cat] ∏ (λ x : X, B).
    isomorphism.
    - apply ProductFunctor. i. construct; [exact (X0 i)|exact (f i)|..]; cat.
    - s. srapply (@FromAFunctor _ _ (λ F, _)).
      { exact (Functor_from_function F). }
      by construct; try natural_transform; ss; subst.
    - cat.
    - by cat; try isomorphism; try natural_transform; ss; subst.
  Qed.
End Ex2. End Ex2.

(* TODO : Ex3. *)

Module Ex4. Section Ex4.
  Import PreOrder Fun.
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