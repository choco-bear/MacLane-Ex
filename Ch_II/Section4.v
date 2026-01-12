Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Isomorphism
  Functor
  Natural.
From Category.Facts Require Group.Automorphism.
From Category.Construction Require Product Fun.
From Category.Instance Require PreOrder Discrete Cat Fin Grp.

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

Module Ex5. Section Ex5.
  Import Fin.
  Context (G : Group) {FIN : @Finite G G}.
  Local Open Scope group_type_scope.
  Local Open Scope group_scope.

  (** Every object [F] in the category [Fun[G,Fin]] can be represented as a group homomorphism
    * from [G] to [Aut[Fin] (F ttt)]. In other words, each object can be represented as a finite
    * G-set.
    *)
  Section Objects.
    Import Grp Fun Discrete Automorphism.
    Program Definition functor_defines_homomorphism
      (F : Fun[G,Fin]) : G ~{Grp}~> Aut (F ttt) :=
        {| grp_map := λ g, {| to := fmap[F] g; from := fmap[F] (g⁻¹)%group |} |}.
    Next Obligation.
      unshelve etransitivity.
      { exact ((fmap[F] (g : ttt ~{G}~> ttt) ∘ fmap[F] (g⁻¹ : ttt ~{G}~> ttt)%group) a). }
      { cat. } rewrite <-fmap_comp; unfold of_group; ss.
      by grp_simplify.
    Qed.
    Next Obligation.
      unshelve etransitivity.
      { exact ((fmap[F] (g⁻¹ : ttt ~{G}~> ttt)%group ∘ fmap[F] (g : ttt ~{G}~> ttt)) a). }
      { cat. } rewrite <-fmap_comp; unfold of_group; ss.
      by grp_simplify.
    Qed.
    Next Obligation. now proper; rewrites. Qed.
    Next Obligation.
      i. unshelve etransitivity.
      { exact ((fmap[F] ((g : ttt ~{G}~> ttt) ∘ (h : ttt ~{G}~> ttt))) a). }
      { cat. } now rewrite fmap_comp.
    Qed.

    Program Definition homomorphism_defines_functor
      `(φ : G ~{Grp}~> Aut[Fin] X) : Fun[G,Fin] :=
      {|  fobj := λ _, X
        ; fmap := λ _ _ g, φ g
      |}.
    Next Obligation. now proper; rewrites. Qed.
    Next Obligation. now grp_simplify. Qed.
    Next Obligation. now grp_simplify. Qed.
  End Objects.

  (** Each morphism [f] from [F] to [G] in the category [Fun[G,Fin]] can be represented as a
    * function [φ] from [F ttt] to [G ttt] such that [φ (g ⋅ x) ≡ g ⋅ φ x] for every [g] and
    * [x]. In other words, each morphism can be represented as a G-morphism. Hence, the category
    * [Fun[G,Fin]] is equivalent to the category of finite G-sets.
    *)
End Ex5. End Ex5.

(* TODO : Ex6. *)

(* TODO : Ex7. *)

(* TODO : Ex8. *)