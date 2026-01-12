Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Isomorphism
  Functor
  Natural.
From Category.Facts Require Group.Automorphism.
From Category.Construction Require Product Fun.
From Category.Instance Require PreOrder Discrete Cat Fin Grp Two.

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
  Import Fin Grp Fun Discrete Automorphism.
  Context (G : Group) {FIN : @Finite G G}.
  Local Open Scope group_type_scope.
  Local Open Scope group_scope.

  (** Every object [F] in the category [Fun[G,Fin]] can be represented as a group homomorphism
    * from [G] to [Aut[Fin] (F ttt)]. In other words, each object can be represented as a finite
    * G-set.
    *)
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

  (** Each morphism [f] from [F] to [G] in the category [Fun[G,Fin]] can be represented as a
    * function [φ] from [F ttt] to [G ttt] such that [φ (g ⋅ x) ≡ g ⋅ φ x] for every [g] and
    * [x]. In other words, each morphism can be represented as a G-morphism. Hence, the category
    * [Fun[G,Fin]] is equivalent to the category of finite G-sets.
    *)
End Ex5. End Ex5.

(* TODO : Ex6. *)

Module Ex7. Section Ex7.
  Import Two Fun.
  Context (B : Category) (C : Category).

  Section H_determines.
    Context (H : C ⟶ Fun[2,B]).

    Program Definition S : C ⟶ B :=
      {| fobj := λ c, H c TwoA ; fmap := λ _ _ f, fmap[H] f TwoA |}.
    Next Obligation. now proper; sufficient (fmap[H] x0 ≡ fmap[H] y0); rewrites. Qed.
    Next Obligation. now sufficient (fmap[H] id[x] ≡ id); rewrite fmap_id. Qed.
    Next Obligation. now sufficient (fmap[H] (f ∘ g) ≡ fmap[H] f ∘ fmap[H] g); normalize. Qed.

    Program Definition T : C ⟶ B :=
      {| fobj := λ c, H c TwoB ; fmap := λ x y f, fmap[H] f TwoB |}.
    Next Obligation. now proper; sufficient (fmap[H] x0 ≡ fmap[H] y0); rewrites. Qed.
    Next Obligation. now sufficient (fmap[H] id[x] ≡ id); rewrite fmap_id. Qed.
    Next Obligation. now sufficient (fmap[H] (f ∘ g) ≡ fmap[H] f ∘ fmap[H] g); normalize. Qed.

    Program Definition τ : S ⟹ T :=
      {| component := λ c, fmap[H c] TwoF |}.
    Next Obligation. now normalize. Qed.
  End H_determines.

  Section Triple_determines.
    Context (S T : C ⟶ B) (τ : S ⟹ T).

    Program Definition H_fobj (c : C) : Fun[2,B] :=
      {|  fobj := λ x : 2, match x with
                           | TwoA => S c
                           | TwoB => T c
                           end
        ; fmap := λ x y (f : x ~{2}~> y), match f with
                                          | TwoIdA => id[S c]
                                          | TwoIdB => id[T c]
                                          | TwoF   => τ c
                                          end
      |}.
    Next Obligation. now destruct x. Qed.
    Next Obligation.
      pose proof (TwoHom_inv f). pose proof (TwoHom_inv g).
      unfold TwoHom_inv_t, Two._2_obligation_1 in *.
      by destruct x, y, z; ss; subst.
    Qed.

    Program Definition H : C ⟶ Fun[2,B] :=
      {|  fobj := H_fobj
        ; fmap := λ x y f,
            {|  component := λ o : 2, match o return (∀ x y f, H_fobj x o ~> H_fobj y o) with
                                      | TwoA => λ _ _, fmap[S]
                                      | TwoB => λ _ _, fmap[T]
                                      end x y f
              ; naturality := _
            |}
      |}.
    Next Obligation.
      pose proof (TwoHom_inv f0). unfold TwoHom_inv_t in X.
      now destruct x0, y0; subst; ss; normalize.
    Qed.
    Next Obligation. now proper; destruct x1; rewrites. Qed.
    Next Obligation. by destruct x0. Qed.
    Next Obligation. by destruct x0. Qed.
  End Triple_determines.

  Section Bijection.
    Program Definition bijective_1 (H' : C ⟶ Fun[2,B]) : H' ≡ H (S H') (T H') (τ H') := (_ ; _).
    Next Obligation.
      isomorphism.
      - natural_transform; ss.
        + destruct x0; exact id.
        + pose proof (TwoHom_inv f). unfold TwoHom_inv_t in X.
          by destruct x0, y; subst; ss.
      - natural_transform; ss.
        + destruct x0; exact id.
        + pose proof (TwoHom_inv f). unfold TwoHom_inv_t in X.
          by destruct x0, y; subst; ss.
      - by destruct x0.
      - by destruct x0.
    Defined.
    Next Obligation. by destruct x0. Qed.
  
    Program Definition bijective_2 (S' T' : C ⟶ B) (τ' : S' ⟹ T')
      : ∃ S_iso : S' ≅[Fun[C,B]] S (H S' T' τ'),
        ∃ T_iso : T' ≅[Fun[C,B]] T (H S' T' τ'),
        τ' ≡ T_iso⁻¹ ∘ τ (H S' T' τ') ∘ S_iso := (_; (_; _)).
    Next Obligation. by unshelve by isomorphism; try natural_transform. Defined.
    Next Obligation. by unshelve by isomorphism; try natural_transform. Defined.
  End Bijection.
End Ex7. End Ex7.

Module Ex8. Section Ex8.
  Import Two Fun Product.
  Context (C : Category).

  Program Definition Ta : C ⟶ C × 2 :=
    {| fobj := λ c, (c, TwoA) ; fmap := λ x y f, (f, TwoIdA) |}.

  Program Definition Tb : C ⟶ C × 2 :=
    {| fobj := λ c, (c, TwoB) ; fmap := λ x y f, (f, TwoIdB) |}.

  Program Definition μ : Ta ⟹ Tb := {| component := λ c, (id[c], TwoF) |}.

  Context (B : Category) (S T : C ⟶ B) (τ : S ⟹ T).

  Definition F_fobj (x : obj[C × 2]) : B :=
    match x with
    | (c, TwoA) => S c
    | (c, TwoB) => T c
    end.

  Program Definition F : C × 2 ⟶ B := {| fobj := F_fobj |}.
  Next Obligation.
    pose proof (TwoHom_inv t). unfold TwoHom_inv_t in X.
    destruct t0, t1; subst; ss.
    - exact (fmap[S] h).
    - exact (fmap[T] h ∘ τ o0).
    - exact (fmap[T] h).
  Defined.
  Next Obligation.
    proper; ss; subst.
    pose proof (TwoHom_inv H0). unfold TwoHom_inv_t in X0.
    now destruct t0, t; subst; ss; rewrites.
  Qed.
  Next Obligation. by destruct t. Qed.
  Next Obligation.
    pose proof (TwoHom_inv t0). pose proof (TwoHom_inv t).
    unfold TwoHom_inv_t in *. destruct t1, t2, t3; ss; subst; normalize; try done.
    now rewrite <-comp_assoc, <-naturality, comp_assoc.
  Qed.

  Theorem ex8 (c : C)
    : let H : C ⟶ Fun[2,B] := Ex7.H B C S T τ in
      F (c, TwoA) ≅ H c TwoA
    ∧ F (c, TwoB) ≅ H c TwoB
    ∧ fmap[F] ((id[c], TwoIdA) : (c,TwoA) ~{C × 2}~> (c,TwoA)) ≡ fmap[H c] TwoIdA
    ∧ fmap[F] ((id[c], TwoIdB) : (c,TwoB) ~{C × 2}~> (c,TwoB)) ≡ fmap[H c] TwoIdB
    ∧ fmap[F] ((id[c], TwoF) : (c,TwoA) ~{C × 2}~> (c,TwoB)) ≡ fmap[H c] TwoF.
  Proof. by simplify; try exact iso_id. Qed.
End Ex8. End Ex8.