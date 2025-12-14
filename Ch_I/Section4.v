Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Functor
  Functor.Hom
  Natural.
From Category.Instance Require Sets.

Module Ex1.
  Import Sets.
  Parameter S : Sets.

  Local Notation "X ^ Y" :=
    (SetoidObject_function Y X) : category_theory_scope.
  Local Notation "X × Y" := (SetoidObject_prod X Y)
    (at level 40) : category_theory_scope.

  Program Definition pointwise_prod
    {C : Category} (F G : C ⟶ Sets) : C ⟶ Sets :=
      {|  fobj := λ x, (F x) × (G x)
        ; fmap := λ x y f,
            {| morphism := λ p, (fmap[F] f (fst p), fmap[G] f (snd p)) |}

        ; fmap_respects := λ x y f g eq, _
      |}.
  Next Obligation. now proper; rewrites. Qed.
  Next Obligation. split; setoid_fequal; now rewrites. Qed.
  Next Obligation.
    sufficient (fmap[F] id[x] ≡ id ∧ fmap[G] id[x] ≡ id).
    now split; rewrite fmap_id.
  Qed.
  Next Obligation.
    sufficient ( fmap[F] (f ∘ g) ≡ fmap[F] f ∘ fmap[F] g
               ∧ fmap[G] (f ∘ g) ≡ fmap[G] f ∘ fmap[G] g ).
    now split; rewrite fmap_comp.
  Qed.
  Local Notation "F × G" := (pointwise_prod F G) : functor_scope.

  Program Definition eval : Hom(S,-) × (Const S) ⟹ Id :=
    {|  component := λ X, {| morphism := λ hs, (fst hs) (snd hs) |} |}.
  Next Obligation.
    intros [h1 s1] [h2 s2] [e1 e2].
    simpl in *. now rewrites.
  Qed.
End Ex1.

(* TODO : Ex2. *)

(* TODO : Ex3. *)

(* TODO : Ex4. *)

Module Ex5.
  Parameter B : Category.
  Parameter C : Category.
  Parameter S T : C ⟶ B.

  Definition diagonal (τ : S ⟹ T) {c c' : C}
    : c ~> c' → S c ~> T c' := λ f, τ c' ∘ fmap[S] f.
  
  Theorem diagonal_spec (τ : S ⟹ T) {c d e : C} (g : d ~> e) (f : c ~> d)
    : fmap[T] g ∘ diagonal τ f ≡ diagonal τ (g ∘ f)
    ∧ diagonal τ (g ∘ f) ≡ diagonal τ g ∘ fmap[S] f.
  Proof.
    unfold diagonal; cat; normalize; try done.
    comp_left; now normalize.
  Qed.

  Theorem diagonal_spec_converse (τ : ∀ {c c' : C}, c ~> c' → S c ~> T c')
    : (∀ {c d e : C} (g : d ~> e) (f : c ~> d), fmap[T] g ∘ τ f ≡ τ (g ∘ f))
    → (∀ {c d e : C} (g : d ~> e) (f : c ~> d), τ (g ∘ f) ≡ τ g ∘ fmap[S] f )
    → (∀ {c c' : C}, Proper (equiv ==> equiv) (@τ c c'))
    → ∃! τ' : S ⟹ T, ∀ c, τ' c ≡ τ (id[c]).
  Proof.
    intros DR DL PROPER. construct;
      [ natural_transform; [exact (λ x, τ x x id)|simpl]
      ; rewrite DR, <-DL; now normalize
      |..]; done.
  Qed.
End Ex5.

(* TODO : Ex6. *)