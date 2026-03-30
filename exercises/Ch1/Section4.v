Require Import Common.
Require Sets Graphs Concrete.

Module Ex1. Section Ex1.
  Import Sets SetsNotations.
  Context (S : Sets.Object).
  
  Program Definition fromS : Sets.t ⟶ Sets.t :=
    {|
      fobj := λ X, S → X;
      fmap := λ X Y f h, f ∘ h
    |}.

  Program Definition eval : ((-×-)%sets ∘ ⟨ fromS , .↦ S ⟩) ⟹ id :=
    {| component := λ X hs, hs.1 hs.2 |}.
End Ex1. End Ex1.

Module Ex2. Section Ex2.
  Import Concrete GrpNotations.
  
  Program Definition Hx (H : Grp.Object) : Grp.t ⟶ Grp.t :=
    {|
      fobj := λ G, (H × G)%grp;
      fmap := λ G G' ϕ, 
        {|
          fobj := λ hg, (hg.1, ϕ hg.2);
          fmap := λ _ _ fg, (fg.1, ϕ # fg.2)%morphism
        |};
    |}.
  Next Obligation.
    apply functor_ext; try functor_solver.
    apply func_ext; i. by depdes x0.
  Qed.
  Next Obligation. apply functor_ext; functor_solver. Qed.

  Notation "H '×-'" := (Hx H) (at level 0, no associativity, format "H ×-").

  Program Definition Ex2 {H K : Grp.Object} (f : H ~> K) : H×- ⟹ K×- :=
    {|
      component := λ G,
        {|
          fobj := λ hg, (f hg.1, hg.2);
          fmap := λ _ _ fg, (f # fg.1, fg.2)%morphism
        |}
    |}.
  Next Obligation. apply functor_ext; functor_solver. Qed.
End Ex2. End Ex2.