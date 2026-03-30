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