Require Import Common.
From CoqCat Require Product.

Module Ex1.
  Import Product.

  (* Check BinaryProduct.preserves_IsMonoid. *)
  (* Check BinaryProduct.preserves_IsGroupoid. *)
  (* Check BinaryProduct.preserves_IsDiscrete. *)
End Ex1.

Module Ex2.
  Import Product.

  (* Check BinaryProduct.preserves_IsPreOrder. *)
End Ex2.

Module Ex3. Section Ex3.
  Import Product. Local Open Scope functor_scope.
  Context `{A : Category ObjA} [I : Type] `{C : ∀ i : I, Category (ObjC i)}.

  Lemma universal_property_existence i (F : ∀ i, A ⟶ C i) : Proj[C] i ∘ ∏ F = F i.
  Proof. cby apply functor_ext. Qed.
  
  Lemma universal_property_uniqueness (F : ∀ i, A ⟶ C i) (G : A ⟶ ∏ C) (COMPAT : ∀ i, Proj[C] i ∘ G = F i) : G = ∏ F.
  Proof.
    apply functor_ext.
    - apply func_ext=> a. apply func_ext_dep=> i.
      specialize (COMPAT i). fapply fobj in COMPAT.
      eapply equal_f in COMPAT. exact COMPAT.
    - ii. eapply jmeq_func_ext_dep=> i. specialize (COMPAT i).
      cut (JMeq ((Proj[C] i ∘ G) # f) (F i # f))%morphism; rewrite // ?COMPAT //.
  Qed.
End Ex3. End Ex3.

Module Ex4.
  (* TODO : Solve this after defining Matr_K. *)
End Ex4.

Module Ex5.
  (* TODO : Solve this after defining Top and Rng. *)
End Ex5.