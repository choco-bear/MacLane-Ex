Require Import Common.
Require Concrete.

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
    {| component := λ G, ⟨f ∘ Fst,id ∘ Snd⟩%functor |}.
  Next Obligation. apply functor_ext; functor_solver. Qed.
End Ex2. End Ex2.

Module Ex3. Section Ex3.
  Import Concrete GrpNotations.
  Context (B C : Grp.Object) (S T : B ~> C).

  Program Definition IfPart (h : ⇑ C) (CONJUGATE : ∀ g : ⇑ B, (⇑ h ∘ S # g = T # g ∘ ⇑ h :> (S ● ~{C}~> T ●))%morphism) : S ⟹ T :=
    {| component := λ g, (⇑ h)%morphism |}.
  Next Obligation.
    cut (x = ● ∧ y = ●)=>[[]|]; last (split; common_simpl); ii; subst.
    pose proof (CONJUGATE f).
    remember (⇑ _ ∘ _)%morphism as LHS.
    remember (_ ∘ ⇑ _)%morphism as RHS.
    etransitivity; first instantiate (1 := LHS).
    { subst. cancel_r. functor_solver. }
    etransitivity; cycle 1; first instantiate (1 := RHS); ss.
    { subst. cancel_l. functor_solver. }
  Qed.

  Theorem OnlyIfPart (τ : S ⟹ T) (g : ⇑ B) : τ ● ∘ S # g =[C] T # g ∘ τ ●.
  Proof. rewrite naturality //. Qed.
End Ex3. End Ex3.

Module Ex4. Section Ex4.
  Context `(C : Category ObjC).
  Context `(P : Category ObjP) `{!IsPreOrder P}.
  Context (S T : C ⟶ P).

  Definition uniqueness : ProofIrrel (S ⟹ T).
  Proof. ii. apply nat_trans_ext=> c. common_simpl. Qed.

  Program Definition IfPart (H : ∀ c : ObjC, S c ≤ T c) : S ⟹ T := {| component := λ c, take _ (H c) |}.

  Definition OnlyIfPart (τ : S ⟹ T) : ∀ c, S c ≤ T c := λ c, inhabits (τ c).
End Ex4. End Ex4.

Module Ex5. Section Ex5.
  Context `(C : Category ObjC) `(B : Category ObjB) (S T : C ⟶ B) (τ : S ⟹ T).

  Definition diagonal `(f : c ~{C}~> c') : S c ~> T c' := T # f ∘ τ c.

  Theorem main `(g : d ~{C}~> e) `(f : c ~{C}~> d)
    : T # g ∘ diagonal f =[B] diagonal (g ∘ f)
    ∧ diagonal (g ∘ f) =[B] diagonal g ∘ S # f.
  Proof.
    split; unfold diagonal; common_simpl.
    cancel_l. rewrite naturality //.
  Qed.

  Theorem converse (μ : S ⟹ T) (H : ∀ c, μ c = diagonal id[c]) : τ = μ.
  Proof. cby apply nat_trans_ext=> c; rewrite H /diagonal. Qed.
End Ex5. End Ex5.

Module Ex6.
  (* TODO : Solve this after defining [Matr] and fields. *)
End Ex6.