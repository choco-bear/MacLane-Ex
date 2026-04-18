Require Import Common.
Require Graphs Concrete.

Module Ex1.
  Section Part1.
    (* TODO : Solve this after defining the field of quotients and the integral domains. *)
  End Part1.

  Section Part2.
    (* TODO : Solve this after defining the Lie algebras and the Lie groups.*)
  End Part2.
End Ex1.

Module Ex2. Section Ex2.
  Import Graphs.
  Context `{C : Category Obj}.
  
  Program Definition wrap_1 x : 1 ⟶ C :=
    {|
      fobj := λ _, x;
      fmap := λ _ _ _, id[x]%morphism
    |}.

  Definition unwrap_1 (F : 1 ⟶ C) : obj[C] := F One.A.

  Lemma unwrap_wrap_1 x : unwrap_1 (wrap_1 x) = x.
  Proof. ss. Qed.

  Lemma wrap_unwrap_1 F : wrap_1 (unwrap_1 F) = F.
  Proof.
    apply functor_ext. { extensionality x. One.solver. }
    ii. ss. depdes x y f F. rewrite /wrap_1 /Functor.fobj /Functor.fmap /= fmap_id //.
  Qed.

  Program Definition wrap_2 `(f : x ~> y) : 2 ⟶ C :=
    {|
      fobj := λ o, match o with
                   | Two.A => x
                   | Two.B => y
                   end;
      fmap := λ _ _ ϕ, match ϕ with
                       | Two.id_A => id[x]
                       | Two.id_B => id[y]
                       | Two.f_AB => f
                       end%morphism
    |}.
  Solve Obligations with Two.solver.

  Definition unwrap_2 (F : 2 ⟶ C) : F Two.A ~> F Two.B := F # Two.f_AB.

  Lemma unwrap_wrap_2 `(f : x ~> y) : unwrap_2 (wrap_2 f) = f.
  Proof. ss. Qed.

  Lemma wrap_unwrap_2 (F : 2 ⟶ C) : wrap_2 (unwrap_2 F) = F.
  Proof.
    apply functor_ext. { extensionality x. Two.solver. }
    ii. ss. depdes x y f F; rewrite /wrap_2 /unwrap_2 /Functor.fmap /Functor.fobj ?fmap_id //.
  Qed.

  Program Definition wrap_3 `(f : y ~> z) `(g : x ~> y) : 3 ⟶ C :=
    {|
      fobj := λ o, match o with
                   | Three.A => x
                   | Three.B => y
                   | Three.C => z
                   end;
      fmap := λ _ _ ϕ, match ϕ with
                       | Three.id_A => id[x]
                       | Three.id_B => id[y]
                       | Three.id_C => id[z]
                       | Three.f_AB => g
                       | Three.f_AC => f ∘ g
                       | Three.f_BC => f
                       end%morphism
    |}.
  Solve Obligations with Three.solver.

  Definition unwrap_3 (F : 3 ⟶ C)
    : (F Three.B ~> F Three.C) * (F Three.A ~> F Three.B) :=
      (F # Three.f_BC, F # Three.f_AB)%morphism.
  
  Lemma unwrap_wrap_3 `(f : y ~> z) `(g : x ~> y) : unwrap_3 (wrap_3 f g) = (f, g).
  Proof. ss. Qed.

  Lemma wrap_unwrap_3 (F : 3 ⟶ C) : (λ p, wrap_3 (fst p) (snd p)) (unwrap_3 F) = F.
  Proof.
    apply functor_ext. { extensionality x. Three.solver. }
    ii. ss. depdes x y f F; rewrite /wrap_3 /unwrap_3 /Functor.fmap /Functor.fobj ?fmap_id -?fmap_comp //.
  Qed.
End Ex2. End Ex2.

Module Ex3.
  Section PartA.
    Context (take : ∀ A, inhabited A → A).
    Context `{_PPO : @IsPreOrder ObjP P} `{_QPO : @IsPreOrder ObjQ Q}.

    Notation monotonic := (Proper ((≤) ==> (≤))).

    Program Definition functor_to_monotonic (T : P ⟶ Q) : monotonic T := _.
    Next Obligation. by inv H; split; apply T. Qed.

    Program Definition monotonic_to_functor
      (f : ObjP → ObjQ) {MONO : monotonic f} : P ⟶ Q :=
      {|
        fobj := f;
        fmap := λ x y g, take _ (MONO x y (inhabits g));
      |}.
  End PartA.

  Section PartB.
    Import Concrete. Local Open Scope morphism_scope.
    Context (G H : Grp.Object).

    Notation is_homomorphism := (λ f, ∀ x y, f (x ∘ y) = f x ∘ f y).

    Program Definition functor_to_homomorphism (T : G ~> H)
      : is_homomorphism (hom_cast _ _ ∘ (fmap T : ⇑ G → _) : _ → ⇑ H)%stdpp := _.
    Next Obligation. by fmap_eq_simplify. Qed.

    Program Definition homomorphism_to_functor
      (f : ⇑ G → ⇑ H) {MORPHISM : is_homomorphism f} : G ~> H :=
      {|
        fobj := λ _, ●;
        fmap := λ _ _ g, f ⇑g;
      |}.
    Next Obligation.
      rewrite hom_cast_id.
      cut (f id[●] ∘ f id[●] = f id[●] ∘ id[●]). 
      - cby i; comp_l (f id[●]).
      - cby rewrite -MORPHISM.
    Qed.
    Next Obligation. rewrite -MORPHISM; f_equal; fmap_eq_simplify //. Qed.
  End PartB.

  Section PartC.
    Import Concrete.
    Context (G : Grp.Object).

    Section Sets.
      Import Sets. Local Open Scope morphism_scope.

      (* Search Functor_preserves_IsIso. *)
      Program Definition functor_to_representation (T : G ⟶ Sets.t) (g : ⇑ G)
        : IsIsomorphism (T # g) := _.

      Program Definition representation_to_functor [X : Sets.Object] (f : ⇑ G → (X ~> X))
        {REPR : ∀ g, IsIsomorphism (f g)} {HOMO : ∀ x y, f (x ∘ y) = f x ∘ f y} : G ⟶ Sets.t :=
          {|
            fobj := λ _, X;
            fmap := λ _ _ g, f ⇑g;
          |}.
      Next Obligation.
        rewrite hom_cast_id.
        cut (f id[●] ∘[Sets.t] f id[●] = f id[●] ∘[Sets.t] id[X]).
        - i. by comp_l (f id[●] : _ ~{Sets.t}~> _).
        - cby rewrite -HOMO.
      Qed.
      Next Obligation. rewrite -HOMO. f_equal. fmap_eq_simplify /=. Qed.
    End Sets.

    Section Matr.
      (* TODO : Solve this after defining Matr_K *)
    End Matr.
  End PartC.
End Ex3.

Module Ex4.
  (* TODO : Solve this after defining [Ab]. *)
End Ex4.

Module Ex5.
  Import Concrete. Local Open Scope morphism_scope.

  Definition I : Grp.t ⟶ Grp.t := id.

  (* TODO *)
End Ex5.