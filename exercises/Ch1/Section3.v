Require Import Common.
Require Import Graphs.

Module Ex1.
  (* TODO *)
End Ex1.

Module Ex2. Section Ex2.
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
  (* TODO *)
End Ex3.

Module Ex4.
  (* TODO *)
End Ex4.

Module Ex5.
  (* TODO *)
End Ex5.