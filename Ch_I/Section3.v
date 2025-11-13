Require Import Category.Lib.
From Category.Theory Require Import
  Category
  Functor
  Isomorphism
  Natural.
Require Import Category.Theory.Functor.Setoid.
Require Import Category.Construction.Fun.
From Category.Instance Require One Two Three PreOrder.

(* TODO : Ex1. *)

Module Ex2.
  Import One Two Three.
  Section One.
    Context {C : Category}.

    Definition Wrap1 (x : C) : 1 ⟶ C :=
      {| fobj := λ _, x
      ; fmap := λ _ _ _, id[x]

      ; fmap_respects := λ _ y f g fg, reflexivity id[x]
      ; fmap_id := λ _, reflexivity id[x]
      ; fmap_comp := λ _ _ _ f g, symmetry (id_right id[x])
      |}.
    
    Definition Unwrap1 (F : 1 ⟶ C) : C := F ttt.

    Lemma Wrap1_Unwrap1 (F : 1 ⟶ C) : Wrap1 (Unwrap1 F) ≡ F.
    Proof. srapply Component_Is_Iso_NatIso; construct; cat. Qed.

    Lemma Unwrap1_Wrap1 (x : C) : Unwrap1 (Wrap1 x) = x.
    Proof. reflexivity. Qed.
  End One.

  Section Two.
    Context {C : Category}.

    Local Ltac two_solver :=
      intros; repeat match goal with
                     | [ f : TwoHom _ _ |- _ ] => srewrite (TwoHom_inv f)
                     | [ x : TwoObj |- _ ] => destruct x
                     | [ x : obj[2] |- _ ] => destruct x
                     | [ H : TwoB = TwoA |- _ ] => inversion H
                     | [ H : TwoA = TwoB |- _ ] => inversion H
                     end; auto with two_laws; cat.

    Program Definition Wrap2 {x y : C} (f : x ~{C}~> y) : 2 ⟶ C :=
      {| fobj := λ o, match o with
                      | TwoA => x
                      | TwoB => y
                      end
       ; fmap := λ _ _ ϕ, match ϕ with
                          | TwoIdA => id[x]
                          | TwoIdB => id[y]
                          | TwoF   => f
                          end
      |}.
    Next Obligation. two_solver. Qed.
    Next Obligation. two_solver. Qed.
    
    Definition Unwrap2 (F : 2 ⟶ C) := fmap[F] TwoF.

    Lemma Wrap2_Unwrap2 (F : 2 ⟶ C) : Wrap2 (Unwrap2 F) ≡ F.
    Proof. srapply Component_Is_Iso_NatIso; construct; two_solver. Qed.

    Lemma Unwrap2_Wrap2 {x y : C} (f : x ~{C}~> y) : Unwrap2 (Wrap2 f) ≡ f.
    Proof. reflexivity. Qed.
  End Two.

  Section Three.
    Context {C : Category}.

    Local Ltac three_solver :=
      intros; repeat match goal with
                     | [ f : ThreeHom _ _ |- _ ] => srewrite (ThreeHom_inv f)
                     | [ x : ThreeObj |- _ ] => destruct x
                     | [ x : obj[3] |- _ ] => destruct x
                     | [ H : ThreeC = ThreeA |- _ ] => inversion H
                     | [ H : ThreeC = ThreeB |- _ ] => inversion H
                     | [ H : ThreeB = ThreeA |- _ ] => inversion H
                     | [ H : ThreeA = ThreeB |- _ ] => inversion H
                     | [ H : ThreeA = ThreeC |- _ ] => inversion H
                     | [ H : ThreeB = ThreeC |- _ ] => inversion H
                     end; auto with three_laws; cat.
    
    Program Definition Wrap3
      {x y z : C} (fg : (y ~{C}~> z) ∧ (x ~{C}~> y)) : 3 ⟶ C :=
        {| fobj := λ o, match o with
                        | ThreeA => x
                        | ThreeB => y
                        | ThreeC => z
                        end
         ; fmap := λ _ _ ϕ, match ϕ with
                            | ThreeIdA => id[x]
                            | ThreeIdB => id[y]
                            | ThreeIdC => id[z]
                            | ThreeAB  => snd fg
                            | ThreeBC  => fst fg
                            | ThreeAC  => fst fg ∘ snd fg
                            end
        |}.
    Next Obligation. three_solver. Qed.
    Next Obligation. three_solver. Qed.
    
    Definition Unwrap3 (F : 3 ⟶ C) := (fmap[F] ThreeBC, fmap[F] ThreeAB).

    Lemma Wrap3_Unwrap3 (F : 3 ⟶ C) : Wrap3 (Unwrap3 F) ≡ F.
    Proof. srapply Component_Is_Iso_NatIso; construct; three_solver. Qed.

    Lemma Unwrap3_Wrap3 {x y z : C} (fg : (y ~{C}~> z) ∧ (x ~{C}~> y))
      : Unwrap3 (Wrap3 fg) ≡ fg.
    Proof. now destruct fg. Qed.
  End Three.
End Ex2.

Module Ex3.
  Import PreOrder.
  Section a.
    Context (A : Type) (RA : crelation A) (PREA : PreOrder RA).
    Context (B : Type) (RB : crelation B) (PREB : PreOrder RB).
    Context (T : PreOrderSet PREA ⟶ PreOrderSet PREB).

    Lemma T_Monotonic (p p' : A) : RA p p' → RB (T p) (T p').
    Proof.
      change (RA _ _) with (p ~{PreOrderSet PREA}~> p').
      change (RB _ _) with ((T p) ~{PreOrderSet PREB}~> (T p')).
      apply fmap.
    Qed.
  End a.

  (* TODO : b *)

  (* TODO : c *)
End Ex3.

(* TODO : Ex4. *)

(* TODO : Ex5. *)