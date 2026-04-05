Require Import Common.
Require Graphs Concrete.

Module Ex1.
  Import Graphs.

  Definition f := Two.f_AB : hom[2] _ _.

  Program Instance f_monic : Monic f.
  Next Obligation. by depdes x y. Qed.

  Program Instance f_epic : Epic f.
  Next Obligation. by depdes x y. Qed.

  Theorem f_not_isomorphism : IsIsomorphism f → False.
  Proof. intros [finv]; ss; depdes finv. Qed.
End Ex1.

Module Ex2.
  (* Check @monic_comp. *)
  (* Check @epic_comp. *)
End Ex2.

Module Ex3.
  Import Sets.

  Notation N := (Sets.from_type nat).
  Notation "{*}" := (Sets.from_type unit).

  Definition g : N ~> {*} := λ _, tt.
  Definition f : {*} ~> N := λ _, 0%nat.

  Theorem gf_monic : Monic (g ∘ f).
  Proof. construct. cby apply func_ext. Qed.

  Theorem f_monic : Monic f.
  Proof. eapply @monic_strip, gf_monic. Qed.

  Theorem g_not_monic : Monic g → False.
  Proof.
    i. hexploit (monic g (λ _ : {*}, 0%nat) (λ _, 1%nat))=> // /equal_f.
    intro CONTRA. hexploit (CONTRA tt)=> //.
  Qed.
End Ex3.