Require Import Common.
Require Sets Graphs Concrete.

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