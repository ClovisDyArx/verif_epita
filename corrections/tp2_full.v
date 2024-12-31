Proposition plus_n_0 :
forall n: nat, n+0=n.

Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.


Proposition double_is_plus:
forall n : nat, n+n=2*n.

Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite plus_n_0.
    reflexivity.
Qed.


Proposition add_succ_l :
forall n m: nat, S n + m = S (n + m).

Proof.
  intros.
  simpl.
  reflexivity.
Qed.


Proposition add_succ_r :
forall n m: nat, n + S m = S (n + m).

Proof.
intros.
induction n.
- simpl.
  reflexivity.
- simpl.
  rewrite IHn.
  reflexivity.
Qed.


Fixpoint even (n:nat) : Prop :=
match n with
| 0 => True
| 1 => False
| S (S m) => (even m) end.



Proposition one_of_two_succ_is_even:
forall n : nat, (even n) \/ (even (S n)).


Proof.
  intros.
  induction n.
  - left.
    simpl.
    reflexivity.
  - destruct IHn.
    + right.
      simpl.
      assumption.
    + left.
      assumption.
Qed.




Proposition but_not_both :
forall n : nat, even n -> ~ (even (S n)).

Proof.
  intros.
  unfold "~".
  induction n.
  - simpl.
    intro.
    assumption.
  - simpl.
    intro.
    apply IHn.
    + assumption.
    + assumption.
Qed.





Proposition double_is_even :
forall n : nat, even (n*2).

Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    assumption.
Qed.


Proposition succ_double_is_odd :
forall n : nat, ~(even (S (n*2))).

(*Proof.
  intros.
  simpl.
  induction n.
  - unfold "~".
    simpl.
    intro.
    assumption.
  - simpl.
    assumption.
Qed.*)

Proof.
  intros.
  apply but_not_both.
  apply double_is_even.
Qed.

Proposition pair_induction :
forall (P : nat -> Prop),
P 0 -> P 1 -> (forall n, P n -> P (S n) -> P (S (S n))) ->
forall x, P x.

Proof.
  intros.
  assert (P x /\ P (S x)).
  - induction x.
    + split.
      * assumption.
      * assumption.
    + split.
      * apply IHx.
      * apply H1.
        -- destruct IHx.
            assumption.
        -- destruct IHx.
            assumption.
  - destruct H2.
    assumption.
Qed.



Proposition even_sum :
forall n m : nat, even (n) /\ even (m) -> even (n + m).

Proof.
  intros.
  induction n using pair_induction.
  - simpl.
    destruct H.
    assumption.
  - destruct H.
    contradiction H.
  - simpl.
    apply IHn.
    split.
    + destruct H.
      apply H.
    + destruct H.
      apply H0.
Qed.





Require Import Arith.

Definition mystery (f : nat -> nat) : Prop :=
exists t, t > 0 /\ forall x, f x = f (x+t).

Definition zero (t : nat) : nat := 0.

Proposition mystery_zero :
mystery zero.

Proof.
  unfold mystery.
  exists 1.
  split.
  - apply Nat.lt_0_1.
  - intros.
    unfold zero.
    reflexivity.
Qed.




Definition inverse (f : nat -> nat) (g : nat -> nat) : Prop :=
forall x, f (g x) = x /\ g (f x) = x.

Definition f (t : nat) : nat := t.

Definition g (t : nat) : nat := t.

Proposition inverse_f_g:
inverse f g.

Proof.
  unfold inverse.
  intros.
  split.
  - unfold g.
    unfold f.
    reflexivity.
  - unfold f.
    unfold g.
    reflexivity.
Qed.  












