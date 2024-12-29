Proposition plus_n_0 :
forall n: nat, n+0=n.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition double_is_plus:
forall n : nat, n+n=2*n.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition add_succ_l :
forall n m: nat, S n + m = S (n + m).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition add_succ_r :
forall n m: nat, n + S m = S (n + m).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Print nat.
Fixpoint fact (n:nat) : nat :=
match n with
| 0 => 1
| S n' => n * (fact n') end.

(*-------------------------------------------------------*)

Fixpoint even (n:nat) : Prop :=
match n with
| 0 => True
| S 0 => False
| S (S n) => even (n) end.

(*-------------------------------------------------------*)

Proposition one_of_two_succ_is_even:
forall n : nat, (even n) \/ (even (S n)).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition but_not_both :
forall n : nat, even n -> ~ (even (S n)).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition double_is_even :
forall n : nat, even (n*2).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition succ_double_is_odd :
forall n : nat, ~(even (S (n*2))).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition pair_induction :
forall (P : nat -> Prop),
P 0 -> P 1 -> (forall n, P n -> P (S n) -> P (S (S n))) ->
forall x, P x.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Definition mystery (f : nat -> nat) : Prop :=
exists t, t > 0 /\ forall x, f x = f (x+t).