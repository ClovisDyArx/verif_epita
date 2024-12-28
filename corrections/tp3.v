Require Import List.
Import ListNotations.


Lemma left_concat_list_nil :
forall(A: Set) (l : list A), l++nil = l.

Proof.
intros.
induction l.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl.
  reflexivity.
Qed.


Lemma right_concat_list_nil :
forall (A: Set) (l : list A), nil++l = l.

Proof.
intros.
induction l.
- simpl.
  reflexivity.
- simpl.
  reflexivity.
Qed.


Proposition list_associativity :
forall (A : Set) (l1 l2 l3 : list A), l1++(l2++l3) = (l1++l2)++l3.

Proof.
intros.
induction l1.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl1.
  reflexivity.
Qed.


Fixpoint length {A : Set} (l : list A) :=
  match l with
  | (_ :: t) => 1 + length t
  | [] => 0 
 end.


Proposition concat_length_sum : forall (A:Set) (xs ys: list A), length
(xs ++ ys) = length xs + length ys.

Proof.
intros.
induction xs.
- simpl.
  reflexivity.
- simpl.
  rewrite IHxs.
  reflexivity.
Qed.


Fixpoint rev {A : Set} (l : list A) :=
  match l with
  | [] => []
  | (a :: t) => (rev t) ++ [a]
  end.


Proposition rev_preserve_length : forall (A : Set) (l : list A), length (rev l) = length l.

Search (_ + _ = S _).

Proof.
intros.
unfold rev.
induction l.
- simpl.
  reflexivity.
- simpl.
  rewrite concat_length_sum with (xs := rev l).
  simpl.
  rewrite <- IHl.
  rewrite PeanoNat.Nat.add_1_r.
    reflexivity.
Qed.


Fixpoint nth {A:Set} (i:nat) (xs:(list A)) : (option A) :=
  match (xs, i) with
  | ([], _) => None
  | ((a :: t), 0) => Some a
  | ((_ :: t), (S j)) => nth j t
  end.


Proposition nth_len_app1 :
forall (A:Set) (l1 l2 : list A),
nth (length l1) (l1 ++ l2) = nth 0 l2.

Proof.
intros.
unfold nth.
induction l1.
- simpl.
  induction l2.
  * reflexivity.
  * reflexivity.
- simpl.
  rewrite IHl1.
  induction l2.
  * reflexivity.
  * reflexivity.
Qed.


Proposition nth_len_app2 :
forall (A:Set) (l1 l2: list A) (i: nat),
(i < length l1) -> nth i (l1 ++ l2) = nth i l1.

Proof.
induction l1.
- intros l2 i.
  simpl.
  intro.
  Search (_ < _).
  apply PeanoNat.Nat.nlt_0_r in H.
  contradiction H.
- intros l2 i.
  destruct i.
  + simpl.
    intro.
    reflexivity.
  + simpl.
    intro.
    Search (S _ < S _).
    apply PeanoNat.lt_S_n in H.
    apply IHl1.
    assumption.
Qed.


Lemma rev_involutive:
forall (A:Set) (l: list A), rev (rev l) = l.

Proof.
admit.
Admitted.

(*flemme...*)

Lemma rev_involution :
forall (A:Set) (xs ys: list A),
rev ((rev xs) ++ ys) = rev ys ++ xs.

Proof.
admit.
Admitted.

(*flemme...*)