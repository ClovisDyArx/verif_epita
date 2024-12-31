Require Import List.
Import ListNotations.


Lemma left_concat_list_nil :
forall (A: Set) (l : list A), nil ++ l = l.

Proof.
  intros.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Lemma right_concat_list_nil:
forall (A : Set) (l : list A), l ++ nil = l.

Proof.
  intros.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.



Proposition asso_list:
forall (A : Set) (l : list A) (m : list A) (n : list A), (l ++ m) ++ n = l ++ (m ++ n).

Proof.
  intros.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.


Fixpoint length {A : Set} (l : list A) :=
  match l with
  | (_ :: t) => 1 + length t
  | [] => 0 
 end.


Proposition concat_length_sum : 
forall (A:Set) (xs ys: list A), length (xs ++ ys) = length xs + length ys.

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
| (j :: t) => rev t ++ [j]
end.


Proposition rev_keep_length :
forall (A:Set) (l : list A), length l = length (rev l).

Proof.
  intros.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite concat_length_sum.
    simpl.
    Search (_ + _ = S _).
    rewrite PeanoNat.Nat.add_1_r.
    rewrite IHl.
    reflexivity.
Qed.


Fixpoint nth {A:Set} (i:nat) (xs:(list A)) : (option A) :=
match i, xs with
| 0, a::l => Some a
| _, [] => None
| S j, a::l => nth (j) l
end.



Proposition nth_len_app1 :
forall (A:Set) (l1 l2 : list A),
nth (length l1) (l1 ++ l2) = nth 0 l2.

Proof.
  intros.
  induction l1.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity.
Qed.


Proposition nth_len_app2 :
forall (A:Set) (l1 l2: list A) (i: nat),
(i < length l1) -> nth i (l1 ++ l2) = nth i l1.

Proof.
  intros A l1 l2.
  induction l1.
  - intro i.
    simpl.
    Search (_ < 0).
    intro.
    apply PeanoNat.Nat.nlt_0_r in H.
    contradiction H.
  - intro i.
    simpl.
    destruct i.
    + simpl.
      reflexivity.
    + intro.
      Search (S _ < S _).
      apply PeanoNat.lt_S_n in H.
      simpl.
      apply IHl1.
      assumption.
Qed.


Lemma rev_distrib:
forall (A:Set) (l m: list A), rev (l ++ m) = rev m ++ rev l.

Proof.
  intros.
  induction l.
  - simpl.
    rewrite right_concat_list_nil.
    reflexivity.
  - simpl.
    rewrite IHl.
    rewrite asso_list.
    reflexivity.
Qed.


Lemma rev_involution :
forall (A:Set) (xs ys: list A),
rev ((rev xs) ++ ys) = rev ys ++ xs.

Proof.
  intros A xs.
  induction xs.
  - simpl.
    intro ys.
    rewrite right_concat_list_nil.
    reflexivity.
  - simpl.
    intro ys.
    rewrite rev_distrib.
    rewrite IHxs.
    simpl.
    reflexivity.
Qed.


Lemma rev_involutive:
forall (A:Set) (l: list A), rev (rev l) = l.

Proof.
  intros.
  replace l with (nil ++ l).
  - rewrite rev_distrib.
    rewrite rev_involution.
    simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Lemma rev_involutive2:
forall (A:Set) (l: list A), rev (rev l) = l.

Proof.
  intros.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite rev_distrib.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.









