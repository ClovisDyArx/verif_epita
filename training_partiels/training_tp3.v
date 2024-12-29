Require Import List.
Import ListNotations.


Lemma left_concat_list_nil :
forall(A: Set) (l : list A), l++nil = l.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Lemma right_concat_list_nil :
forall (A: Set) (l : list A), nil++l = l.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition list_associativity :
forall (A : Set) (l1 l2 l3 : list A), l1++(l2++l3) = (l1++l2)++l3.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Fixpoint length {A : Set} (l : list A) :=
  match l with
  | (_ :: t) => 1 + length t
  | [] => 0
 end.


Proposition concat_length_sum : forall (A:Set) (xs ys: list A), length
(xs ++ ys) = length xs + length ys.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Fixpoint rev {A : Set} (l : list A) :=
  match l with
  | [] => []
  | (a :: t) => (rev t) ++ [a]
  end.


Proposition rev_preserve_length : forall (A : Set) (l : list A), length (rev l) = length l.

Search (_ + _ = S _).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

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
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition nth_len_app2 :
forall (A:Set) (l1 l2: list A) (i: nat),
(i < length l1) -> nth i (l1 ++ l2) = nth i l1.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Lemma rev_involutive:
forall (A:Set) (l: list A), rev (rev l) = l.

Proof.
    admit.
Admitted.

(*-------------------------------------------------------*)

Lemma rev_involution :
forall (A:Set) (xs ys: list A),
rev ((rev xs) ++ ys) = rev ys ++ xs.

Proof.
    admit.
Admitted.