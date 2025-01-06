(* The goal of this exam is to prove the equivalence:

a = 1 /\ b = 1 <-> a * b = 1.

and then a more general verison on lists.

It is split into 8 propositions you will have to prove.

Your goal is to replace the "admit. Admitted." part by an actual
proof, validated by Qed.

You MUST respect the following instructions

- only tactics from the cheatsheet are authorized
- lemmas from the standard library are forbidden.
- do not change the propositions q1, q2 ...
- do not load any third party library
- do not add load any module (e.g, Arith, ...) (the ones you will need are already loaded)
- remove printing (Show, Locate, etc) before submitting

You can:
- add intermediate lemmas *if you prove them* (you can not admit them)
- use a result from a previous question even if it is admitted

Failure to comply to one or more instructions can lead to grade of 0
of the whole exercise. Syntactically invalid files and files that fails to
interpret correctly will be graded 0.
*)

Proposition q0 :
  forall a:nat, a + 0 = a.
Proof.
   admit.
Admitted.

Proposition q1 :
  forall a:nat, a * 0 = 0.
Proof.
   admit.
Admitted.

Proposition q2 :
  forall a b: nat, a + S b = S (a + b).
Proof.
   admit.
Admitted.


Proposition q3 :
  forall a b :nat, a = 1 /\ b = 1 -> a * b = 1.
Proof.
   admit.
Admitted.


(* Hint 1: reasonning on the case b=0, b>=1 can be useful *)
(* Hint 2: the 'discriminate H' tactic makes it possible to solve a goal
as soon as there is an equality between two different constructor in
the hypothesis 'H'.*)
Proposition q4 :
  forall a b :nat, S (S a) * b = 1 -> False.
Proof.
   admit.
Admitted.

(* Hint: reasonning on the three cases a=0, a=1, a>=2, should help you *)
Proposition q5 :
  forall a b :nat, a * b = 1 -> a = 1 /\ b = 1.
Proof.
   admit.
Admitted.

Require Import List.
Require Import Setoid.
Import ListNotations.

(* Builds the proposition : all elements in l are equal to 1 *)
Fixpoint f1 (l:list nat) : Prop :=
  match l with
  | [] => True
  | h::t => h = 1 /\ f1 t
  end.

(* [List.fold_right Nat.mul 1 l] computes the product of all the integer in l, using the initial value 1. *)
Proposition q6 :
  forall l,
    List.fold_right Nat.mul 1 l = 1 -> f1 l.
Proof.
   admit.
Admitted.

Proposition q7 :
  forall l, f1 l -> List.fold_right Nat.mul 1 l = 1.
Proof.
    admit.
Admitted.

Proposition q8 :
  forall l,
    List.fold_right Nat.mul 1 l = 1 <-> f1 l.
Proof.
   admit.
Admitted.
