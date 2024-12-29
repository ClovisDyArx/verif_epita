Proposition modus_ponens :
forall A B : Prop, (A -> B) -> A -> B.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition transitivity_imp :
forall A B C: Prop, ((A -> B) /\ (B -> C)) -> (A -> C).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition modus_tollens :
forall A B: Prop, (A -> B) -> ~ B -> ~ A.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition a_or_b_false_left:
forall A B : Prop, (( A \/ B) -> False) -> (A -> False).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition a_or_b_false_right:
forall A B : Prop, (( A \/ B) -> False) -> (B -> False).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition de_morgan_bool_1 :
forall a b:bool, negb (orb a b) = andb (negb a) (negb b).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition de_morgan_bool_2 :
forall a b:bool, negb (andb a b) = orb (negb a) (negb b).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition de_morgan_1 :
forall P Q, ~(P \/ Q) -> ~P /\ ~Q.

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition de_morgan_2 :
forall P Q, ~P /\ ~Q -> ~(P \/ Q).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition de_morgan_1_2 :
forall P Q, ~P /\ ~Q <-> ~(P \/ Q).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition de_morgan_classic:
forall P Q, ~P \/ ~Q <-> ~(P /\ Q).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition excluded_middle_irrefutable:
forall P:Prop, ~ ~ (P \/ ~ P).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition double_neg_implies_excluded :
(forall P: Prop, ~ ~ P -> P) -> (forall P, (P \/ ~ P)).

Proof.
   admit.
Admitted.

(*-------------------------------------------------------*)

Proposition excluded_implies_demorgan:
(forall R : Prop, R \/ ~ R) ->
(forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q).

Proof.
   admit.
Admitted.