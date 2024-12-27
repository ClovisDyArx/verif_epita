Proposition modus_ponens :
forall A B : Prop, (A -> B) -> A -> B.

Proof.
  intros A B AB.
  apply AB.
Qed.


Proposition transitivity_imp :
forall A B C: Prop, ((A -> B) /\ (B -> C)) -> (A -> C).

Proof.
  intros.
  apply H.
  apply H.
  assumption.
Qed.


Proposition modus_tollens :
forall A B: Prop, (A -> B) -> ~ B -> ~ A.

Proof.
  unfold not.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.




Proposition a_or_b_false_left:
forall A B : Prop, (( A \/ B) -> False) -> (A -> False).

Proof.
  intros.
  apply H.
  left.
  assumption.
Qed.


Proposition a_or_b_false_right:
forall A B : Prop, (( A \/ B) -> False) -> (B -> False).

Proof.
  intros.
  apply H.
  right.
  assumption.
Qed.


Proposition de_morgan_bool_1 :
forall a b:bool, negb (orb a b) = andb (negb a) (negb b).

Proof.
  intros.
  destruct a.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Proposition de_morgan_bool_2 :
forall a b:bool, negb (andb a b) = orb (negb a) (negb b).

Proof.
  intros.
  destruct a.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Proposition de_morgan_1 :
forall P Q, ~(P \/ Q) -> ~P /\ ~Q.

Proof.
  unfold not.
  intros.
  split.
  - intro.
    apply H.
    left.
    assumption.
  - intro.
    apply H.
    right.
    assumption.
Qed.


Proposition de_morgan_2 :
forall P Q, ~P /\ ~Q -> ~(P \/ Q).

Proof.
  unfold not.
  intros.
  destruct H.
  destruct H0.
  - apply H.
    assumption.
  - apply H1.
    assumption.
Qed.


Proposition de_morgan_1_2 :
forall P Q, ~P /\ ~Q <-> ~(P \/ Q).

Proof.
  intros.
  split.
  - apply de_morgan_2.
  - apply de_morgan_1.
Qed.


Proposition de_morgan_classic:
forall P Q, ~P \/ ~Q <-> ~(P /\ Q).

Proof.
  admit.
Abort.


Proposition excluded_middle_irrefutable:
forall P:Prop, ~ ~ (P \/ ~ P).

Proof.
  unfold not.
  intros.
  apply H.
  right.
  intro.
  apply H.
  left.
  assumption.
Qed.


Proposition double_neg_implies_excluded :
(forall P: Prop, ~ ~ P -> P) -> (forall P, (P \/ ~ P)).

Proof.
intros.
apply H.
apply excluded_middle_irrefutable.
Qed.


Proposition excluded_implies_demorgan:
(forall R : Prop, R \/ ~ R) ->
(forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q).

Proof.
unfold not.
intros.
destruct (H P).
- right.
  intros.
  apply H0.
  split.
  * assumption.
  * assumption.
- left.
  intros.
  apply H1.
  assumption.
Qed.