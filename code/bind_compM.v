Lemma neutrally_bind :
  forall P Q : Prop,
    P -> (P -> Q) -> Q.
(* begin hide *)
Proof.
  intros.
  apply H0.
  assumption.
Qed.
(* end hide *)

Lemma neutrally_compM :
  forall P Q R : Prop,
    (P -> Q) -> (Q -> R) -> (P -> R).
(* begin hide *)
Proof.
  intros.
  apply H0, H, H1.
Qed.
(* end hide *)

Lemma trivially_bind :
  forall P Q : Prop,
    True -> (P -> True) -> True.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma trivially_compM :
  forall P Q R : Prop,
    (P -> True) -> (Q -> True) -> (P -> True).
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Lemma excuse_bind :
  forall E P Q : Prop,
    (E \/ P) -> (P -> E \/ Q) -> E \/ Q.
(* begin hide *)
Proof.
  intros E P Q [e | p] H.
    left. assumption.
    destruct (H p).
      left. assumption.
      right. assumption.
Qed.
(* end hide *)

Lemma excuse_compM :
  forall E P Q R : Prop,
    (P -> E \/ Q) -> (Q -> E \/ R) -> (P -> E \/ R).
(* begin hide *)
Proof.
  intros E P Q R peq qer p.
  destruct (peq p) as [e | q].
    left. assumption.
    destruct (qer q).
      left. assumption.
      right. assumption.
Qed.

Require Import W3.

Lemma classically_bind :
  forall P Q : Prop,
    (LEM -> P) -> (P -> (LEM -> Q)) -> (LEM -> Q).
(* begin hide *)
Proof.
  intros P Q p pq lem.
  apply pq.
    apply p. assumption.
    assumption.
Qed.
(* end hide *)

Lemma classically_compM :
  forall P Q R : Prop,
    (P -> (LEM -> Q)) -> (Q -> (LEM -> R)) -> (P -> (LEM -> R)).
(* begin hide *)
Proof.
  intros P Q R pq qr pr lem.
  apply qr.
    apply pq; assumption.
    assumption.
Qed.
(* end hide *)

Lemma axiomatically_bind :
  forall A P Q : Prop,
    (A -> P) -> (P -> (A -> Q)) -> (A -> Q).
(* begin hide *)
Proof.
  intros A P Q p pq a.
  apply pq.
    apply p. assumption.
    assumption.
Qed.
(* end hide *)

Lemma axiomatically_compM :
  forall A P Q R : Prop,
    (P -> (A -> Q)) -> (Q -> (A -> R)) -> (P -> (A -> R)).
(* begin hide *)
Proof.
  intros A P Q R pq qr p a.
  apply qr.
    apply pq; assumption.
    assumption.
Qed.
(* end hide *)

Lemma irrefutably_bind :
  forall P Q : Prop,
    ~ ~ P -> (P -> ~ ~ Q) -> ~ ~ Q.
(* begin hide *)
Proof.
  intros P Q p pq nq.
  apply p. intro pure_p.
  apply pq.
    assumption.
    assumption.
Qed.
(* end hide *)

Lemma irrefutably_compM :
  forall P Q R : Prop,
    (P -> ~ ~ Q) -> (Q -> ~ ~ R) -> (P -> ~ ~ R).
(* begin hide *)
Proof.
  intros P Q R pq qr p nr.
  apply pq.
    assumption.
    intro q. apply qr.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma indirectly_bind :
  forall C P Q : Prop,
    ((P -> C) -> C) -> (P -> ((Q -> C) -> C)) -> ((Q -> C) -> C).
(* begin hide *)
Proof.
  intros C P Q p pq qc.
  apply p. intro pure_p.
  apply pq.
    assumption.
    assumption.
Qed.
(* end hide *)

Lemma indirectly_compM :
  forall C P Q R : Prop,
    (P -> ((Q -> C) -> C)) -> (Q -> ((R -> C) -> C)) ->
      (P -> ((R -> C) -> C)).
(* begin hide *)
Proof.
  intros C P Q R pq qr p rc.
  apply pq.
    assumption.
    intro q. apply qr.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma omnidirectly_bind :
  forall P Q : Prop,
    (forall C : Prop, (P -> C) -> C) ->
    (P -> (forall C : Prop, (Q -> C) -> C)) ->
      (forall C : Prop, (Q -> C) -> C).
(* begin hide *)
Proof.
  intros P Q p pq C qc.
  apply p. intro pure_p.
  apply pq; assumption.
Qed.
(* end hide *)

Lemma omnidirectly_compM :
  forall P Q R : Prop,
    (P -> (forall C : Prop, (Q -> C) -> C)) ->
    (Q -> (forall C : Prop, (R -> C) -> C)) ->
      (P -> (forall C : Prop, (R -> C) -> C)).
(* begin hide *)
Proof.
  intros P Q R pq qr p C rc.
  apply pq.
    assumption.
    intro q. apply qr; assumption.
Qed.
(* end hide *)