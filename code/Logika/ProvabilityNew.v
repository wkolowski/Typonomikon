(** Zainspirowane przez podręcznik
    #<a class='link' href='https://www.ps.uni-saarland.de/~smolka/drafts/icl2021.pdf'>
    Modeling and Proving in Computational Type Theory Using the Coq Proof Assistant</a>#
    (rozdział 14). *)

Module Provability.

Axiom Provable : Prop -> Prop.

Definition Unprovable (P : Prop) : Prop :=
  ~ Provable P.

Definition Disprovable (P : Prop) : Prop :=
  Provable (~ P).

Definition Consistent (P : Prop) : Prop :=
  ~ Provable (~ P).

Definition Independent (P : Prop) : Prop :=
  ~ Provable P /\ ~ Provable (~ P).

Lemma Independent2Consistent :
  forall {P : Prop},
    Independent P -> Consistent P.
Proof.
  intros P [_ HC]; assumption.
Qed.

Lemma Consistent2Unprovable :
  forall {P : Prop},
    Consistent P -> Unprovable (~ P).
Proof.
  compute.
  intros P C U.
  apply C. assumption.
Qed.

Axiom PMP :
  forall P Q : Prop, Provable (P -> Q) -> Provable P -> Provable Q.

Axiom PI :
  forall P : Prop, Provable (P -> P).

Axiom PK :
  forall P Q : Prop, Provable Q -> Provable (P -> Q).

Axiom PC :
  forall P Q Z : Prop, Provable (P -> Q) -> Provable ((Q -> Z) -> P -> Z).

Lemma Provable_contraposition :
  forall P Q : Prop,
    Provable (P -> Q) -> ~ Provable Q -> ~ Provable P.
(* begin hide *)
Proof.
  intros P Q pq nq p.
  apply nq. eapply PMP; eassumption.
Qed.
(* end hide *)

Lemma Provable_contraposition' :
  forall P Q : Prop,
    Provable (P -> Q) -> Unprovable Q -> Unprovable P.
(* begin hide *)
Proof.
  intros P Q pq nq p.
  apply nq. eapply PMP; eassumption.
Qed.
(* end hide *)

Lemma Provable_Consistent :
  forall P Q : Prop,
    Provable (P -> Q) -> Consistent P -> Consistent Q.
(* begin hide *)
Proof.
  intros P Q ppq cp dq.
  apply cp.
  eapply PMP; cycle 1.
  - exact dq.
  - apply PC. assumption.
Qed.
(* end hide *)

Lemma sandwich :
  forall P Q Z : Prop,
    Consistent P -> Unprovable Q -> Provable (P -> Z) -> Provable (Z -> Q) -> Independent Z.
(* begin hide *)
Proof.
  intros P Q Z cp uq p2z z2q.
  split.
  - intros pz. apply uq. eapply PMP; eauto.
  - eapply Provable_Consistent; eauto.
Qed.
(* end hide *)

Lemma PropExt_PI_Provable : 
  (forall P Q : Prop, (P <-> Q) -> P = Q) ->
  forall P : Prop,
    P -> Provable P.
(* begin hide *)
Proof.
  intros PropExt P p.
  assert (H : P <-> (P <-> P)) by tauto.
  assert (H' : P = (P -> P)) by firstorder.
  rewrite H'.
  apply PI.
Qed.
(* end hide *)

End Provability.