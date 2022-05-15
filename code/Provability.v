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

Definition PMP : Prop :=
  forall P Q : Prop, Provable (P -> Q) -> Provable P -> Provable Q.

Definition PI : Prop :=
  forall P : Prop, Provable (P -> P).

Definition PK : Prop :=
  forall P Q : Prop, Provable Q -> Provable (P -> Q).

Definition PC : Prop :=
  forall P Q Z : Prop, Provable (P -> Q) -> Provable ((Q -> Z) -> P -> Z).

Definition UF : Prop :=
  Unprovable False.

Axiom Unprovable_False : Unprovable False.

Definition extract : Prop :=
  forall (P : Prop), Provable P -> P.

Lemma Provable_contraposition :
  PMP ->
  forall P Q : Prop,
    Provable (P -> Q) -> ~ Provable Q -> ~ Provable P.
(* begin hide *)
Proof.
  intros pmp P Q pq nq p.
  apply nq. eapply pmp; eassumption.
Qed.
(* end hide *)

Lemma Provable_contraposition' :
  PMP ->
  forall P Q : Prop,
    Provable (P -> Q) -> Unprovable Q -> Unprovable P.
(* begin hide *)
Proof.
  compute.
  intros pmp P Q pq nq p.
  apply nq. eapply pmp; eassumption.
Qed.
(* end hide *)

Lemma Provable_Consistent :
  PMP -> PC ->
  forall P Q : Prop,
    Provable (P -> Q) -> Consistent P -> Consistent Q.
(* begin hide *)
Proof.
  unfold PMP, PC.
  intros pmp pc P Q ppq cp dq.
  apply cp.
  specialize (pc _ _ False ppq).
  specialize (pmp _ _ pc).
  apply pmp.
  assumption.
Qed.
(* end hide *)

Lemma sandwich :
  PMP -> PK -> PC ->
  forall P Q Z : Prop,
    Consistent P -> Unprovable Q -> Provable (P -> Z) -> Provable (Z -> Q) -> Independent Z.
(* begin hide *)
Proof.
  unfold PMP, PK, PC (* Consistent, Unprovable, Independent *).
  intros pmp pk pc P Q Z cp uq p2z z2q.
  split.
  - intros pz. apply uq. eapply pmp; eauto.
  - eapply Provable_Consistent; eauto.
Qed.
(* end hide *)

Lemma PropExt_PI_Provable : 
  (forall P Q : Prop, (P <-> Q) -> P = Q) ->
  PI ->
  forall P : Prop,
    P -> Provable P.
(* begin hide *)
Proof.
  compute.
  intros PropExt PI P p.
  assert (H : P <-> (P <-> P)) by tauto.
  assert (H' : P = (P -> P)) by firstorder.
  rewrite H'.
  apply PI.
Qed.
(* end hide *)

End Provability.