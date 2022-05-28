(** Zainspirowane przez podręcznik
    #<a class='link' href='https://www.ps.uni-saarland.de/~smolka/drafts/icl2021.pdf'>
    Modeling and Proving in Computational Type Theory Using the Coq Proof Assistant</a>#
    (rozdział 14). *)

Class Provability : Type :=
{
  Provable : Prop -> Prop;
  PMP : forall P Q : Prop, Provable (P -> Q) -> Provable P -> Provable Q;
  PI  : forall P : Prop, Provable (P -> P);
  PK  : forall P Q : Prop, Provable Q -> Provable (P -> Q);
  PC  : forall P Q Z : Prop, Provable (P -> Q) -> Provable ((Q -> Z) -> P -> Z)
}.

Section AbstractProvability.

Context
  (Prv : Provability).

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

Lemma ex_14_1_4 :
  forall P Q : Prop,
    Provable (P -> Q) -> Consistent P -> Unprovable Q ->
      Independent P /\ Independent Q.
(* begin hide *)
Proof.
  intros P Q ppq cp uq. split.
  - eapply sandwich; eauto. apply PI.
  - eapply sandwich; eauto. apply PI.
Qed.
(* end hide *)

Lemma PE_Provable_False :
  (forall P : Prop, Provable False -> Provable P) ->
  Provable False <-> forall P : Prop, Provable P.
(* begin hide *)
Proof.
  intros PE. split.
  - intros pf P. apply PE. assumption.
  - intros PPP. apply PPP.
Qed.
(* end hide *)

Lemma Unprovable_False__Consistent_NotFalse :
  Unprovable False -> Consistent (~ False).
(* begin hide *)
Proof.
  unfold Unprovable, Consistent.
  intros f g.
  eapply (PMP (~ False) False) in g.
  - contradiction.
  - apply PI.
Qed.
(* end hide *)

Lemma Consistent_NotFalse__Consistent_Any :
  Consistent (~ False) -> exists P : Prop, Consistent P.
(* begin hide *)
Proof.
  intros cnf. exists (~ False). assumption.
Qed.
(* end hide *)

Lemma Consistent_Any__Provable_Consistent :
  (exists P : Prop, Consistent P) ->
    forall P : Prop, Provable P -> Consistent P.
(* begin hide *)
Proof.
(*   unfold Unprovable, Consistent. *)
  intros [X cx] P p.
  apply Provable_Consistent with X.
  - apply PK. assumption.
  - assumption.
Qed.
(* end hide *)

Lemma Provable_Consistent__Disprovable_Unprovable :
  (forall P : Prop, Provable P -> Consistent P) ->
  forall P : Prop, Disprovable P -> Unprovable P.
(* begin hide *)
Proof.
  unfold Consistent, Disprovable, Unprovable.
  intros H P dp np.
  eapply H; eassumption.
Qed.
(* end hide *)

Lemma Disprovable_Unprovable__Unprovable_False :
  (forall P : Prop, Disprovable P -> Unprovable P) ->
    Unprovable False.
(* begin hide *)
Proof.
  unfold Disprovable, Unprovable.
  intros H.
  apply H.
  apply PI.
Qed.
(* end hide *)

End AbstractProvability.

#[refine]
#[export]
Instance Provability_id : Provability :=
{|
  Provable P := P;
|}.
(* begin hide *)
Proof.
  all: tauto.
Defined.
(* end hide *)

#[refine]
#[export]
Instance Provability_True : Provability :=
{|
  Provable _ := True;
|}.
(* begin hide *)
Proof.
  all: tauto.
Defined.
(* end hide *)