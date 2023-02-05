Require Import Setoid.

From Typonomikon Require Import F3.

Module FirstTry.

Variant BisimCF (F : conat -> conat -> Prop) : NatF conat -> NatF conat -> Prop :=
| BisimC_Z : BisimCF F Z Z
| BisimC_S : forall n1 n2 : conat, F n1 n2 -> BisimCF F (S n1) (S n2)
| BisimC_comm :
    forall n1 n2 : conat,
      BisimCF F (out (add n1 n2)) (out (add n2 n1)).

CoInductive BisimC (n1 n2 : conat) : Prop :=
{
  BisimC_out : BisimCF BisimC (out n1) (out n2);
}.

Lemma from_sim :
  forall n1 n2 : conat,
    sim n1 n2 -> BisimC n1 n2.
Proof.
  cofix CH.
  intros n1 n2 [H].
  constructor.
  inversion H; constructor.
  now apply CH.
Qed.

Lemma BisimC_add_comm :
  forall n1 n2 : conat,
    BisimC (add n1 n2) (add n2 n1).
Proof.
  do 2 constructor.
Qed.

#[export]
Instance Equivalence_BisimC : Equivalence BisimC.
Proof.
  split; red.
  - cofix CH.
    constructor.
    destruct (out x); constructor.
    now apply CH.
  - cofix CH.
    intros n1 n2 [H].
    constructor.
    inversion H.
    + now constructor.
    + constructor.
      now apply CH.
    + cbn in *.
      destruct (out n0) as [| n0'] eqn: Heq0,
               (out n3) as [| n3'] eqn: Heq3;
        constructor.
      * apply from_sim.
        now rewrite add_zero_r'.
      * apply from_sim.
        now rewrite add_zero_r'.
      * admit.
  -
Admitted.

Lemma BisimC_trans :
  forall a b c : conat,
    BisimC a b -> BisimC b c -> BisimC a c.
Proof.
  cofix CH.
  intros a b c [ab] [bc].
  constructor.
  inversion ab; inversion bc.
  - now constructor.
  - now congruence.
  - now congruence.
  - now congruence.
  - constructor.
    eapply CH with n2; [easy |].
    now congruence.
  - cbn in *.
    destruct (out n3) as [| n3'] eqn: Heq.
    + rewrite H4 in H3.
      destruct (out c) as [| c'] eqn: Heqc.
      * now congruence.
      * rewrite H4.
        constructor.
        admit.
    + constructor.
Admitted.

Lemma BisimC_Bisim :
  forall n1 n2 : conat,
    BisimC n1 n2 -> sim n1 n2.
Proof.
  cofix CH.
  intros n1 n2 [H].
  constructor.
  inversion H.
  - now constructor.
  - now constructor; apply CH.
  - cbn in *.
    destruct (out n0) as [| n0'] eqn: Heq0,
             (out n3) as [| n3'] eqn: Heq3.
    + now constructor.
    + constructor.
      now rewrite add_zero_r'.
    + constructor.
      now rewrite add_zero_r'.
    + constructor.
      apply CH.
      rewrite (BisimC_add_comm n0'), (BisimC_add_comm n3').
      constructor; cbn.
      rewrite Heq0, Heq3.
      constructor.
      do 2 constructor.
Qed.

End FirstTry.

Module SecondTry.

Variant BisimCF (F : conat -> conat -> Prop) : NatF conat -> NatF conat -> Prop :=
| BisimCF_Z : BisimCF F Z Z
| BisimCF_S : forall n1 n2 : conat, F n1 n2 -> BisimCF F (S n1) (S n2)
| BisimCF_comm :
    forall n1 n2 n2' n n' : conat,
      out n2 = S n2' -> out n = S n' ->
        F (add n1 n2') n' -> BisimCF F (out (add n1 n2)) (out n).

CoInductive BisimC (n1 n2 : conat) : Prop :=
{
  BisimC_out : BisimCF BisimC (out n1) (out n2);
}.

Lemma from_sim :
  forall n1 n2 : conat,
    sim n1 n2 -> BisimC n1 n2.
Proof.
  cofix CH.
  intros n1 n2 [H].
  constructor.
  inversion H; constructor.
  now apply CH.
Qed.

Lemma BisimC_add_comm :
  forall n1 n2 : conat,
    BisimC (add n1 n2) (add n2 n1).
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n1) as [| n1'] eqn: Heq1,
           (out n2) as [| n2'] eqn: Heq2;
    constructor.
  - apply from_sim.
    now rewrite add_zero_r'.
  - apply from_sim.
    now rewrite add_zero_r'.
  - constructor.
    
Admitted.

#[export]
Instance Equivalence_BisimC : Equivalence BisimC.
Proof.
  split; red.
  - cofix CH.
    constructor.
    destruct (out x); constructor.
    now apply CH.
  - cofix CH.
    intros n1 n2 [H].
    constructor.
    inversion H.
    + now constructor.
    + constructor.
      now apply CH.
Admitted.
(*
    + econstructor 3; [eassumption.. |].
      now apply CH.
  - cofix CH.
    intros a b c [ab] [bc].
    constructor.
    inversion ab; inversion bc.
    + now constructor.
    + now congruence.
    + now congruence.
    + now congruence.
    + constructor.
      eapply CH with n2; [easy |].
      now congruence.
    +
 cbn in *.
      destruct (out n3) as [| n3'] eqn: Heq.
      + rewrite H4 in H3.
        destruct (out c) as [| c'] eqn: Heqc.
        * now congruence.
        * rewrite H4.
          constructor.
          admit.
   cbn in *.
        destruct (out n0) as [| n0'] eqn: Heq0,
                 (out n3) as [| n3'] eqn: Heq3;
          constructor.
        * apply from_sim.
          now rewrite add_zero_r'.
        * apply from_sim.
          now rewrite add_zero_r'.
        *
Admitted.
*)

Lemma BisimC_Bisim :
  forall n1 n2 : conat,
    BisimC n1 n2 -> sim n1 n2.
Proof.
  cofix CH.
  intros n1 n2 [H].
  constructor.
  inversion H.
  - now constructor.
  - now constructor; apply CH.
  - cbn in *.
    destruct (out n0) as [| n0'] eqn: Heq0,
             (out n3) as [| n3'] eqn: Heq3.
Admitted.
(*
    + now constructor.
    + constructor.
      now rewrite add_zero_r'.
    + constructor.
      now rewrite add_zero_r'.
    + constructor.
      apply CH.
Admitted.
*)

End SecondTry.