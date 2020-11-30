Require Import F2.

CoInductive sim2 (n m : conat) : Prop :=
{
    sim2' :
      (pred n = None /\ pred m = None)
        \/
      (exists n' m' : conat,
        sim2 n (succ n') /\ sim2 m (succ m') /\ sim2 n' m')
}.

Lemma sim2_refl :
  forall n : conat,
    sim2 n n.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct n as [[n' |]]; cbn.
    right. exists n', n'. split.
      apply CH.
      split; apply CH.
    left. split; reflexivity.
Qed.
(* end hide *)

Lemma sim2_symm :
  forall n m : conat,
    sim2 n m -> sim2 m n.
(* begin hide *)
Proof.

Admitted.
(* end hide *)

Lemma sim2_trans :
  forall a b c : conat,
    sim2 a b -> sim2 b c -> sim2 a c.
(* begin hide *)
Proof.

Admitted.
(* end hide *)

Lemma sim_sim2 :
  forall n m : conat,
    sim n m -> sim2 n m.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [[H | (n' & m' & H1 & H2 & H3)]].
    constructor. left. assumption.
    constructor. right. exists n', m'. split.
      apply CH. constructor. right. exists n', n'. split.
        assumption.
        split.
          cbn. reflexivity.
          apply sim_refl.
      split.
        apply CH. constructor. right. exists m', m'. split.
          assumption.
          split.
            cbn. reflexivity.
            apply sim_refl.
        apply CH. assumption.
Qed.
(* end hide *)

Lemma sim2_add :
  forall n1 n2 m1 m2 : conat,
    sim2 n1 n2 -> sim2 m1 m2 -> sim2 (add n1 m1) (add n2 m2).
(* begin hide *)
Proof.
  cofix CH.
  intros n1 n2 m1 m2.
  destruct 1 as [[[H11 H12] | (n1' & n2' & H11 & H12 & H13)]];
  destruct 1 as [[[H21 H22] | (m1' & m2' & H21 & H22 & H23)]].
    constructor. left. cbn. rewrite H11, H12. split; assumption.
    constructor. right. exists m1', m2'. split.
      admit.
      split.
        admit.
        assumption.
    constructor. right. exists n1', n2'. split.
      admit.
      split.
        admit.
        assumption.
    constructor. right. exists (add n1' m1), (add n2' m2). split.
      admit.
      split.
        admit.
        eapply CH.
          eassumption.
          eapply sim2_trans.
            eassumption.
            eapply sim2_trans.
              Focus 2. apply sim2_symm. eassumption.
              constructor. right. exists m1', m2'. split.
                apply sim2_refl.
                split.
                  apply sim2_refl.
                  assumption.
Admitted.
(* end hide *)
