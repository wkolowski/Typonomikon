CoInductive conat : Type :=
{
    pred : option conat;
}.

CoInductive sim (n m : conat) : Prop :=
{
    sim' :
      (pred n = None /\ pred m = None) \/
      exists n' m' : conat,
        pred n = Some n' /\ pred m = Some m' /\ sim n' m'
}.

Lemma sim_refl :
  forall n : conat, sim n n.
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]]; cbn.
    right. exists n', n'. do 2 split; try reflexivity. apply CH.
    left. do 2 constructor.
Qed.

Lemma sim_sym :
  forall n m : conat, sim n m -> sim m n.
Proof.
  cofix CH.
  constructor. destruct H as [[[] | (n' & m' & H1 & H2 & H3)]].
    auto.
    right. exists m', n'. do 2 (split; auto).
Qed.

Lemma sim_trans :
  forall a b c : conat, sim a b -> sim b c -> sim a c.
Proof.
  cofix CH.
  constructor.
  destruct H as [[[] | (n' & m' & H1 & H2 & H3)]].
    left. destruct H0. decompose [ex or and] sim'0; split; congruence.
    right. destruct H0. decompose [ex or and] sim'0.
      congruence.
      exists n', x0. do 2 (try split; auto). eapply CH. eauto. congruence.
Qed.

Require Import Setoid.

Instance Equivalence_sim : Equivalence sim.
Proof.
  esplit; red.
    apply sim_refl.
    apply sim_sym.
    apply sim_trans.
Defined.

Definition zero : conat :=
{|
    pred := None;
|}.

Definition succ (n : conat) : conat :=
{|
    pred := Some n;
|}.

CoFixpoint add (n m : conat) : conat :=
{|
    pred :=
      match pred n with
          | None => pred m
          | Some n' => Some (add n' m)
      end
|}.

Lemma add_zero_l :
  forall n : conat, sim (add zero n) n.
Proof.
  constructor; cbn. destruct n as [[n' |]]; cbn.
    right. exists n', n'. do 2 split; try reflexivity.
    left. auto.
Qed.

Lemma add_zero_r :
  forall n : conat, sim (add n zero) n.
Proof.
  cofix CH.
  constructor; cbn. destruct n as [[n' |]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity. apply CH.
    left. auto.
Qed.

Lemma add_assoc :
  forall a b c : conat, sim (add (add a b) c) (add a (add b c)).
Proof.
  cofix CH.
  constructor.
  destruct a as [[|]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity. apply CH.
    destruct b as [[|]]; cbn.
      right. do 2 eexists. do 2 split; try reflexivity. apply sim_refl.
Qed.

Lemma add_succ_l :
  forall n m : conat, sim (add (succ n) m) (add n (succ m)).
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity. apply CH.
    right. do 2 eexists. do 2 split; try reflexivity. apply add_zero_l.
Qed.

Lemma add_succ_r :
  forall n m : conat, sim (add n (succ m)) (add (succ n) m).
Proof.
  intros. apply sim_sym, add_succ_l.
Qed.

Ltac inv H := inversion H; subst; clear H; auto.

Lemma sim_succ_succ :
  forall n m : conat, sim n m -> sim (succ n) (succ m).
Proof.
  constructor. cbn. right. exists n, m. auto.
Qed.

Lemma sim_pred_pred :
  forall n n' m m' : 

Lemma add_comm :
  forall n m : conat, sim (add n m) (add m n).
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]], m as [[m' |]]; cbn.
    Focus 2. right. do 2 eexists. do 2 split; try reflexivity.
      apply add_zero_r.
    Focus 2. right. do 2 eexists. do 2 split; try reflexivity.
      apply sim_sym. apply add_zero_r.
    Focus 2. auto.
    right. do 2 eexists. do 2 split; try reflexivity.
      eapply sim_trans with (add (succ n') m').
        rewrite add_succ_l. unfold succ. reflexivity.
        unfold succ. apply CH.
Qed.
      
      apply sim_trans with (add {| pred := Some m'; |} n').
        apply CH.
        destruct m'; cbn. Focus 2.