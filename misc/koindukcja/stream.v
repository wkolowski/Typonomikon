Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Setoid.
Require Import FinFun.

Module Stream.

CoInductive stream (A : Type) : Type :=
    | scons : A -> stream A -> stream A.

Arguments scons [A].

Definition iid {A : Type} (s : stream A) : stream A :=
match s with
    | scons h t => scons h t
end.

Lemma iid_id :
  forall {A : Type} (s : stream A), s = iid s.
Proof.
  destruct s; trivial.
Defined.

Ltac step'_aux :=
fun n x =>
match goal with
    | |- context [x] =>
        do n (rewrite (iid_id x); cbn)
end.

Ltac step' n x := step'_aux ltac:(n) x.

Ltac step x := step'_aux ltac:(1) x.

Ltac step'_aux_hyp n x H :=
match goal with
    | H : context [x] |- _ =>
        do n (rewrite (iid_id x) in H; cbn in H)
end.

Ltac step'_hyp n x H := step'_aux_hyp ltac:(n) constr:(x) H.

Ltac step_hyp x H := step'_aux ltac:(1) constr:(x) H.

CoFixpoint theChosenOne : stream unit :=
  scons tt theChosenOne.

CoInductive sim {A : Type} : stream A -> stream A -> Prop :=
    | make_sim : forall (h1 h2 : A) (t1 t2 : stream A),
        h1 = h2 -> sim t1 t2 -> sim (scons h1 t1) (scons h2 t2).

Lemma sim_refl :
  forall (A : Type) (x : stream A), sim x x.
Proof.
  cofix.
  destruct x. constructor; auto.
Qed.

Lemma sim_sym :
  forall (A : Type) (x y : stream A),
    sim x y -> sim y x.
Proof.
  cofix.
  destruct 1. constructor; auto.
Qed.

Lemma sim_trans :
  forall (A : Type) (x y z : stream A),
    sim x y -> sim y z -> sim x z.
Proof.
  cofix.
  destruct 1; subst. destruct z. intro. constructor.
    inversion H; subst. trivial.
  apply sim_trans with t2.
    assumption.
    inversion H; subst. assumption.
Qed.

Instance Equiv_sim (A : Type) : Equivalence (@sim A).
Proof.
  split; red.
    apply sim_refl.
    apply sim_sym.
    apply sim_trans.
Defined.

Lemma all_chosen_unit_aux :
  forall s : stream unit, sim s theChosenOne.
Proof.
  cofix.
  intro. step theChosenOne. destruct s, u. constructor; auto.
Qed.

Theorem all_chosen_unit :
  forall x y : stream unit, sim x y.
Proof.
  intros. apply sim_trans with theChosenOne.
    apply all_chosen_unit_aux.
    apply sim_sym, all_chosen_unit_aux.
Qed.

Axiom sim_eq :
  forall (A : Type) (x y : stream A), sim x y -> x = y.

Theorem all_eq :
  forall x y : stream unit, x = y.
Proof.
  intros. apply sim_eq. apply all_chosen_unit.
Qed.

Definition unit_to_stream (u : unit) : stream unit := theChosenOne.
Definition stream_to_unit (s : stream unit) : unit := tt.

Theorem unit_is_stream :
  Bijective unit_to_stream.
Proof.
  red. exists stream_to_unit.
  split; intros.
    destruct x; trivial.
    apply all_eq.
Qed.

CoFixpoint memo_aux {A : Type} (f : nat -> A) (n : nat) : stream A :=
  scons (f n) (memo_aux f (S n)).

Definition memo {A : Type} (f : nat -> A) : stream A :=
  memo_aux f 0.

Fixpoint index {A : Type} (s : stream A) (n : nat) : A :=
match n, s with
    | 0, scons h _ => h
    | S n', scons _ t => index t n'
end.

Fixpoint drop {A : Type} (n : nat) (s : stream A) : stream A :=
match n, s with
    | 0, _ => s
    | S n', scons _ t => drop n' t
end.

Lemma aux :
  forall (s : stream nat) (n : nat),
    sim (memo_aux (index s) n) (drop n s).
Proof.
  cofix.
  intros. step (memo_aux (index s) n). rewrite (iid_id s) at 3.
  destruct s. cbn. rewrite <- aux. step (memo_aux (index (scons n0 s)) n).
  constructor; auto. apply sim_refl.
Restart.
  cofix.
  intros. destruct s as [h t], n as [| n']; cbn; intros.
    step (memo_aux (index (scons h t)) 0). constructor; auto. apply aux.
    step (memo_aux (index (scons h t)) (S n')). case_eq (drop n' t); intros.
      constructor.
        admit.
        induction n'; destruct t. cbn in H. (*
    rewrite <- aux. step (memo_aux (index (scons h t)) (S n')).
      step (memo_aux (index t) n'). constructor; auto.*)
Restart.
  intros s n. generalize dependent s.
  induction n as [| n']; cbn; intros.
    destruct s. step (memo_aux (index (scons n s)) 0). constructor; auto.
Admitted.

Lemma auxzor :
  forall (f : nat -> nat) (n : nat),
    sim (memo_aux f n) (memo_aux (fun k : nat => f (n + k)) 0).
Proof.
  intros. remember 0 as w. generalize dependent w.
  cofix.
  intros.
  step (memo_aux f n). step (memo_aux (fun k : nat => f (n + k)) w).
  constructor.
    rewrite Heqw, <- plus_n_O. trivial.
Abort.

Lemma index_memo_aux :
  forall (A : Type) (f : nat -> A) (n : nat),
    index (memo_aux f n) = fun k : nat => f (k + n).
Proof.
  intros. extensionality k. generalize dependent n.
  induction k as [| k']; cbn; intros.
      trivial.
      rewrite IHk'. f_equal. omega.
Qed.

Lemma index_memo :
  forall (A : Type) (f : nat -> A),
    index (memo f) = fun k : nat => f k.
Proof.
  intros. change (memo f) with (memo_aux f 0).
  replace (fun k : nat => f k) with (fun k : nat => f (k + 0)).
    apply index_memo_aux.
    extensionality k. rewrite <- plus_n_O. trivial.
Qed.

Theorem natfun_is_stream_nat :
  Bijective (@memo nat).
Proof.
  red. exists index. split; intros.
    extensionality n. replace (memo x) with (memo_aux x 0).
      rewrite aux'. rewrite <- plus_n_O. trivial.
      step (memo x). step (memo_aux x 0). trivial.
    apply sim_eq. generalize dependent y. cofix. intro.
      step (memo (index y)). destruct y. constructor.
        trivial.
        apply aux.
Defined.

CoInductive coeq {A : Type} (x : A) : A -> Prop :=
    | coeq_refl : coeq x x.
(*    | coeq_wut :
        forall y : A, coeq x y -> coeq x y.
*)

Theorem eq_coeq :
  forall (A : Type) (x y : A), x = y <-> coeq x y.
Proof.
  split; destruct 1; constructor.
Defined.

Theorem sim_coeq :
  forall (A : Type) (x y : stream A),
    sim x y -> coeq x y.
Proof.
  cofix H.
  destruct x, y. intro. destruct H0; subst.
  destruct (eq_coeq (stream A) (scons h2 t1) (scons h2 t2)).
  apply H0. f_equal.
  destruct (eq_coeq (stream A) t1 t2).
  apply H4.
  apply H. Guarded. assumption.
Qed.