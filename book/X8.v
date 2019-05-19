(** * X8: Liczby konaturalne *)

(** TODO: coś tu napisać. *)

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

Axiom sim_eq :
  forall n m : conat, sim n m -> n = m.

Lemma sim_refl :
  forall n : conat, sim n n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]]; cbn.
    right. exists n', n'. do 2 split; try reflexivity. apply CH.
    left. do 2 constructor.
Qed.
(* end hide *)

Lemma sim_sym :
  forall n m : conat, sim n m -> sim m n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[[] | (n' & m' & H1 & H2 & H3)]].
    auto.
    right. exists m', n'. do 2 (split; auto).
Qed.
(* end hide *)

Lemma sim_trans :
  forall a b c : conat, sim a b -> sim b c -> sim a c.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct H as [[[] | (n' & m' & H1 & H2 & H3)]].
    left. destruct H0. decompose [ex or and] sim'0; split; congruence.
    right. destruct H0. decompose [ex or and] sim'0.
      congruence.
      exists n', x0. do 2 (try split; auto). eapply CH. eauto. congruence.
Qed.
(* end hide *)

Require Import Setoid.

Instance Equivalence_sim : Equivalence sim.
(* begin hide *)
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
(* begin hide *)
Proof.
  constructor; cbn. destruct n as [[n' |]]; cbn.
    right. exists n', n'. do 2 split; try reflexivity.
    left. auto.
Qed.
(* end hide *)

Lemma add_zero_r :
  forall n : conat, sim (add n zero) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn. destruct n as [[n' |]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity. apply CH.
    left. auto.
Qed.
(* end hide *)

Lemma add_assoc :
  forall a b c : conat, sim (add (add a b) c) (add a (add b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[|]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity. apply CH.
    destruct b as [[|]]; cbn.
      right. do 2 eexists. do 2 split; try reflexivity. apply sim_refl.
Qed.
(* end hide *)

Lemma add_succ_l :
  forall n m : conat, sim (add (succ n) m) (add n (succ m)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity. apply CH.
    right. do 2 eexists. do 2 split; try reflexivity. apply add_zero_l.
Qed.
(* end hide *)

Lemma add_succ_r :
  forall n m : conat, sim (add n (succ m)) (add (succ n) m).
(* begin hide *)
Proof.
  intros. apply sim_sym, add_succ_l.
Qed.
(* end hide *)

Ltac inv H := inversion H; subst; clear H; auto.

Lemma sim_succ_succ :
  forall n m : conat, sim n m -> sim (succ n) (succ m).
(* begin hide *)
Proof.
  constructor. cbn. right. exists n, m. auto.
Qed.
(* end hide *)

Lemma add_comm :
  forall n m : conat, sim (add n m) (add m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]], m as [[m' |]]; cbn.
    Focus 2. right. do 2 eexists. do 2 split; try reflexivity.
      apply add_zero_r.
    Focus 2. right. do 2 eexists. do 2 split; try reflexivity.
      apply sim_sym. apply add_zero_r.
    Focus 2. auto.
    specialize (CH n' (succ m')).
    right. do 2 eexists. do 2 split; try reflexivity.
      rewrite (sim_eq _ _ (add_succ_l _ _)) in CH. apply CH.
Qed.
(* end hide *)

CoInductive le (n m : conat) : Prop :=
{
    le' :
      pred n = None \/
      exists n' m' : conat,
        pred n = Some n' /\
        pred m = Some m' /\ le n' m'
}.

Lemma le_refl :
  forall n : conat, le n n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity. apply CH.
    left. reflexivity.
Qed.
(* end hide *)

Lemma le_trans :
  forall a b c : conat, le a b -> le b c -> le a c.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H, H0.
  decompose [or ex and] le'0; clear le'0.
    left. assumption.
    decompose [or ex and] le'1; clear le'1.
      congruence.
      rewrite H in H3. inv H3. right. do 2 eexists. split.
        eassumption.
        split.
          eassumption.
          eapply CH; eauto.
Qed.
(* end hide *)

Lemma le_sim :
  forall n n' m m' : conat,
    sim n n' -> sim m m' -> le n m -> le n' m'.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H1. decompose [or ex and] le'0; clear le'0.
    left. destruct H. decompose [or and ex] sim'0.
      assumption.
      congruence.
    right. exists x, x0. split; [idtac | split].
      destruct H.
Abort.
(* end hide *)

Lemma le_add_l :
  forall n m : conat, le n (add n m).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity. apply CH.
    left. reflexivity.
Qed.
(* end hide *)

Lemma le_add_r :
  forall n m : conat, le m (add n m).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]], m as [[m' |]]; cbn.
    right. do 2 eexists. do 2 split; try reflexivity.
Abort.
(* end hide *)

Lemma le_add_l' :
  forall n n' m : conat,
    le n n' -> le (add n m) (add n' m).
Proof.
Admitted.

Lemma le_add_r' :
  forall n m m' : conat,
    le m m' -> le (add n m) (add n m').
Proof.
Admitted.

Lemma le_add :
  forall n n' m m' : conat,
    le n n' -> le m m' -> le (add n m) (add n' m').
Proof.
Admitted.

Lemma le_succ_r :
  forall n m : conat, le n m -> le n (succ m).
Proof.
Admitted.

Lemma le_succ :
  forall n m : conat, le n m -> le (succ n) (succ m).
Proof.
Admitted.





CoFixpoint sub (n m : conat) : conat :=
{|
    pred :=
      match pred n, pred m with
          | _, None => pred n
          | None, _ => None
          | Some n', Some m' => Some (sub n' m')
      end;
|}.
