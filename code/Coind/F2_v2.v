(** * F2: Liczby konaturalne [TODO] *)

(** Zdefiniuj liczby konaturalne oraz ich relację bipodobieństwa. Pokaż,
    że jest to relacja równoważności. *)

(* begin hide *)
Inductive NatF (X : Type) : Type :=
    | Z : NatF X
    | S : X -> NatF X.

Arguments Z {X}.
Arguments S {X} _.

CoInductive conat : Type :=
{
    out : NatF conat;
}.

Inductive simF (n m : conat) (R : conat -> conat -> Prop) : Prop :=
    | simF_Z :
        forall (Hn : out n = Z) (Hm : out m = Z), simF n m R
    | simf_S :
        forall (n' m' : conat) (Hn : out n = S n') (Hm : out m = S m'),
          R n' m' -> simF n m R.

CoInductive sim (n m : conat) : Prop :=
{
    sim' : simF n m sim;
}.

Axiom sim_eq :
  forall {n m : conat}, sim n m -> n = m.

Lemma eq_out :
  forall n m : conat, out n = out m -> n = m.
(* begin hide *)
Proof.
  destruct n, m. cbn. destruct 1. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Ltac inv H := inversion H; subst; clear H; auto.
(* end hide *)

Lemma sim_refl :
  forall n : conat, sim n n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']]; cbn.
    left; cbn; reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma sim_sym :
  forall n m : conat, sim n m -> sim m n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[| n' m' H1 H2 H3]].
    constructor; assumption.
    eright; try eassumption. apply CH. assumption.
Qed.
(* end hide *)

Lemma sim_trans :
  forall a b c : conat, sim a b -> sim b c -> sim a c.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct H as [[| n' m' H1 H2 H3]].
    left.
      assumption.
      destruct H0 as [[]]; congruence.
    destruct H0 as [[]].
      congruence.
      eright; try eassumption. eapply CH.
        eassumption.
        congruence.
Qed.
(* end hide *)

(** Dzięki poniższemu będziemy mogli używac taktyki [rewrite] do
    przepisywania [sim] tak samo jak [=]. *)

Require Import Setoid.

Instance Equivalence_sim : Equivalence sim.
(* begin hide *)
Proof.
  esplit; red.
    apply sim_refl.
    apply sim_sym.
    apply sim_trans.
Defined.
(* end hide *)

(** * Zero, następnik i nieskończoność *)

(** Zdefiniuj zero, następnik oraz liczbę [omega] - jest to nieskończona
    liczba konaturalna, która jest sama swoim poprzednikiem. Udowodnij
    ich kilka podstawowych właściwości. *)

(* begin hide *)
Definition zero : conat :=
{|
    out := Z;
|}.

Definition succ (n : conat) : conat :=
{|
    out := S n;
|}.

CoFixpoint omega : conat :=
{|
    out := S omega;
|}.
(* end hide *)

Lemma succ_out :
  forall n m : conat,
    n = succ m <-> out n = S m.
(* begin hide *)
Proof.
  split; intro.
    rewrite H. cbn. reflexivity.
    destruct n as [[| n']]; inv H.
Qed.
(* end hide *)

Lemma zero_not_omega :
  ~ sim zero omega.
(* begin hide *)
Proof.
  destruct 1 as [[H1 H2 | zero' omega' H1 H2 H3]].
    cbn in H2. inv H2.
    cbn in H1. inv H1.
Qed.
(* end hide *)

Lemma sim_succ_omega :
  forall n : conat, sim n (succ n) -> sim n omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn.
  destruct H as [[H1 H2 | n' succn' H1 H2 H3]]; cbn in *.
    inv H2.
    eright.
      eassumption.
      cbn. reflexivity.
      apply CH. apply succ_out in H1. rewrite <- H1. inv H2.
Qed.
(* end hide *)

Lemma succ_omega :
  omega = succ omega.
(* begin hide *)
Proof.
  apply eq_out. cbn. reflexivity.
Qed.
(* end hide *)

Lemma sim_succ :
  forall n m : conat, sim n m -> sim (succ n) (succ m).
(* begin hide *)
Proof.
  constructor. cbn. right with n m; auto.
Defined.
(* end hide *)

Lemma sim_succ_inv :
  forall n m : conat, sim (succ n) (succ m) -> sim n m.
(* begin hide *)
Proof.
  destruct 1 as [[H1 H2 | n' m' H1 H2 H3]].
    inv H1.
    cbn in *. inv H1. inv H2.
Qed.
(* end hide *)

(** * Dodawanie *)

(** Zdefiniuj dodawanie liczb konaturalnych i udowodnij jego podstawowe
    właściwości. *)

(* begin hide *)
CoFixpoint add (n m : conat) : conat :=
{|
    out :=
      match out n with
          | Z => out m
          | S n' => S (add n' m)
      end
|}.
(* end hide *)

Lemma add_zero_l :
  forall n : conat, sim (add zero n) n.
(* begin hide *)
Proof.
  constructor; cbn.
  destruct n as [[| n']]; cbn.
    left; reflexivity.
    right with n' n'; cbn; reflexivity.
Qed.
(* end hide *)

Lemma add_zero_r :
  forall n : conat, sim (add n zero) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct n as [[| n']]; cbn.
    left; cbn; reflexivity.
    right with (n' := add n' zero) (m' := n'); cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma sim_add_zero :
  forall n m : conat,
    sim (add n m) zero -> sim n zero /\ sim m zero.
(* begin hide *)
Proof.
  destruct n as [[]], m as [[]]; cbn; intros.
    split; repeat constructor.
    1-3: destruct H as [[]]; cbn in *; congruence.
Qed.
(* end hide *)

Lemma add_omega_l :
  forall n : conat, sim (add omega n) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  right with (add omega n) omega; cbn.
    1-2: reflexivity.
    apply CH.
Qed.
(* end hide *)

Lemma add_omega_r :
  forall n : conat, sim (add n omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']]; cbn.
    right with omega omega; cbn; reflexivity.
    right with (add n' omega) omega; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma add_succ_l :
  forall n m : conat, sim (add (succ n) m) (add n (succ m)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct n as [[]]; cbn.
    eright; cbn; try reflexivity. apply add_zero_l.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma add_succ_r :
  forall n m : conat, sim (add n (succ m)) (add (succ n) m).
(* begin hide *)
Proof.
  intros. apply sim_sym, add_succ_l.
Qed.
(* end hide *)

Lemma add_succ_l' :
  forall n m : conat, sim (add (succ n) m) (succ (add n m)).
(* begin hide *)
Proof.
  constructor. eright; cbn; auto. reflexivity.
Qed.
(* end hide *)

Lemma add_succ_r' :
  forall n m : conat, sim (add n (succ m)) (succ (add n m)).
(* begin hide *)
Proof.
  intros. rewrite <- add_succ_l. apply add_succ_l'.
Qed.
(* end hide *)

Lemma eq_sim :
  forall n m : conat, n = m -> sim n m.
(* begin hide *)
Proof.
  destruct 1.
  apply sim_refl.
Qed.
(* end hide *)

Lemma add_assoc :
  forall a b c : conat, sim (add (add a b) c) (add a (add b c)).
(* begin hide *)
Proof.
  cofix CH.
  destruct a as [[]]; cbn; intros.
    apply eq_sim, eq_out. cbn. reflexivity.
    constructor. eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma add_comm :
  forall n m : conat, sim (add n m) (add m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']], m as [[| m']]; cbn.
    left; cbn; reflexivity.
    eright; cbn; try reflexivity. rewrite add_zero_r. apply sim_refl.
    eright; cbn; try reflexivity. rewrite add_zero_r. apply sim_refl.
    eright; cbn; try reflexivity. change {| out := S m' |} with (succ m').
      rewrite add_succ_r. unfold succ. apply CH.
Admitted.
(* end hide *)

Lemma sim_add_zero_l :
  forall n m : conat,
    sim (add n m) zero -> sim n zero.
(* begin hide *)
Proof.
  intros.
  apply sim_add_zero in H.
  destruct H. assumption.
Qed.
(* end hide *)

Lemma sim_add_zero_r :
  forall n m : conat,
    sim (add n m) zero -> sim m zero.
(* begin hide *)
Proof.
  intros.
  apply sim_add_zero in H.
  destruct H. assumption.
Qed.
(* end hide *)

Lemma add_zero_l' :
  forall n m : conat,
    out n = Z -> sim (add n m) m.
(* begin hide *)
Proof.
  intros. replace n with zero.
    apply add_zero_l.
    apply eq_out. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma add_zero_r' :
  forall n m : conat,
    out m = Z -> sim (add n m) n.
(* begin hide *)
Proof.
  intros. replace m with zero.
    apply add_zero_r.
    apply eq_out. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma sim_add :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> sim (add n1 m1) (add n2 m2).
(* begin hide *)
Proof.
  cofix CH.
  intros n1 n2 m1 m2 [[Hn1 Hn2 | n1' n2' Hn1 Hn2 Hn12]]; intros.
    rewrite !add_zero_l'; assumption.
    constructor. eright; cbn; rewrite ?Hn1, ?Hn2; try reflexivity. apply CH; assumption.
Qed.
(* end hide *)

(** * Lepsze dodawanie *)

CoFixpoint add' (n m : conat) : conat :=
{|
    out :=
      match out n with
          | Z    => out m
          | S n' =>
              match out m with
                  | Z    => S n'
                  | S m' => S {| out := S (add' n' m') |}
              end
      end
|}.

(* To raczej nie przejdzie *)
Lemma sim_add_add' :
  forall n m : conat,
    sim (add n m) (add' n m).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct n as [[| n']]; cbn.
Abort.
(* end hide *)

Lemma add'_zero_l :
  forall n : conat, sim (add' zero n) n.
(* begin hide *)
Proof.
  constructor. destruct n as [[| n']]; cbn.
    left; cbn; reflexivity.
    right with n' n'; cbn; reflexivity.
Qed.
(* end hide *)

Lemma add'_zero_r :
  forall n : conat, sim (add' n zero) n.
(* begin hide *)
Proof.
  constructor. destruct n as [[| n']]; cbn.
    left; cbn; reflexivity.
    eright; cbn; reflexivity.
Qed.
(* end hide *)

Lemma add'_zero_l' :
  forall n m : conat,
    out n = Z -> sim (add' n m) m.
(* begin hide *)
Proof.
  intros. replace n with zero.
    apply add'_zero_l.
    symmetry. apply eq_out. assumption.
Qed.
(* end hide *)

Lemma add'_zero_r' :
  forall n m : conat,
    out m = Z -> sim (add' n m) n.
(* begin hide *)
Proof.
  intros. replace m with zero.
    apply add'_zero_r.
    symmetry. apply eq_out. assumption.
Qed.
(* end hide *)

Lemma sim_add'_zero :
  forall n m : conat,
    sim (add' n m) zero -> sim n zero /\ sim m zero.
(* begin hide *)
Proof.
  intros [[]] [[]]; intros.
    repeat constructor.
    1-3: destruct H as [[]]; cbn in *; try congruence.
Qed.
(* end hide *)

Ltac conat := eright; cbn; try reflexivity.

Lemma add'_omega_l :
  forall n : conat, sim (add' omega n) omega.
(* begin hide *)
Proof.
  cofix CH.
  destruct n as [[]]; cbn.
    apply add'_zero_r.
    do 2 (constructor; eright; cbn; try reflexivity). apply CH.
Qed.
(* end hide *)

Lemma add'_omega_r :
  forall n : conat, sim (add' n omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  destruct n as [[| n']]; cbn.
    apply add'_zero_l.
    do 2 (constructor; eright; cbn; try reflexivity). apply CH.
Qed.
(* end hide *)

Lemma add'_succ_l :
  forall n m : conat, sim (add' (succ n) m) (add' n (succ m)).
(* begin hide *)
Proof.
  cofix CH.
  destruct n as [[| n']], m as [[| m']]; cbn.
    constructor. eright; cbn; reflexivity.
    do 2 (constructor; eright; cbn; try reflexivity). apply add'_zero_l.
    do 2 (constructor; eright; cbn; try reflexivity). rewrite add'_zero_r. apply sim_refl.
    do 2 (constructor; eright; cbn; try reflexivity). apply CH.
Qed.
(* end hide *)

Lemma add'_succ_r :
  forall n m : conat, sim (add' n (succ m)) (add' (succ n) m).
(* begin hide *)
Proof.
  intros. apply sim_sym, add'_succ_l.
Qed.
(* end hide *)

Lemma add'_succ_l' :
  forall n m : conat, sim (add' (succ n) m) (succ (add' n m)).
(* begin hide *)
Proof.
  cofix CH.
  destruct m as [[| m']]; cbn.
  all: constructor; eright; cbn; try reflexivity.
    rewrite add'_zero_r. apply sim_refl.
    destruct n as [[| n']].
    all: constructor; eright; cbn; try reflexivity.
      apply add'_zero_l.
      apply CH.
Qed.
(* end hide *)

Lemma add'_succ_r' :
  forall n m : conat, sim (add' n (succ m)) (succ (add' n m)).
(* begin hide *)
Proof.
  intros. rewrite <- add'_succ_l. apply add'_succ_l'.
Qed.
(* end hide *)

Lemma add'_comm :
  forall n m : conat, sim (add' n m) (add' m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct n as [[| n']], m as [[| m']]; cbn.
    left; cbn; reflexivity.
    eright; try reflexivity.
    eright; try reflexivity.
    eright; cbn. 1-2: try reflexivity. apply sim_succ. apply CH.
Qed.
(* end hide *)

Lemma sim_add'_zero_l :
  forall n m : conat,
    sim (add' n m) zero -> sim n zero.
(* begin hide *)
Proof.
  destruct 1 as [[H1 H2 | n' m' H1 H2 H3]].
    destruct n as [[| n']]; cbn in *.
      constructor; left; cbn; reflexivity.
      destruct m as [[]]; inv H1.
    inv H2.
Qed.
(* end hide *)

Lemma sim_add'_zero_r :
  forall n m : conat,
    sim (add' n m) zero -> sim m zero.
(* begin hide *)
Proof.
  intros.
  rewrite add'_comm in H.
  apply sim_add'_zero_l in H.
  assumption.
Qed.
(* end hide *)

Global Hint Constructors simF sim : core.

Lemma sim_add' :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> sim (add' n1 m1) (add' n2 m2).
(* begin hide *)
Proof.
  cofix CH.
  intros n1 n2 m1 m2 [[Hn1 Hn2 | n1' n2' Hn1 Hn2 Hn12]] Hm12.
    rewrite !add'_zero_l'; assumption.
    destruct Hm12 as [[Hm1 Hm2 | m1' m2' Hm1 Hm2 Hm12]].
      rewrite !add'_zero_r'; try assumption. eauto.
      constructor. eright; cbn; rewrite ?Hn1, ?Hn2, ?Hm1, ?Hm2; try reflexivity.
        apply sim_succ. apply CH; assumption.
Qed.
(* end hide *)

Lemma add'_assoc :
  forall a b c : conat, sim (add' (add' a b) c) (add' a (add' b c)).
(* begin hide *)
Proof.
  cofix CH.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn.
    constructor; left; cbn; try reflexivity.
    constructor; eright; cbn; try reflexivity.
    constructor; eright; cbn; try reflexivity.
    constructor; eright; cbn; try reflexivity.
    constructor; eright; cbn; try reflexivity.
    constructor; eright; cbn; try reflexivity.
    constructor; eright; cbn; try reflexivity.
    {
      do 2 (constructor; eright; cbn; try reflexivity).
      destruct a' as [[| a'']], c' as [[| c'']]; cbn.
        constructor; eright; cbn; try reflexivity.
          rewrite add'_comm. apply sim_refl.
        constructor; eright; cbn; try reflexivity.
          change {| out := S c'' |} with (succ c'').
          rewrite add'_succ_r'. apply sim_succ, sim_add'.
            rewrite add'_zero_l. apply sim_refl.
            apply sim_refl.
        constructor; eright; cbn; try reflexivity.
          change {| out := S a'' |} with (succ a'').
          rewrite add'_succ_l'. apply sim_succ. apply sim_add'.
            apply sim_refl.
            rewrite add'_zero_r. apply sim_refl.
        constructor; eright; cbn; try reflexivity. apply sim_succ.
          destruct a'' as [[| a''']], b' as [[| b'']], c'' as [[| c''']].
            constructor; eright; cbn; try reflexivity.
            do 2 (constructor; eright; cbn; try reflexivity). apply add'_zero_l.
            do 2 (constructor; eright; cbn; try reflexivity). apply add'_comm.
            do 2 (constructor; eright; cbn; try reflexivity). admit.
            do 2 (constructor; eright; cbn; try reflexivity). rewrite add'_zero_r. apply sim_refl.
            do 2 (constructor; eright; cbn; try reflexivity). admit.
            do 2 (constructor; eright; cbn; try reflexivity). admit.
            do 1 (constructor; eright; cbn; try reflexivity). apply sim_succ.
              Print add'_succ_l.
Admitted.
(* end hide *)

(** * Porządek *)

(** Zdefiniuj relację [<=] na liczbach konaturalnych i udowodnij jej
    podstawowe właściwości. *)

(* begin hide *)
Inductive leF (n m : conat) (R : conat -> conat -> Prop) : Prop :=
    | leF_Z :
        out n = Z -> leF n m R
    | leF_S :
        forall n' m' : conat, out n = S n' -> out m = S m' -> R n' m' -> leF n m R.

CoInductive le (n m : conat) : Prop :=
{
    le' : leF n m le
}.
(* end hide *)

Lemma le_0_l :
  forall n : conat, le zero n.
(* begin hide *)
Proof.
  constructor. left. cbn. reflexivity.
Qed.
(* end hide *)

Lemma le_0_r :
  forall n : conat, le n zero -> n = zero.
(* begin hide *)
Proof.
  destruct 1 as [[]].
    apply eq_out. cbn. assumption.
    inv H0.
Qed.
(* end hide *)

Lemma le_succ :
  forall n m : conat, le n m -> le (succ n) (succ m).
(* begin hide *)
Proof.
  constructor. right with n m; cbn; try reflexivity. assumption.
Qed.
(* end hide *)

Lemma le_succ_conv :
  forall n m : conat,
    le (succ n) (succ m) -> le n m.
(* begin hide *)
Proof.
  destruct 1 as [[]]; cbn in *.
    inv H.
    inv H; inv H0.
Qed.
(* end hide *)

Lemma le_refl :
  forall n : conat, le n n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']]; cbn.
    left. cbn. reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma le_trans :
  forall a b c : conat, le a b -> le b c -> le a c.
(* begin hide *)
Proof.
  cofix CH.
  intros a b c [[Ha | a' b' Ha Hb Hab]] Hbc.
    constructor. left. assumption.
    destruct Hbc as [[Hb' | b'' c' Hb' Hc Hbc]].
      congruence.
      constructor. eright; cbn; try eassumption. eapply CH.
        eassumption.
        rewrite Hb in Hb'. inv Hb'.
Qed.
(* end hide *)

Lemma le_univalent :
  forall n m : conat,
    le n m -> le m n -> sim n m.
(* begin hide *)
Proof.
  cofix CH.
  intros n m [[Hn | n1 m1 Hn1 Hm1 Hnm]] [[Hm | m2 n2 Hm2 Hn2 Hmn]].
    constructor. left; assumption.
    congruence.
    congruence.
    constructor. eright; cbn; try eassumption. apply CH.
      rewrite Hn1 in Hn2. inv Hn2. rewrite Hm1 in Hm2. inv Hm2.
      assumption.
Qed.
(* end hide *)

Lemma le_sim :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> le n1 m1 -> le n2 m2.
(* begin hide *)
Proof.
  intros.
  rewrite <- (sim_eq H), <- (sim_eq H0). assumption.
Restart.
  cofix CH.
  intros n1 n2 m1 m2 Hn12 Hm12 [[Hn1 | n1' m1' Hn1' Hm1' Hnm1']].
    destruct Hn12 as [[]].
      constructor. left. assumption.
      congruence.
    destruct Hn12 as [[]], Hm12 as [[]]; try congruence.
      constructor. eright; try eassumption. eapply CH; try eassumption.
        rewrite Hn in Hn1'. inv Hn1'. rewrite Hn0 in Hm1'. inv Hm1'.
Qed.
(* end hide *)

Lemma le_omega_r :
  forall n : conat, le n omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']].
    left; cbn. reflexivity.
    right with n' omega; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma le_omega_l :
  forall n : conat, le omega n -> sim n omega.
(* begin hide *)
Proof.
  cofix CH.
  intros n [[]].
    inv H.
    constructor. eright; cbn.
      eassumption.
      reflexivity.
      apply CH. cbn in H. inv H.
Qed.
(* end hide *)

Lemma le_succ_r :
  forall n m : conat, le n m -> le n (succ m).
(* begin hide *)
Proof.
  cofix CH.
  intros n m [[]]; constructor.
    left. assumption.
    eright with n' (succ m'); eauto.
      cbn. f_equal. apply eq_out. cbn. assumption.
Qed.
(* end hide *)

Lemma le_add_l :
  forall a b c : conat,
    le a b -> le a (add b c).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[Ha | a' b' Ha Hb Hab]].
    left. assumption.
    eright; cbn.
      eassumption.
      rewrite Hb. reflexivity.
      apply CH. assumption.
Qed.
(* end hide *)

Lemma le_add_r :
  forall a b c : conat,
    le a c -> le a (add b c).
(* begin hide *)
Proof.
  intros. eapply le_sim.
    reflexivity.
    apply add_comm.
    apply le_add_l. assumption.
Qed.
(* end hide *)

Lemma le_add :
  forall n1 n2 m1 m2 : conat,
    le n1 n2 -> le m1 m2 -> le (add n1 m1) (add n2 m2).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct H as [[Hn1 | n1' n2' Hn1 Hn2 Hn12]].
    destruct H0 as [[Hm1 | m1' m2' Hm1 Hm2 Hm12]].
      left. cbn. rewrite Hn1. assumption.
      destruct n2 as [[| n2']].
        eright; cbn; rewrite ?Hn1; eassumption.
        eright; cbn; rewrite ?Hn1; eauto. apply le_add_r. replace m2 with (succ m2').
          apply le_succ_r. assumption.
          apply eq_out. cbn. symmetry. assumption.
    eright; cbn; rewrite ?Hn1, ?Hn2; try reflexivity.
      apply CH; assumption.
Qed.
(* end hide *)

Lemma le_add_l' :
  forall n m : conat, le n (add n m).
(* begin hide *)
Proof.
  intros. apply le_add_l. apply le_refl.
Qed.
(* end hide *)

Lemma le_add_r' :
  forall n m : conat, le m (add n m).
(* begin hide *)
Proof.
  intros. apply le_add_r. apply le_refl.
Qed.
(* end hide *)

Lemma le_add_l'' :
  forall n n' m : conat,
    le n n' -> le (add n m) (add n' m).
(* begin hide *)
Proof.
  intros. apply le_add.
    assumption.
    apply le_refl.
Qed.
(* end hide *)

Lemma le_add_r'' :
  forall n m m' : conat,
    le m m' -> le (add n m) (add n m').
(* begin hide *)
Proof.
  intros. apply le_add.
    apply le_refl.
    assumption.
Qed.
(* end hide *)

(** * Minimum i maksimum *)

(** Zdefiniuj funkcje [min] i [max] i udowodnij ich właściwości. *)

(* begin hide *)
CoFixpoint min (n m : conat) : conat :=
{|
    out :=
      match out n, out m with
          | Z, _ => Z
          | _, Z => Z
          | S n', S m' => S (min n' m')
      end;
|}.

CoFixpoint max (n m : conat) : conat :=
{|
    out :=
      match out n, out m with
          | Z, _ => out m
          | _, Z => out n
          | S n', S m' => S (max n' m')
      end;
|}.
(* end hide *)

Lemma min_zero_l :
  forall n : conat, min zero n = zero.
(* begin hide *)
Proof.
  intros. apply eq_out. cbn. reflexivity.
Qed.
(* end hide *)

Lemma min_zero_r :
  forall n : conat, min n zero = zero.
(* begin hide *)
Proof.
  intros. apply eq_out. cbn. destruct (out n); reflexivity.
Qed.
(* end hide *)

Lemma min_omega_l :
  forall n : conat, sim (min omega n) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']]; cbn.
    left; cbn; reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma min_omega_r :
  forall n : conat, sim (min n omega) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']]; cbn.
    left; cbn; reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma min_succ :
  forall n m : conat,
    sim (min (succ n) (succ m)) (succ (min n m)).
(* begin hide *)
Proof.
  constructor. eright; reflexivity.
Qed.
(* end hide *)

Lemma max_zero_l :
  forall n : conat, sim (max zero n) n.
(* begin hide *)
Proof.
  constructor. destruct n as [[| n']]; cbn.
    left; cbn; reflexivity.
    eright; cbn; reflexivity.
Qed.
(* end hide *)

Lemma max_zero_r :
  forall n : conat, sim (max n zero) n.
(* begin hide *)
Proof.
  constructor. destruct n as [[| n']]; cbn.
    left; cbn; reflexivity.
    eright; cbn; reflexivity.
Qed.
(* end hide *)

Lemma max_omega_l :
  forall n : conat, sim (max omega n) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']]; cbn.
    eright; cbn; try reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma max_omega_r :
  forall n : conat, sim (max n omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']]; cbn.
    eright; cbn; try reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma max_succ :
  forall n m : conat,
    sim (max (succ n) (succ m)) (succ (max n m)).
(* begin hide *)
Proof.
  constructor. eright; reflexivity.
Qed.
(* end hide *)

Lemma min_assoc :
  forall a b c : conat, sim (min (min a b) c) (min a (min b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn; auto.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma max_assoc :
  forall a b c : conat, sim (max (max a b) c) (max a (max b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn.
    auto.
    1-6: eright; cbn; try reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma min_comm :
  forall n m : conat, sim (min n m) (min m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']], m as [[| m']]; cbn; auto.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma max_comm :
  forall n m : conat, sim (max n m) (max m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[| n']], m as [[| m']]; cbn.
    left; cbn; reflexivity.
    1-2: eright; cbn; try reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.
(* end hide *)

Lemma min_add_l :
  forall a b c : conat,
    sim (min (add a b) (add a c)) (add a (min b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn; auto.
    all: eright; intuition.
Qed.
(* end hide *)

Lemma min_add_r :
  forall a b c : conat,
    sim (min (add a c) (add b c)) (add (min a b) c).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn; auto.
    all: eright; cbn; intuition.
  cofix CH.
  destruct a as [[| a']], b as [[| b']]; intros.
    rewrite min_zero_l. rewrite !add_zero_l.
    left; cbn. reflexivity.
    all: eright; cbn; intuition.
      rewrite min_diag.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn.
    1, 3, 5: left; cbn; reflexivity.
    all: eright; cbn; intuition.
      rewrite min_diag.
Qed.
(* end hide *)

Lemma max_add_l :
  forall a b c : conat,
    sim (max (add a b) (add a c)) (add a (max b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn; auto.
    all: eright; try intuition. do 2 eexists; intuition.
Qed.
(* end hide *)

Lemma max_add_r :
  forall a b c : conat,
    sim (max (add a c) (add b c)) (add (max a b) c).
(* begin hide *)
Proof.
  intros.
  rewrite (sim_eq (add_comm a c)), (sim_eq (add_comm b c)).
  rewrite max_add_l, add_comm. reflexivity.
Qed.
(* end hide *)

Lemma min_le :
  forall n m : conat, le n m -> sim (min n m) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | (n' & m' & H1 & H2 & H3)]]; cbn.
    rewrite H. left. auto.
    rewrite H1, H2. right. do 2 eexists. intuition.
Qed.
(* end hide *)

Lemma max_le :
  forall n m : conat, le n m -> sim (max n m) m.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | (n' & m' & H1 & H2 & H3)]]; cbn.
    rewrite H. destruct m as [[| m']]; cbn.
      right. do 2 eexists. intuition.
      left. auto.
    rewrite H1, H2. right. do 2 eexists. intuition.
Qed.
(* end hide *)

Lemma min_diag :
  forall n : conat, sim (min n n) n.
(* begin hide *)
Proof.
  intros. apply min_le. apply le_refl.
Qed.
(* end hide *)

Lemma max_diag :
  forall n : conat, sim (max n n) n.
(* begin hide *)
Proof.
  intros. apply max_le. apply le_refl.
Qed.
(* end hide *)

Lemma sim_min_max :
  forall n m : conat,
    sim (min n m) (max n m) -> sim n m.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[[H1 H2] | (n' & m' & H1 & H2 & H3)]].
    left. cbn in *. destruct (out n), (out m); try congruence. auto.
    right. cbn in *. destruct (out n), (out m); try congruence.
      do 2 eexists. intuition. apply CH. inv H1. inv H2.
Qed.
(* end hide *)

Lemma min_max :
  forall a b : conat, sim (min a (max a b)) a.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']]; cbn; auto.
    right. do 2 eexists. intuition.
    right. do 2 eexists. intuition. rewrite min_diag. apply sim_refl.
Qed.
(* end hide *)

Lemma max_min :
  forall a b : conat, sim (max a (min a b)) a.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']]; cbn; auto.
    right. do 2 eexists. intuition.
    right. do 2 eexists. intuition.
Qed.
(* end hide *)

Lemma min_max_distr :
  forall a b c : conat,
    sim (min a (max b c)) (max (min a b) (min a c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn; auto.
    right. do 2 eexists. intuition.
    right. do 2 eexists. intuition.
    right. do 2 eexists. intuition.
Qed.
(* end hide *)

Lemma max_min_distr :
  forall a b c : conat,
    sim (max a (min b c)) (min (max a b) (max a c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn; auto.
    right. do 2 eexists. intuition.
    right. do 2 eexists. intuition.
      rewrite min_comm, min_max. apply sim_refl.
    right. do 2 eexists. intuition.
      rewrite min_max. reflexivity.
    right. do 2 eexists. intuition. rewrite min_diag. reflexivity.
    right. do 2 eexists. intuition.
Qed.
(* end hide *)

(** * Dzielenie przez 2 *)

(** Zdefiniuj funkcję [div2], która dzieli liczbę konaturalną przez 2
    (cokolwiek to znaczy). Udowodnij jej właściwości. *)

(* begin hide *)
CoFixpoint div2 (n : conat) : conat :=
{|
    out :=
      match out n with
          | Z => Z
          | S n' =>
              match out n' with
                  | Z => Z
                  | S n'' => S (div2 n'')
              end
      end;
|}.
(* end hide *)

Lemma div2_zero :
  sim (div2 zero) zero.
(* begin hide *)
Proof.
  constructor. cbn. left. auto.
Qed.
(* end hide *)

Lemma div2_omega :
  sim (div2 omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. right. do 2 eexists. intuition.
Qed.
(* end hide *)

Lemma div2_succ :
  forall n : conat, sim (div2 (succ (succ n))) (succ (div2 n)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. right. do 2 eexists. intuition.
Qed.
(* end hide *)

Lemma div2_add :
  forall n : conat, sim (div2 (add n n)) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct n as [[| n']].
    right. exists (div2 (add n' n')).
      replace {| out := S n' |} with (succ n').
        exists n'. intuition. rewrite (sim_eq (add_succ_l' _ _)).
          rewrite (sim_eq (add_succ_r' _ _)).
          rewrite (sim_eq (div2_succ _)). cbn. reflexivity.
      apply eq_out. cbn. reflexivity.
    left. cbn. auto.
Qed.
(* end hide *)

Lemma le_div2_l_aux :
  forall n m : conat, le n m -> le (div2 n) m.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | (n' & m' & H1 & H2 & H3)]]; cbn.
    rewrite H. left. reflexivity.
    rewrite H1. destruct H3 as [[H3 | (n'' & m'' & H31 & H32 & H33)]]; cbn.
      rewrite H3. left. reflexivity.
      rewrite H31. right. do 2 eexists. intuition.
        eassumption.
        apply CH. apply le_trans with m''.
          assumption.
          replace m' with (succ m'').
            apply le_succ_r. apply le_refl.
            apply eq_out. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma le_div2_l :
  forall n : conat, le (div2 n) n.
(* begin hide *)
Proof.
  intros. apply le_div2_l_aux, le_refl.
Qed.
(* end hide *)

Lemma le_div2 :
  forall n m : conat, le n m -> le (div2 n) (div2 m).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct H as [[H | (n' & m' & H1 & H2 &
                [[H3 | (n'' & m'' & H31 & H32 & H33)]])]]; cbn.
    rewrite H. left. reflexivity.
    rewrite H1, H2, H3. left. reflexivity.
    rewrite H1, H2, H31, H32. right. do 2 eexists. intuition.
Qed.
(* end hide *)

(** * Skończoność i nieskończoność *)

(** Zdefiniuj outykaty [Finite] i [Infinite], które wiadomo co znaczą.
    Pokaż, że omega jest liczbą nieskończoną i że nie jest skończona,
    oraz że każda liczba nieskończona jest bipodobna do omegi. Pokaż
    też, że żadna liczba nie może być jednocześnie skończona i
    nieskończona. *)

(* begin hide *)
Inductive Finite : conat -> Prop :=
    | Finite_zero : Finite zero
    | Finite_succ : forall n : conat, Finite n -> Finite (succ n).

Inductive InfiniteF (n : conat) (P : conat -> Prop) : Prop :=
    | InfiniteF' :
        forall (n' : conat) (H : out n = S n'),
          P n' -> InfiniteF n P.

CoInductive Infinite (n : conat) : Prop :=
{
    Infinite' : InfiniteF n Infinite;
}.
(* end hide *)

Lemma omega_not_Finite :
  ~ Finite omega.
(* begin hide *)
Proof.
  intro. remember omega as n. revert Heqn.
  induction H; intro.
    apply (f_equal out) in Heqn. cbn in Heqn. inv Heqn.
    apply (f_equal out) in Heqn. cbn in Heqn. inv Heqn.
Qed.
(* end hide *)

Lemma Infinite_omega :
  Infinite omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. exists omega. split.
    cbn. reflexivity.
    apply CH.
Qed.
(* end hide *)

Lemma Infinite_omega' :
  forall n : conat, Infinite n -> sim n omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[n' [H1 H2]]].
  right. exists n', omega. intuition.
Qed.
(* end hide *)

Lemma Finite_Infinite :
  forall n : conat, Finite n -> Infinite n -> False.
(* begin hide *)
Proof.
  induction 1; destruct 1 as [(n' & H1 & H2)]; inv H1.
Qed.
(* end hide *)

(** * Parzystość i nieparzystość *)

(** Zdefiniuj outykaty [Even] i [Odd]. Pokaż, że omega jest jednocześnie
    parzysta i nieparzysta. Pokaż, że jeżeli liczba jest jednocześnie
    parzysta i nieparzysta, to jest nieskończona. Wyciągnij z tego oczywisty
    wniosek. Pokaż, że każda liczba skończona jest parzysta albo
    nieparzysta. *)

(* begin hide *)
Inductive EvenF (n : conat) (P : conat -> Prop) : Prop :=
    | EvenF_Z  :
        forall Hn : out n = Z, EvenF n P
    | EvenF_SS :
        forall (n1 n2 : conat) (Hn1 : out n = S n1) (Hn2 : out n1 = S n2),
          P n2 -> EvenF n P.

CoInductive Even (n : conat) : Prop :=
{
    Even' : EvenF n Even
}.

Inductive OddF (n : conat) (P : conat -> Prop) : Prop :=
    | OddF_SZ :
        forall (n' : conat) (Hn : out n = S n') (Hn' : out n' = Z),
          OddF n P
    | OddF_SS :
        forall (n1 n2 : conat) (Hn1 : out n = S n1) (Hn2 : out n1 = S n2),
          P n2 -> OddF n P.

CoInductive Odd (n : conat) : Prop :=
{
    Odd' : OddF n Odd;
}.
(* end hide *)

Lemma Even_zero :
  Even zero.
(* begin hide *)
Proof.
  constructor. left. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Odd_zero :
  ~ Odd zero.
(* begin hide *)
Proof.
  destruct 1 as [[H | (n & m & H1 & H2 & H3)]].
    inv H.
    inv H1.
Qed.
(* end hide *)

Lemma Even_Omega :
  Even omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. right.
  exists omega, omega. cbn. intuition.
Qed.
(* end hide *)

Lemma Odd_Omega :
  Odd omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. right.
  exists omega, omega. cbn. intuition.
Qed.
(* end hide *)

Lemma Even_Odd_Infinite :
  forall n : conat, Even n -> Odd n -> Infinite n.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct H as [[HE | (n1 & n2 & HE1 & HE2 & HE3)]],
          H0 as [[HO | (m1 & m2 & HO1 & HO2 & HO3)]];
  subst; cbn in *.
    inv HE.
    congruence.
    inv HE1. inv HE2.
    rewrite HO1 in HE1. inv HE1. rewrite HO2 in HE2. inv HE2.
      exists n1. intuition. constructor. exists n2. intuition.
Qed.
(* end hide *)

Lemma Even_succ :
  forall n : conat, Odd n -> Even (succ n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | (n1 & n2 & H1 & H2 & H3)]]; cbn.
    right. exists n, zero. intuition.
      rewrite H. cbn. reflexivity.
      constructor. left. cbn. reflexivity.
    right. exists n, n1. intuition. replace n1 with (succ n2).
      apply CH. assumption.
      apply eq_out. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Odd_succ :
  forall n : conat, Even n -> Odd (succ n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | (n1 & n2 & H1 & H2 & H3)]].
    left. apply sim_eq. apply sim_succ. constructor.
      left. cbn. auto.
    right. cbn. exists n, n1. intuition. replace n1 with (succ n2).
      apply CH. assumption.
      apply eq_out. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Even_succ_inv :
  forall n : conat, Odd (succ n) -> Even n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | (n1 & n2 & H1 & H2 & H3)]]; cbn.
    inv H.
    cbn in H1. inv H1. right.
      destruct H3 as [[H3 | (m1 & m2 & H1' & H2' & H3')]]; subst.
        exists (succ zero), zero. intuition. apply Even_zero.
        exists n2, m1. intuition. replace m1 with (succ m2).
          apply Even_succ. assumption.
          apply eq_out. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Odd_succ_inv :
  forall n : conat, Even (succ n) -> Odd n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | (n1 & n2 & H1 & H2 & H3)]]; cbn.
    inv H.
    cbn in H1. inv H1.
      destruct H3 as [[H | (n1' & n2' & H1' & H2' & H3')]]; cbn.
        left. apply eq_out. cbn. rewrite H2. f_equal.
          apply eq_out. cbn. assumption.
        right. exists n2, n1'. intuition. apply CH.
          replace (succ n1') with n2.
            constructor. right. do 2 eexists. eauto.
            apply eq_out. cbn. assumption.
Qed.
(* end hide *)

Lemma Finite_Even_Odd :
  forall n : conat, Finite n -> Even n \/ Odd n.
(* begin hide *)
Proof.
  induction 1.
    left. constructor. left. cbn. reflexivity.
    destruct IHFinite.
      right. apply Odd_succ. assumption.
      left. apply Even_succ. assumption.
Qed.
(* end hide *)

Lemma Finite_not_both_Even_Odd :
  forall n : conat, Finite n -> ~ (Even n /\ Odd n).
(* begin hide *)
Proof.
  induction 1; destruct 1.
    apply Odd_zero. assumption.
    apply IHFinite. split.
      apply Even_succ_inv. assumption.
      apply Odd_succ_inv. assumption.
Qed.
(* end hide *)

Lemma Even_add_Odd :
  forall n m : conat, Odd n -> Odd m -> Even (add n m).
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [[H | (n1 & n2 & H1 & H2 & H3)]]; intro.
    rewrite H, (sim_eq (add_succ_l' _ _)), (sim_eq (add_zero_l _)).
      apply Even_succ. assumption.
    constructor. right. exists (add n1 m), (add n2 m).
      cbn. rewrite H1, H2. intuition.
Qed.
(* end hide *)

Lemma Even_add_Even :
  forall n m : conat, Even n -> Even m -> Even (add n m).
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [[H | (n1 & n2 & H1 & H2 & H3)]]; intro.
    replace n with zero.
      rewrite (sim_eq (add_zero_l _)). assumption.
      apply eq_out. cbn. auto.
    constructor. right. exists (add n1 m), (add n2 m).
      cbn. rewrite H1, H2. auto.
Qed.
(* end hide *)

Lemma Odd_add_Even_Odd :
  forall n m : conat, Even n -> Odd m -> Odd (add n m).
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [[H | (n1 & n2 & H1 & H2 & H3)]]; intro.
    replace n with zero.
      rewrite (sim_eq (add_zero_l _)). assumption.
      apply eq_out. cbn. auto.
    constructor. right. exists (add n1 m), (add n2 m).
      cbn. rewrite H1, H2. auto.
Qed.
(* end hide *)

(** * Odejmowanie (TODO) *)

(** Było już o dodawaniu, przydałoby się powiedzieć też coś o odejmowaniu.
    Niestety, ale odejmowania liczb konaturalnych nie da się zdefiniować
    (a przynajmniej tak mi się wydaje). Nie jest to również coś, co można
    bezpośrednio udowodnić. Jest to fakt żyjący na metapoziomie, czyli
    mówiący coś o Coqu, a nie mówiący coś w Coqu. Jest jednak pewien
    wewnętrzny sposób by upewnić się, że odejmowanie faktycznie nie jest
    koszerne. *)

Definition Sub (n m r : conat) : Prop :=
  sim (add r m) n.

(** W tym celu definiujemy relację [Sub], która ma reprezentować wykres
    funkcji odejmującej, tzn. specyfikować, jaki jest związek argumentów
    funkcji z jej wynikiem. *)

Definition sub : Type :=
  {f : conat -> conat -> conat |
    forall n m r : conat, f n m = r <-> Sub n m r}.

(** Dzięki temu możemy napisać precyzyjny typ, który powinna mieć nasza
    funkcja - jest to funkcja biorąca dwie liczby konaturalne i zwracająca
    liczbę konaturalną, która jest poprawna i pełna względem wykresu. *)

Lemma Sub_nondet :
  forall r : conat, Sub omega omega r.
(* begin hide *)
Proof.
  unfold Sub.
  cofix CH.
  constructor. destruct r as [[r' |]]; cbn.
    right. do 2 eexists. intuition.
    right. do 2 eexists. intuition.
Qed.
(* end hide *)

(** Niestety mimo, że definicja relacji [Sub] jest tak oczywista, jak to
    tylko możliwe, relacja ta nie jest wykresem żadnej funkcji, gdyż jest
    niedeterministyczna. *)

Lemma sub_cant_exist :
  sub -> False.
(* begin hide *)
Proof.
  destruct 1 as [f H].
  assert (f omega omega = zero).
    apply H. apply Sub_nondet.
  assert (f omega omega = succ zero).
    apply H. apply Sub_nondet.
  rewrite H0 in H1. inv H1.
Qed.
(* end hide *)

(** Problem polega na tym, że [omega - omega] może być dowolną liczbą
    konaturalną. Bardziej obrazowo:
    - Chcielibyśmy, żeby [n - n = 0]
    - Chcielibyśmy, żeby [(n + 1) - n = 1]
    - Jednak dla [n = omega] daje to [omega - omega = 0] oraz
      [omega - omega = 1], co prowadzi do sprzeczności

    Dzięki temu możemy skonkludować, że typ [sub] jest pusty, a zatem
    pożądana przez nas funkcją odejmująca nie może istnieć.

    Najbliższą odejmowaniu operacją, jaką możemy wykonać na liczbach
    konaturalnych, jest odejmowanie liczby naturalnej od liczby
    konaturalnej. *)

(* begin hide *)
Fixpoint subn (n : conat) (m : nat) : conat :=
match out n, m with
    | Z, _ => n
    | _, 0 => n
    | S n', S m' => subn n' m'
end.
(* end hide *)

(* begin hide *)
Lemma sim_add_Finite :
  forall a b c : conat,
    Finite c -> sim (add a c) (add b c) -> sim a b.
Proof.
  intros until 1. revert a b.
  induction H; cbn; intros.
    rewrite !add_zero_r in H. assumption.
    rewrite !add_succ_r, !add_succ_l' in H0.
      apply sim_succ_inv in H0. apply IHFinite. assumption.
Qed.

Lemma Finite_sim :
  forall n m : conat,
    sim n m -> Finite n -> Finite m.
Proof.
  intros until 2. revert m H.
  induction H0; intros.
    inv H; decompose [ex or and] sim'0; clear sim'0.
      replace m with zero.
        apply Finite_zero.
        apply eq_out. cbn. congruence.
      inv H0.
    destruct m as [[| m']].
      constructor. apply IHFinite. apply sim_succ_inv. exact H.
      constructor.
Qed.

Lemma Finite_add :
  forall n m : conat,
    Finite n -> Finite m -> Finite (add n m).
Proof.
  intros until 1. revert m.
  induction H; intros.
    apply Finite_sim with m.
      rewrite add_zero_l. reflexivity.
      assumption.
    apply Finite_sim with (succ (add n m)).
      rewrite add_succ_l'. reflexivity.
      constructor. apply IHFinite. assumption.
Qed.

Lemma Finite_add_inv_l :
  forall n m : conat,
    Finite (add n m) -> Finite n.
Proof.
  intros. remember (add n m) as c.
  revert n m Heqc.
  induction H; intros.
    destruct n as [[| n']].
      apply (f_equal out) in Heqc. inv Heqc.
      constructor.
    destruct n0 as [[| n']].
      apply (f_equal out) in Heqc. inv Heqc.
        constructor. eapply IHFinite. reflexivity.
      constructor.
Qed.

Lemma Sub_Finite_sim :
  forall n m r1 r2 : conat,
    Finite n -> Sub n m r1 -> Sub n m r2 -> sim r1 r2.
Proof.
  unfold Sub; intros.
  eapply sim_add_Finite.
    2: { rewrite H0, H1. reflexivity. }
    eapply Finite_add_inv_l. eapply Finite_sim.
      apply add_comm.
      eapply Finite_sim.
        symmetry. exact H0.
        assumption.
Qed.

Definition sub' : Type :=
  {f : conat -> conat -> conat |
    forall n m r : conat, f n m = r -> Sub n m r}.
(* end hide *)

(** * Mnożenie (TODO) *)

CoFixpoint mul' (n m acc : conat) : conat :=
{|
    out :=
      match out n, out m with
          | Z   , _       => out acc
          | _      , Z    => out acc
          | S n', S m' => S (mul' n' m' (add n' (add m' acc)))
      end
|}.

Definition mul (n m : conat) : conat :=
  mul' n m zero.

Lemma mul'_zero_l :
  forall c acc : conat,
    mul' zero c acc = acc.
(* begin hide *)
Proof.
  intros. apply eq_out. cbn. reflexivity.
Qed.
(* end hide *)

Lemma mul'_zero_r :
  forall n m acc : conat,
    out m = Z -> mul' n m acc = acc.
(* begin hide *)
Proof.
  intros. apply eq_out. cbn. rewrite H. destruct (out n); reflexivity.
Qed.
(* end hide *)

Lemma mul'_comm :
  forall n m acc1 acc2 : conat,
    sim acc1 acc2 ->
      sim (mul' n m acc1) (mul' m n acc2).
(* begin hide *)
Proof.
  cofix CH.
  destruct n as [[| n']],
           m as [[| m']];
  constructor; cbn.
    right. do 2 eexists. do 2 (split; try reflexivity).
      apply CH. rewrite <- !add_assoc. apply sim_add.
        apply add_comm.
        assumption.
    1-3: inv H.
Qed.
(* end hide *)

Lemma mul'_one_l :
  forall c acc : conat,
    sim (mul' (succ zero) c acc) (add c acc).
(* begin hide *)
Proof.
  destruct c as [[| c']]; constructor; cbn.
    right. do 2 eexists. do 2 (split; try reflexivity).
      rewrite mul'_zero_l, add_zero_l. reflexivity.
    destruct acc as [[acc' |]]; cbn; eauto.
      right. do 2 eexists. do 2 (split; try reflexivity).
Qed.
(* end hide *)

Lemma mul'_one_r :
  forall c acc : conat,
    sim (mul' c (succ zero) acc) (add c acc).
(* begin hide *)
Proof.
  intros. rewrite mul'_comm.
    apply mul'_one_l.
    reflexivity.
Qed.
(* end hide *)

Lemma mul'_omega_l :
  forall c acc : conat,
    out c <> Z ->
      sim (mul' omega c acc) omega.
(* begin hide *)
Proof.
  cofix CH.
  destruct c as [[| c']];
  constructor; cbn.
    right. do 2 eexists. do 2 (split; try reflexivity). destruct c' as [[c'' |]].
      apply CH. cbn. inversion 1.
      change {| out := Z |} with zero. rewrite mul'_zero_r.
        apply add_omega_l.
        cbn. reflexivity.
    cbn in H. congruence.
Qed.
(* end hide *)

Lemma mul'_omega_r :
  forall c acc : conat,
    out c <> Z ->
      sim (mul' c omega acc) omega.
(* begin hide *)
Proof.
  intros. rewrite mul'_comm.
    apply mul'_omega_l. assumption.
    reflexivity.
Qed.
(* end hide *)

Definition out' (n : conat) : conat :=
match out n with
    | Z    => zero
    | S n' => n'
end.

(* Inductive Finite' : conat -> Prop :=
    | Finite'_zero :
        forall n : conat, out n = Z -> Finite' n
    | Finite'_succ :
        forall n n' : conat, out n = S n' -> Finite' n' -> Finite' n.
 *)

(* Inductive Finite' : conat -> Prop :=
    | Finite'_zero :
        forall n : conat, out n = Z -> Finite' n
    | Finite'_succ :
        forall n : conat, Finite' (out' n) -> Finite' n.

Hint Constructors Finite' : core.
 *)

Lemma mul'_acc :
  forall n m acc1 acc2 : conat,
    sim (mul' n m (add acc1 acc2)) (add acc1 (mul' n m acc2)).
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma mul'_succ_l :
  forall n m acc : conat,
    sim (mul' (succ n) m acc) (add m (mul' n m acc)).
(* begin hide *)
Proof.
  destruct m as [[| m']];
  constructor; cbn.
    right. do 2 eexists. do 2 (split; try reflexivity).
Admitted.
(* end hide *)

Lemma Finite_mul' :
  forall n m acc : conat,
    Finite n -> Finite m -> Finite acc ->
      Finite (mul' n m acc).
(* begin hide *)
Proof.
  intros until 1. revert m acc.
  induction H; intros m acc Hm Hacc.
    eapply Finite_sim.
      rewrite mul'_zero_l. reflexivity.
      assumption.
    eapply Finite_sim.
      symmetry. apply mul'_succ_l.
      apply Finite_add.
        assumption.
        apply IHFinite; assumption.
Qed.
(* end hide *)

Lemma mul'_assoc :
  forall a b c acc1 acc1' acc2 acc2' : conat,
    sim acc1 acc1' -> sim acc2 acc2' ->
      sim (mul' a (mul' b c acc1) acc2) (mul' (mul' a b acc1') c acc2').
(* begin hide *)
Proof.
  cofix CH.
  destruct a as [[| a']],
           b as [[| b']],
           c as [[| c']];
  constructor; cbn.
    right. do 2 eexists. do 2 (split; try reflexivity).
Admitted.
(* end hide *)

(** * Koindukcja wzajemna (TODO) *)

(* begin hide *)
CoInductive Even2 (n : conat) : Prop :=
{
    Even2' :
      out n = Z \/
      exists n' : conat,
        out n = S n' /\ Odd2 n';
}

with Odd2 (n : conat) : Prop :=
{
    Odd2' :
      n = succ zero \/
      exists n' : conat,
        out n = S n' /\ Even2 n';
}.

Module Even2_v2.

Inductive Even2F (n : conat) (P : conat -> Prop) : Prop :=
    | Even2_Z  :
        forall Hn : out n = Z, Even2F n P
    | Even2_SS :
        forall (n' : conat) (Hn : out n = S n'),
          P n' -> Even2F n P.

Inductive Odd2F (n : conat) (P : conat -> Prop) : Prop :=
    | Odd2_S :
        forall (n' : conat) (Hn : out n = S n'),
          P n' -> Odd2F n P.

CoInductive Even2 (n : conat) : Prop :=
{
    Even2' : Even2F n Odd2
}

with Odd2 (n : conat) : Prop :=
{
    Odd2' : Odd2F n Even2
}.

End Even2_v2.

Lemma Even2_add_Odd2 :
  forall n m : conat, Odd2 n -> Odd2 m -> Even2 (add n m)

with Even2_add_Odd2_Even2 :
  forall n m : conat, Even2 n -> Odd2 m -> Odd2 (add n m).
Proof.
  constructor. destruct H as [[H | (n' & H1 & H2)]].
    rewrite H. cbn. right. exists m. split.
      f_equal. apply eq_out. cbn. reflexivity.
      assumption.
    cbn. rewrite H1. right. eexists. intuition.
  constructor.
  destruct H as [[H | (n' & H1 & H2)]],
          H0 as [[H' | (m' & H1' & H2')]]; subst; cbn.
    rewrite H. left. apply sim_eq. rewrite add_comm. constructor.
      cbn. right. do 2 eexists. intuition. rewrite add_zero_l. constructor; eauto.
    rewrite H. right. exists m'. intuition.
    rewrite H1. right. exists (succ n'). split.
      f_equal. apply sim_eq. rewrite add_comm. constructor. cbn.
        right. do 2 eexists. intuition. rewrite add_zero_l. apply sim_refl.
      constructor. cbn. right. exists n'. auto.
    rewrite H1. right. exists (add n' m). intuition. apply Even2_add_Odd2.
      assumption.
      constructor. right. exists m'. auto.
Qed.
(* end hide *)

(** * Liczby naturalne i konaturalne *)

(** Zdefiniuj funkcję [from_nat], która przekształca liczbę naturalną
    w odpowiadającą jej skończoną liczbę konaturalną. *)

(* begin hide *)
Fixpoint from_nat (n : nat) : conat :=
match n with
    | 0 => zero
    | S n' => succ (from_nat n')
end.
(* end hide *)

Lemma Finite_from_nat :
  forall n : nat, Finite (from_nat n).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; constructor; assumption.
Qed.
(* end hide *)

(** Pokaż, że [from_nat] nie ma żadnej preodwrotności. *)

(* begin hide *)
(* TODO: wyjaśnić wcześniej pojęcie preodwrotności. *)
(* end hide *)

(* begin hide *)
Lemma no_preinverse_aux :
  forall f : conat -> nat,
    from_nat (f omega) <> omega.
Proof.
  intros f H.
  apply omega_not_Finite.
  rewrite <- H.
  apply Finite_from_nat.
Qed.
(* end hide *)

Lemma no_preinverse :
  forall f : conat -> nat,
    (forall c : conat, from_nat (f c) = c) -> False.
(* begin hide *)
Proof.
  intros f H.
  eapply no_preinverse_aux.
  apply H.
Qed.
(* end hide *)

(** Pokaż, że jeżeli [from_nat] ma postodwrotność, to można rozstrzygać,
    czy liczba konaturalna jest skończona czy nie.

    UWAGA: diabelsko trudne. Wymaga ruszenia wyobraźnią i wymyślenia
    kilku induktywnych definicji relacji oraz udowodnienia paru lematów
    na ich temat. *)

(* begin hide *)
Inductive lec : conat -> nat -> Prop :=
    | lec_0 : forall n : nat, lec zero n
    | lec_S : forall (c : conat) (n : nat), lec c n -> lec (succ c) (S n).

Inductive gtc : conat -> nat -> Prop :=
    | gtc_zero : forall c : conat, gtc (succ c) 0
    | gtc_S : forall (c : conat) (n : nat), gtc c n -> gtc (succ c) (S n).

Lemma lec_spec :
  forall (n : nat) (c : conat),
    lec c n -> Finite c.
Proof.
  induction 1; constructor; assumption.
Qed.

Lemma gtc_omega :
  forall n : nat, gtc omega n.
Proof.
  induction n as [| n'].
    rewrite succ_omega. constructor.
    rewrite succ_omega. constructor. assumption.
Qed.

Lemma gtc_from_nat :
  forall n : nat, ~ gtc (from_nat n) n.
Proof.
  induction n as [| n']; cbn.
    inversion 1.
    intro. apply IHn'. inversion H. assumption.
Qed.

Lemma conat_nat_order :
  forall (n : nat) (c : conat),
    lec c n \/ gtc c n.
Proof.
  induction n as [| n']; cbn; intro.
    destruct c as [[| c']].
      right. constructor.
      left. constructor.
    destruct c as [[| c']].
      destruct (IHn' c') as [IH | IH].
        left. constructor. assumption.
        right. constructor. assumption.
      left. constructor.
Qed.

Lemma Infinite_not_from_nat :
  forall c : conat,
    (forall n : nat, c <> from_nat n) -> Infinite c.
Proof.
  cofix CH.
  intros c H.
  destruct c as [[| c']].
    constructor. exists c'. split.
      cbn. reflexivity.
      apply CH. intros n H'. apply (H (S n)). cbn. subst. reflexivity.
    specialize (H 0). cbn in H. contradiction H. reflexivity.
Qed.
(* end hide *)

Lemma inverse_taboo :
  forall f : conat -> nat,
    (forall n : nat, f (from_nat n) = n) ->
      forall c : conat, Infinite c \/ Finite c.
(* begin hide *)
Proof.
  intros.
  destruct (conat_nat_order (f c) c) as [Hlec | Hgtc].
    right. eapply lec_spec. eassumption.
    left.
    {
      apply Infinite_not_from_nat.
      intros n Heq.
      apply (gtc_from_nat (f c)).
      subst. rewrite H in *.
      assumption.
    }
Qed.
(* end hide *)

(** ** Losowe ćwiczenia *)

(** **** Ćwiczenie *)

(** Pokaż, że niezaprzeczalnie każda liczba konaturalna jest skończona
    lub nieskończona. *)

Lemma Finite_or_Infinite :
  forall c : conat, ~ ~ (Finite c \/ Infinite c).
(* begin hide *)
Proof.
  intros c H.
  apply H. right. revert c H. cofix CH.
  destruct c as [[| c']]; intro H.
    2: { exfalso. apply H. left. constructor. }
    constructor. exists c'. split.
      cbn. reflexivity.
      apply CH. intros [H' | H']; apply H.
        left. constructor. assumption.
        right. constructor. exists c'. split.
          cbn. reflexivity.
          assumption.
Qed.
(* end hide *)