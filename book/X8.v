(** * X8: Liczby konaturalne *)

(** TODO: coś tu napisać. *)

(** Zdefiniuj liczby konaturalne oraz ich relację bipodobieństwa. Pokaż,
    że jest to relacja równoważności. *)

(* begin hide *)
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
  forall {n m : conat}, sim n m -> n = m.

Ltac inv H := inversion H; subst; clear H; auto.

Ltac invle H n m :=
  let n' := fresh n "'" in
  let m' := fresh m "'" in
  let H1 := fresh H "1" in
  let H2 := fresh H "2" in
  let H3 := fresh H "3" in
    destruct H as [[| (n' & m' & H1 & H2 & H3)]].
(* end hide *)

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

(** Dzięki poniższemu będziemy mogli używac taktyki [rewrite] do
    przepisywania [sim] tak samo jak [=]. *)

Require Import Setoid.

Instance Equivalence_sim : Equivalence sim.
Proof.
  esplit; red.
    apply sim_refl.
    apply sim_sym.
    apply sim_trans.
Defined.

(** Zdefiniuj zero, następnik oraz liczbę omega - jest to nieskończona
    liczba konaturalna, która jest sama swoim poprzednikiem. Udowodnij
    ich kilka podstawowych właściwości. *)

(* begin hide *)
Definition zero : conat :=
{|
    pred := None;
|}.

Definition succ (n : conat) : conat :=
{|
    pred := Some n;
|}.

CoFixpoint omega : conat :=
{|
    pred := Some omega;
|}.
(* end hide *)

Lemma succ_pred :
  forall n m : conat,
    n = succ m <-> pred n = Some m.
(* begin hide *)
Proof.
  split; intro.
    rewrite H. cbn. reflexivity.
    destruct n as [[n' |]]; inv H.
Qed.
(* end hide *)

Lemma zero_not_omega :
  ~ sim zero omega.
(* begin hide *)
Proof.
  destruct 1 as [[[H1 H2] | (zero' & omega' & H1 & H2 & H3)]].
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
  destruct H as [[[H1 H2] | (n' & succn' & H1 & H2 & H3)]]; cbn in *.
    inv H2.
    right. inv H2. exists n', omega. intuition. apply CH.
      apply succ_pred in H1. rewrite <- H1. assumption.
Qed.
(* end hide *)

Lemma succ_omega :
  omega = succ omega.
(* begin hide *)
Proof.
  apply sim_eq.
  constructor. cbn. right. do 2 eexists. intuition.
Qed.
(* end hide *)

Lemma sim_succ_succ :
  forall n m : conat, sim n m -> sim (succ n) (succ m).
(* begin hide *)
Proof.
  constructor. cbn. right. exists n, m. auto.
Qed.
(* end hide *)

(** Zdefiniuj dodawanie liczb konaturalnych i udowodnij jego podstawowe
    właściwości. *)

(* begin hide *)
CoFixpoint add (n m : conat) : conat :=
{|
    pred :=
      match pred n with
          | None => pred m
          | Some n' => Some (add n' m)
      end
|}.
(* end hide *)

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

Lemma add_omega_l :
  forall n : conat, sim (add omega n) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. right.
  exists (add omega n), omega. auto.
Qed.
(* end hide *)

Lemma add_omega_r :
  forall n : conat, sim (add n omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]]; cbn.
    right. exists (add n' omega), omega. auto.
    right. exists omega, omega. intuition.
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

Lemma add_comm :
  forall n m : conat, sim (add n m) (add m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]], m as [[m' |]]; cbn.
    right. specialize (CH n' (succ m')).
      do 2 eexists. do 2 split; try reflexivity.
        rewrite (sim_eq (add_succ_l _ _)) in CH. apply CH.
    right. do 2 eexists. do 2 split; try reflexivity.
      apply add_zero_r.
    right. do 2 eexists. do 2 split; try reflexivity.
      apply sim_sym. apply add_zero_r.
    left. split; reflexivity.
Qed.
(* end hide *)

(** Zdefiniuj relację [<=] na liczbach konaturalnych i udowodnij jej
    podstawowe właściwości. *)

(* begin hide *)
CoInductive le (n m : conat) : Prop :=
{
    le' :
      pred n = None \/
      exists n' m' : conat,
        pred n = Some n' /\
        pred m = Some m' /\ le n' m'
}.
(* end hide *)

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
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> le n1 m1 -> le n2 m2.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H1 as [[| (n1' & m1' & H1 & H2 & H3)]].
Restart.
  intros.
  rewrite <- (sim_eq H), <- (sim_eq H0). assumption.
Qed.
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
  intros. invle H n zero.
    destruct n. unfold zero. cbn in H. rewrite H. reflexivity.
    cbn in *. inv H2.
Qed.
(* end hide *)

Lemma le_omega_r :
  forall n : conat, le n omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct n as [[n' |]]; cbn.
    right. exists n', omega. auto.
    left. reflexivity.
Qed.
(* end hide *)

Lemma le_omega_l :
  forall n : conat, le omega n -> sim n omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. invle H omega' n; cbn in *.
    inv H.
    inv H1. right. do 2 eexists. intuition. exact H2. apply CH. assumption.
Qed.
(* end hide *)

Lemma le_succ_r :
  forall n m : conat, le n m -> le n (succ m).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[| (n' & m' & H1 & H2 & H3)]].
    left. assumption.
    right. exists n', (succ m'). cbn. intuition. f_equal.
      destruct m as [[m'' |]]; inv H2.
Qed.
(* end hide *)

Lemma le_succ :
  forall n m : conat, le n m -> le (succ n) (succ m).
(* begin hide *)
Proof.
  constructor. cbn. right. exists n, m. intuition.
Qed.
(* end hide *)

Lemma le_add_l :
  forall a b c : conat,
    le a b -> le a (add b c).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[| (n1' & n2' & Hn1 & Hn2 & Hn3)]].
    left. assumption.
    right. cbn. rewrite Hn1, Hn2. do 2 eexists. intuition.
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
  constructor. cbn.
  destruct H as [[| (n1' & n2' & Hn1 & Hn2 & Hn3)]].
    Focus 2. rewrite Hn1, Hn2. right. do 2 eexists. do 2 split.
      reflexivity.
      apply CH; assumption.
    destruct H0 as [[| (m1' & m2' & Hm1 & Hm2 & Hm3)]].
      rewrite H. left. assumption.
      rewrite H, Hm1, Hm2. right. exists m1'.
        destruct (pred n2); eexists; intuition.
        replace m2 with (succ m2').
          apply le_add_r, le_succ_r. assumption.
          symmetry. rewrite succ_pred. assumption.
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

Inductive Finite : conat -> Prop :=
    | Finite_zero : Finite zero
    | Finite_succ : forall n : conat, Finite n -> Finite (succ n).

Lemma omega_not_Finite :
  ~ Finite omega.
(* begin hide *)
Proof.
  intro. remember omega as n. revert Heqn.
  induction H; intro.
    apply (f_equal pred) in Heqn. cbn in Heqn. inv Heqn.
    apply (f_equal pred) in Heqn. cbn in Heqn. inv Heqn.
Qed.
(* end hide *)

CoInductive Infinite (n : conat) : Prop :=
{
    Infinite' :
      exists n' : conat, pred n = Some n' /\ Infinite n';
}.

Lemma Infinite_omega :
(* begin hide *)
  Infinite omega.
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

CoInductive Even (n : conat) : Prop :=
{
    Even' :
      pred n = None \/
      exists n1 n2 : conat,
        pred n = Some n1 /\ pred n1 = Some n2 /\ Even n2;
}.

Lemma Even_Omega :
  Even omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. right.
  exists omega, omega. cbn. intuition.
Qed.
(* end hide *)

CoInductive Odd (n : conat) : Prop :=
{
    Odd' :
      n = succ zero \/
      exists n1 n2 : conat,
        pred n = Some n1 /\ pred n1 = Some n2 /\ Odd n2;
}.

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

Lemma wut :
  forall n m : conat, pred n = pred m -> n = m.
Proof.
  destruct n, m. cbn. destruct 1. reflexivity.
Qed.

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
      apply wut. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Odd_succ :
  forall n : conat, Even n -> Odd (succ n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | (n1 & n2 & H1 & H2 & H3)]].
    left. apply sim_eq. apply sim_succ_succ. constructor.
      left. cbn. auto.
    right. cbn. exists n, n1. intuition. replace n1 with (succ n2).
      apply CH. assumption.
      apply wut. cbn. symmetry. assumption.
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

