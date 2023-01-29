(** * F2: Liczby konaturalne [TODO] *)

Set Primitive Projections.

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

Inductive simF (R : conat -> conat -> Prop) : NatF conat -> NatF conat -> Prop :=
| simF_Z : simF R Z Z
| simF_S : forall n1 n2 : conat, R n1 n2 -> simF R (S n1) (S n2).

CoInductive sim (n m : conat) : Prop :=
{
  sim' : simF sim (out n) (out m);
}.

Axiom sim_eq :
  forall {n m : conat}, (sim n m) = (n = m).

Lemma sim_refl :
  forall n : conat, sim n n.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct (out n) as [| n'].
  - now constructor.
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma sim_sym :
  forall n m : conat, sim n m -> sim m n.
(* begin hide *)
Proof.
  cofix CH.
  intros n m H; constructor.
  destruct H as [[]].
  - now constructor.
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma sim_trans :
  forall a b c : conat, sim a b -> sim b c -> sim a c.
(* begin hide *)
Proof.
  cofix CH.
  intros a b c ab bc.
  constructor.
  destruct ab as [ab], bc as [bc].
  inversion ab; inversion bc; [| congruence.. |].
  - now constructor.
  - constructor.
    now apply CH with n2; [| congruence].
Qed.
(* end hide *)

(** Dzięki poniższemu będziemy mogli używać taktyki [rewrite] do
    przepisywania [sim] tak samo jak [=]. *)

Require Import Setoid.

#[export]
Instance Equivalence_sim : Equivalence sim.
(* begin hide *)
Proof.
  esplit; red.
  - apply sim_refl.
  - apply sim_sym.
  - apply sim_trans.
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
  split.
  - now intros ->; cbn.
  - intros Heq.
    assert (out n = out (succ m)).
      now rewrite Heq; cbn.
Abort.
(* end hide *)

Lemma zero_not_omega :
  ~ sim zero omega.
(* begin hide *)
Proof.
  intros [Hsim]; inversion Hsim.
Qed.
(* end hide *)

Lemma sim_succ_omega :
  forall n : conat, sim n (succ n) -> sim n omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct H as [H]; cbn in H; inversion H; subst.
  constructor.
  apply CH.
  constructor; cbn.
  rewrite H0.
  now apply H2.
Qed.
(* end hide *)

Lemma succ_omega :
  omega = succ omega.
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma sim_succ :
  forall n m : conat, sim n m -> sim (succ n) (succ m).
(* begin hide *)
Proof.
  now do 2 constructor.
Defined.
(* end hide *)

Lemma sim_succ_inv :
  forall n m : conat, sim (succ n) (succ m) -> sim n m.
(* begin hide *)
Proof.
  intros n m [H]; cbn in H.
  now inversion H.
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
  forall n m : conat,
    out n = Z -> add n m = m.
(* begin hide *)
Proof.
  intros n m Heq.
  rewrite <- sim_eq.
  constructor; cbn.
  rewrite Heq.
  now apply sim_refl.
Qed.
(* end hide *)

Lemma add_zero_r :
  forall n : conat,
    sim (add n zero) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n'].
  - now constructor.
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma add_zero_r' :
  forall n m : conat,
    out m = Z -> sim (add n m) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n'].
  - now rewrite H; constructor.
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma sim_add_zero :
  forall n m : conat,
    sim (add n m) zero -> n = zero /\ m = zero.
(* begin hide *)
Proof.
  intros n m [H]; inversion H.
  rewrite <- !sim_eq.
  cbn in *.
  destruct (out n) eqn: Heq; [| now congruence].
  split; constructor; cbn.
  - now rewrite Heq; constructor.
  - now rewrite <- H1; constructor.
Qed.
(* end hide *)

Lemma sim_add_zero_l :
  forall n m : conat,
    sim (add n m) zero -> n = zero.
(* begin hide *)
Proof.
  now intros; apply sim_add_zero in H as [].
Qed.
(* end hide *)

Lemma sim_add_zero_r :
  forall n m : conat,
    sim (add n m) zero -> m = zero.
(* begin hide *)
Proof.
  now intros; apply sim_add_zero in H as [].
Qed.
(* end hide *)

Lemma add_omega_l :
  forall n : conat, sim (add omega n) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma add_omega_r :
  forall n : conat, sim (add n omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n).
  - now constructor.
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma add_succ_l :
  forall n m : conat, add (succ n) m = succ (add n m).
(* begin hide *)
Proof.
  intros n m.
  rewrite <- sim_eq.
  constructor; cbn; constructor.
  reflexivity.
Qed.
(* end hide *)

Lemma add_succ_r' :
  forall n m m' : conat, out m = S m' -> sim (add n m) (succ (add n m')).
Proof.
  cofix CH.
  intros n m m' Hm.
  constructor; cbn.
  destruct (out n) as [| n'] eqn: Hn.
  - rewrite Hm.
    constructor.
    now rewrite add_zero_l.
  - constructor.
Abort.

Lemma add_succ_r :
  forall n m : conat, sim (add n (succ m)) (succ (add n m)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n'] eqn: Heq; constructor.
  - constructor; cbn.
    rewrite Heq.
    apply sim_refl.
  - constructor; cbn.
    rewrite Heq.
    apply (CH n' m).
Abort.
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
  constructor; cbn.
  destruct (out a) as [| a'] eqn: Ha.
  - now apply (sim_refl (add b c)).
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma add_comm :
  forall n m : conat, sim (add n m) (add m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n'] eqn: Hn, (out m) as [| m'] eqn: Hm.
  - now constructor.
  - constructor.
    now rewrite add_zero_r'.
  - constructor.
    now rewrite add_zero_r'.
  - constructor.
Abort.
(* end hide *)

Lemma sim_add :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> sim (add n1 m1) (add n2 m2).
(* begin hide *)
Proof.
  cofix CH.
  intros n1 n2 m1 m2 [Hn] [Hm].
  constructor; cbn.
  inversion Hn; inversion Hm; constructor; [easy | ..].
  - now rewrite !add_zero_r'.
  - now apply CH.
Qed.
(* end hide *)

(** * Lepsze dodawanie *)

(* begin hide *)
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

CoFixpoint add'' (n m : conat) : conat :=
match out n, out m with
| Z   , _    => m
| _   , Z    => n
| S n', S m' => succ (succ (add'' n' m'))
end.
(* end hide *)

Lemma sim_add_add' :
  forall n m : conat,
    sim (add n m) (add' n m).
(* begin hide *)
Proof.
  (* To raczej nie przejdzie *)
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n'].
  - now apply sim_refl.
  - destruct (out m) as [| m'] eqn: Heq.
    + constructor.
      now rewrite add_zero_r'.
    +
Abort.
(* end hide *)

Lemma add'_comm :
  forall n m : conat,
    sim (add' n m) (add' m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n'], (out m) as [| m']; constructor; [easy.. |].
  do 2 (constructor; cbn).
  apply CH.
Qed.
(* end hide *)

Lemma add'_zero_l :
  forall n m : conat,
    out n = Z -> sim (add' n m) m.
(* begin hide *)
Proof.
  intros n m Hn.
  constructor; cbn.
  rewrite Hn.
  now apply sim_refl.
Qed.
(* end hide *)

Lemma add'_zero_r :
  forall n m : conat,
    out m = Z -> sim (add' n m) n.
(* begin hide *)
Proof.
  intros.
  rewrite add'_comm.
  now apply add'_zero_l.
Qed.
(* end hide *)

Lemma sim_add'_zero :
  forall n m : conat,
    sim (add' n m) zero -> sim n zero /\ sim m zero.
(* begin hide *)
Proof.
  intros n m [H]; inversion H; cbn in *.
  destruct (out n) as [| n'] eqn: Hn,
           (out m) as [| m'] eqn: Hm;
    [| now congruence..].
  now split; constructor; cbn; rewrite ?Hn, ?Hm; constructor.
Qed.
(* end hide *)

Lemma sim_add'_zero_l :
  forall n m : conat,
    sim (add' n m) zero -> sim n zero.
(* begin hide *)
Proof.
  now intros n m [H _]%sim_add'_zero.
Qed.
(* end hide *)

Lemma sim_add'_zero_r :
  forall n m : conat,
    sim (add' n m) zero -> sim m zero.
(* begin hide *)
Proof.
  now intros n m [_ H]%sim_add'_zero.
Qed.
(* end hide *)

Lemma add'_omega_l :
  forall n : conat,
    sim (add' omega n) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n'].
  - now constructor.
  - constructor; cbn.
    do 2 (constructor; cbn).
    now apply CH.
Qed.
(* end hide *)

Lemma add'_omega_r :
  forall n : conat,
    sim (add' n omega) omega.
(* begin hide *)
Proof.
  intros.
  rewrite add'_comm.
  now apply add'_omega_l.
Qed.
(* end hide *)

Lemma add'_S_l :
  forall n n' m : conat,
    out n = S n' -> sim (add' n m) (succ (add' n' m)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  rewrite H.
  destruct (out m) as [| m'] eqn: Hm; constructor.
  - now rewrite add'_zero_r.
  - constructor; cbn.
    rewrite Hm.
    destruct (out n') as [| n''] eqn: Hn'; constructor.
    + now rewrite add'_zero_l.
    + now apply CH.
Defined.
(* end hide *)

Lemma add'_S_r :
  forall n m m' : conat,
    out m = S m' -> sim (add' n m) (succ (add' n m')).
(* begin hide *)
Proof.
  intros.
  rewrite add'_comm.
  rewrite add'_S_l; [| eassumption].
  apply sim_succ.
  now rewrite add'_comm.
Qed.
(* end hide *)

Lemma add'_succ_l :
  forall n m : conat,
    sim (add' (succ n) m) (succ (add' n m)).
(* begin hide *)
Proof.
  now intros; rewrite add'_S_l.
Qed.
(* end hide *)

Lemma add'_succ_r :
  forall n m : conat,
    sim (add' n (succ m)) (succ (add' n m)).
(* begin hide *)
Proof.
  now intros; rewrite add'_S_r.
Defined.
(* end hide *)

Lemma add'_succ_l' :
  forall n m : conat,
    sim (add' (succ n) m) (add' n (succ m)).
(* begin hide *)
Proof.
  now intros; rewrite add'_succ_l, add'_succ_r.
Qed.
(* end hide *)

Lemma add'_succ_r' :
  forall n m : conat,
    sim (add' n (succ m)) (add' (succ n) m).
(* begin hide *)
Proof.
  now intros; rewrite add'_succ_l, add'_succ_r.
Qed.
(* end hide *)

#[global] Hint Constructors simF sim : core.

Lemma sim_add' :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> sim (add' n1 m1) (add' n2 m2).
(* begin hide *)
Proof.
  cofix CH.
  intros n1 n2 m1 m2 [Hn] [Hm].
  constructor; cbn.
  inversion Hn; inversion Hm; constructor; [easy.. |].
  constructor; cbn; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma add'_comp :
  forall n m : conat,
    sim (add' (succ n) (succ m)) (succ (succ (add' n m))).
(* begin hide *)
Proof.
  now do 2 (constructor; cbn; constructor).
Qed.
(* end hide *)

Require Import SetoidClass.

#[export]
Instance sim_add'' :
  Proper (sim ==> sim ==> sim) add'.
(* begin hide *)
Proof.
  cofix CH.
  intros n1 n2 [Hn] m1 m2 [Hm].
  constructor; cbn.
  inversion Hn; inversion Hm; constructor; [easy.. |].
  constructor; cbn; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma add'_assoc :
  forall a b c : conat,
    sim (add' (add' a b) c) (add' a (add' b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out a) as [| a'], (out b) as [| b'], (out c) as [| c']; constructor; [easy.. |].
  constructor; cbn; constructor.
  constructor; cbn.
  destruct (out a') as [| a''] eqn: Ha,
           (out c') as [| c''] eqn: Hc;
    constructor; cbn.
  - admit.
  - admit.
  - admit.
  - constructor; cbn; constructor.
    constructor; cbn.
    rewrite Ha, Hc.
    destruct (out a'') as [| a'''], (out b') as [| b''], (out c'') as [| c'''].
      constructor.
Abort.
(* end hide *)

(** * Porządek *)

(** Zdefiniuj relację [<=] na liczbach konaturalnych i udowodnij jej
    podstawowe właściwości. *)

(* begin hide *)
Inductive leF (R : conat -> conat -> Prop) : NatF conat -> NatF conat -> Prop :=
| leF_Z : forall m : NatF conat, leF R Z m
| leF_S : forall n m : conat, R n m -> leF R (S n) (S m).

CoInductive le (n m : conat) : Prop :=
{
  le' : leF le (out n) (out m);
}.
(* end hide *)

Lemma le_0_l :
  forall n : conat,
    le zero n.
(* begin hide *)
Proof.
  now constructor; cbn; constructor.
Qed.
(* end hide *)

Lemma le_0_r :
  forall n : conat,
    le n zero -> sim n zero.
(* begin hide *)
Proof.
  intros n [H].
  constructor; cbn.
  inversion H.
  now constructor.
Qed.
(* end hide *)

Lemma le_succ :
  forall n m : conat,
    le n m -> le (succ n) (succ m).
(* begin hide *)
Proof.
  now constructor; cbn; constructor.
Qed.
(* end hide *)

Lemma le_succ_conv :
  forall n m : conat,
    le (succ n) (succ m) -> le n m.
(* begin hide *)
Proof.
  now intros n m [H]; inversion H.
Qed.
(* end hide *)

Lemma le_refl :
  forall n : conat,
    le n n.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n']; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma le_trans :
  forall a b c : conat,
    le a b -> le b c -> le a c.
(* begin hide *)
Proof.
  cofix CH.
  intros a b c [Hab] [Hbc].
  constructor.
  inversion Hab; inversion Hbc; subst;
    [| | congruence |]; constructor.
  now eapply CH; [eassumption | congruence].
Qed.
(* end hide *)

Lemma le_univalent :
  forall n m : conat,
    le n m -> le m n -> sim n m.
(* begin hide *)
Proof.
  cofix CH.
  intros n m [Hnm] [Hmn].
  constructor.
  inversion Hnm; inversion Hmn; subst;
    [constructor | congruence.. | constructor].
  now apply CH; [| congruence].
Qed.
(* end hide *)

Lemma le_sim :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> le n1 m1 -> le n2 m2.
(* begin hide *)
Proof.
  cofix CH.
  intros n1 n2 m1 m2 [Hn] [Hm] [Hnm].
  constructor.
  inversion Hn; inversion Hm; inversion Hnm; subst; try congruence.
  - now constructor.
  - constructor.
    apply (CH _ _ _ _ H1 H4).
    now congruence.
Qed.
(* end hide *)

Lemma le_omega_r :
  forall n : conat,
    le n omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n']; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma le_omega_l :
  forall n : conat,
    le omega n -> sim n omega.
(* begin hide *)
Proof.
  cofix CH.
  intros n [H].
  constructor; cbn.
  inversion H; cbn in *.
  constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma le_succ_r' :
  forall n m m' : conat,
    out m = S m' -> le n m' -> le n m.
(* begin hide *)
Proof.
  cofix CH.
  intros n m m' Hm [Hle].
  constructor; cbn.
  rewrite Hm.
  inversion Hle; constructor.
  now apply CH with m0.
Qed.

Lemma le_succ_r :
  forall n m : conat,
    le n m -> le n (succ m).
(* begin hide *)
Proof.
  now intros; eapply le_succ_r'.
Qed.
(* end hide *)

Lemma le_add_l :
  forall a b c : conat,
    le a b -> le a (add b c).
(* begin hide *)
Proof.
  cofix CH.
  intros a b c [H].
  constructor; cbn.
  inversion H; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma le_add_r :
  forall a b c : conat,
    le a c -> le a (add b c).
(* begin hide *)
Proof.
  cofix CH.
  intros a b c [H].
  constructor; cbn.
  inversion H; [now constructor |].
  destruct (out b) as [| b']; constructor; [easy |].
  apply CH.
  apply le_trans with m; [easy |].
Abort.
(* end hide *)

Lemma le_add :
  forall n1 n2 m1 m2 : conat,
    le n1 n2 -> le m1 m2 -> le (add n1 m1) (add n2 m2).
(* begin hide *)
Proof.
  cofix CH.
  intros n1 n2 m1 m2 [Hn] [Hm].
  constructor; cbn.
  inversion Hn; inversion Hm.
  - now constructor.
  - rewrite <- H1.
    destruct m; constructor; [easy |].
    apply le_add_l.
Admitted.
(* end hide *)

Lemma le_add_l' :
  forall n m : conat,
    le n (add n m).
(* begin hide *)
Proof.
  intros; apply le_add_l, le_refl.
Qed.
(* end hide *)

#[export]
Instance Proper_le :
  Proper (sim ==> sim ==> iff) le.
(* begin hide *)
Proof.
  now split; apply le_sim.
Qed.
(* end hide *)

#[export]
Instance Proper_le' :
  Proper (sim ==> sim ==> Basics.flip Basics.impl) le.
(* begin hide *)
Proof.
  intros n1 n2 Hn m1 m2 Hm Hle.
  now eapply le_sim; [symmetry.. | apply Hle].
Qed.
(* end hide *)

Lemma le_add_r' :
  forall n m : conat, le m (add n m).
(* begin hide *)
Proof.
  cofix CH.
  intros.
  destruct (out n) as [| n'] eqn: Heq.
  - now rewrite add_zero_l; [apply le_refl |].
  - constructor; cbn.
    rewrite Heq.
    destruct (out m) as [| m']; constructor.
Abort.
(* end hide *)

Lemma le_add_l'' :
  forall n n' m : conat,
    le n n' -> le (add n m) (add n' m).
(* begin hide *)
Proof.
  now intros; apply le_add; [| apply le_refl].
Qed.
(* end hide *)

Lemma le_add_r'' :
  forall n m m' : conat,
    le m m' -> le (add n m) (add n m').
(* begin hide *)
Proof.
  now intros; apply le_add; [apply le_refl |].
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
  forall n : conat,
    sim (min zero n) zero.
(* begin hide *)
Proof.
  now constructor; cbn; constructor.
Qed.
(* end hide *)

Lemma min_zero_r :
  forall n : conat,
    sim (min n zero) zero.
(* begin hide *)
Proof.
  constructor; cbn.
  now destruct (out n); constructor.
Qed.
(* end hide *)

Lemma min_omega_l :
  forall n : conat,
    sim (min omega n) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n']; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma min_omega_r :
  forall n : conat,
    sim (min n omega) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n']; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma min_succ :
  forall n m : conat,
    sim (min (succ n) (succ m)) (succ (min n m)).
(* begin hide *)
Proof.
  now constructor; cbn; constructor.
Qed.
(* end hide *)

Lemma max_zero_l :
  forall n : conat,
    sim (max zero n) n.
(* begin hide *)
Proof.
  constructor; cbn.
  now apply sim_refl.
Qed.
(* end hide *)

Lemma max_zero_r :
  forall n : conat,
    sim (max n zero) n.
(* begin hide *)
Proof.
  constructor; cbn.
  now destruct (out n) as [| n']; constructor.
Qed.
(* end hide *)

Lemma max_omega_l :
  forall n : conat,
    sim (max omega n) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n']; constructor; [easy |].
  now apply CH.
Qed.
(* end hide *)

Lemma max_omega_r :
  forall n : conat,
    sim (max n omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n']; constructor; [easy |].
  now apply CH.
Qed.
(* end hide *)

Lemma max_succ :
  forall n m : conat,
    sim (max (succ n) (succ m)) (succ (max n m)).
(* begin hide *)
Proof.
  now constructor; cbn; constructor.
Qed.
(* end hide *)

Lemma min_assoc :
  forall a b c : conat,
    sim (min (min a b) c) (min a (min b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  now destruct (out a), (out b), (out c); constructor.
Qed.
(* end hide *)

Lemma max_assoc :
  forall a b c : conat,
    sim (max (max a b) c) (max a (max b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  now destruct (out a), (out b), (out c); constructor.
Qed.
(* end hide *)

Lemma min_comm :
  forall n m : conat,
    sim (min n m) (min m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  now destruct (out n), (out m); constructor.
Qed.
(* end hide *)

Lemma max_comm :
  forall n m : conat,
    sim (max n m) (max m n).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  now destruct (out n), (out m); constructor.
Qed.
(* end hide *)

Lemma min_le :
  forall n m : conat,
    le n m -> sim (min n m) n.
(* begin hide *)
Proof.
  cofix CH.
  intros n m [Hle].
  constructor; cbn.
  inversion Hle; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma max_le :
  forall n m : conat, le n m -> sim (max n m) m.
(* begin hide *)
Proof.
  cofix CH.
  intros n m [Hle].
  constructor; cbn.
  inversion Hle.
  - now apply sim_refl.
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma min_diag :
  forall n : conat,
    sim (min n n) n.
(* begin hide *)
Proof.
  now intros; apply min_le, le_refl.
Qed.
(* end hide *)

Lemma max_diag :
  forall n : conat,
    sim (max n n) n.
(* begin hide *)
Proof.
  now intros; apply max_le, le_refl.
Qed.
(* end hide *)

Lemma min_add_l :
  forall a b c : conat,
    sim (min (add a b) (add a c)) (add a (min b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  now destruct (out a), (out b), (out c); constructor.
Qed.
(* end hide *)

Lemma min_add_r :
  forall a b c : conat,
    sim (min (add a c) (add b c)) (add (min a b) c).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out a) as [| a'], (out b) as [| b'], (out c) as [| c']; constructor.
  - now apply min_diag.
  - admit.
  - admit.
  - easy.
  - easy.
Abort.
(*
  cofix CH.
  constructor.
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn; auto.
    all: eright; cbn; intuition.
      rewrite min_diag. apply sim_refl.
      apply min_le. apply le_add_r. apply le_succ_r. apply le_refl.
        rewrite min_comm. apply min_le. apply le_add_r. apply le_succ_r. apply le_refl.
*)
(* end hide *)

Lemma max_add_l :
  forall a b c : conat,
    sim (max (add a b) (add a c)) (add a (max b c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  now destruct (out a), (out b), (out c); constructor.
Qed.
(* end hide *)

Lemma max_add_r :
  forall a b c : conat,
    sim (max (add a c) (add b c)) (add (max a b) c).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out a), (out b), (out c); constructor; try easy.
  - now apply max_diag.
  - admit.
  - admit.
Abort.
(*
  destruct a as [[| a']], b as [[| b']], c as [[| c']]; cbn; auto.
    all: eright; cbn; eauto.
      rewrite max_diag. apply sim_refl.
      rewrite add_zero_r. apply sim_refl.
      apply max_le, le_add_r, le_succ_r, le_refl.
      apply sim_refl.
      rewrite max_comm. apply max_le, le_add_r, le_succ_r, le_refl.
*)
(* end hide *)

Lemma sim_min_max :
  forall n m : conat,
    sim (min n m) (max n m) -> sim n m.
(* begin hide *)
Proof.
  cofix CH.
  intros n m [H]; cbn in H.
  constructor.
  destruct (out n) as [| n'], (out m) as [| m'];
    inversion H; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma min_max :
  forall a b : conat,
    sim (min a (max a b)) a.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out a), (out b); constructor.
  - apply min_diag.
  - apply CH.
Qed.
(* end hide *)

Lemma max_min :
  forall a b : conat,
    sim (max a (min a b)) a.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  now destruct (out a), (out b); constructor.
Qed.
(* end hide *)

Lemma min_max_distr :
  forall a b c : conat,
    sim (min a (max b c)) (max (min a b) (min a c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  now destruct (out a), (out b), (out c); constructor.
Qed.
(* end hide *)

Lemma max_min_distr :
  forall a b c : conat,
    sim (max a (min b c)) (min (max a b) (max a c)).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out a), (out b), (out c); constructor; [try easy.. |].
  - now symmetry; apply min_diag.
  - now rewrite min_max.
  - now rewrite min_comm, min_max.
  - now apply CH.
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
  constructor; cbn; constructor.
Qed.
(* end hide *)

Lemma div2_omega :
  sim (div2 omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; constructor.
  apply CH.
Qed.
(* end hide *)

Lemma div2_succ :
  forall n : conat,
    sim (div2 (succ (succ n))) (succ (div2 n)).
(* begin hide *)
Proof.
  now constructor; cbn; constructor.
Qed.
(* end hide *)

Lemma div2_add' :
  forall n : conat,
    sim (div2 (add' n n)) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out n) as [| n']; cbn; constructor.
  apply CH.
Qed.
(* end hide *)

Lemma le_div2_l' :
  forall n m : conat,
    le n m -> le (div2 n) m.
(* begin hide *)
Proof.
  cofix CH.
  intros n m [H].
  constructor; cbn.
  inversion H as [| n' m' [H']]; [constructor |].
  inversion H'; constructor.
  apply CH.
  setoid_replace m' with (succ m0) using relation sim.
  - apply le_trans with m0; [easy |].
    apply le_succ_r, le_refl.
  - constructor; cbn.
    rewrite <- H3.
    now constructor.
Qed.
(* end hide *)

Lemma le_div2_l :
  forall n : conat,
    le (div2 n) n.
(* begin hide *)
Proof.
  intros; apply le_div2_l', le_refl.
Qed.
(* end hide *)

Lemma le_div2 :
  forall n m : conat,
    le n m -> le (div2 n) (div2 m).
(* begin hide *)
Proof.
  cofix CH.
  intros n m [H].
  constructor; cbn.
  inversion H as [| n' m' [H'] Hn Hm]; [constructor |].
  inversion H'; constructor.
  now apply CH.
Qed.
(* end hide *)

(** * Skończoność i nieskończoność *)

(** Zdefiniuj predykaty [Finite] i [Infinite], które wiadomo co znaczą.
    Pokaż, że omega jest liczbą nieskończoną i że nie jest skończona,
    oraz że każda liczba nieskończona jest bipodobna do omegi. Pokaż
    też, że żadna liczba nie może być jednocześnie skończona i
    nieskończona. *)

(* begin hide *)
Inductive Finite : conat -> Prop :=
| Finite_zero : Finite zero
| Finite_succ : forall n : conat, Finite n -> Finite (succ n).

Inductive InfiniteF (P : conat -> Prop) : NatF conat -> Prop :=
| InfiniteF' :
    forall (n : conat),
      P n -> InfiniteF P (S n).

CoInductive Infinite (n : conat) : Prop :=
{
  Infinite' : InfiniteF Infinite (out n);
}.
(* end hide *)

Lemma omega_not_Finite :
  ~ Finite omega.
(* begin hide *)
Proof.
  intros HF.
  remember omega as n; revert Heqn.
  induction HF; intros.
  - apply (f_equal out) in Heqn; inversion Heqn.
  - apply (f_equal out) in Heqn as [=]; cbn in H.
    now apply IHHF.
Qed.
(* end hide *)

Lemma Infinite_omega :
  Infinite omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma Infinite_omega' :
  forall n : conat,
    Infinite n -> sim n omega.
(* begin hide *)
Proof.
  cofix CH.
  intros n [H].
  constructor; cbn.
  inversion H; constructor.
  now apply CH.
Qed.
(* end hide *)

Lemma Finite_Infinite :
  forall n : conat,
    Finite n -> Infinite n -> False.
(* begin hide *)
Proof.
  induction 1; intros [HI]; inversion HI.
  now apply IHFinite.
Qed.
(* end hide *)

(** * Parzystość i nieparzystość *)

(** Zdefiniuj predykaty [Even] i [Odd]. Pokaż, że omega jest jednocześnie
    parzysta i nieparzysta. Pokaż, że jeżeli liczba jest jednocześnie
    parzysta i nieparzysta, to jest nieskończona. Wyciągnij z tego oczywisty
    wniosek. Pokaż, że każda liczba skończona jest parzysta albo
    nieparzysta. *)

(* begin hide *)
Inductive EvenF (P : conat -> Prop) : NatF conat -> Prop :=
| EvenF_Z  : EvenF P Z
| EvenF_SS :
    forall (n n' : conat), out n = S n' -> P n' -> EvenF P (S n).

CoInductive Even (n : conat) : Prop :=
{
  Even' : EvenF Even (out n)
}.

Inductive OddF (P : conat -> Prop) : NatF conat -> Prop :=
| OddF_SZ :
    forall (n : conat), out n = Z -> OddF P (S n)
| OddF_SS :
    forall (n n' : conat), out n = S n' -> P n' -> OddF P (S n).

CoInductive Odd (n : conat) : Prop :=
{
  Odd' : OddF Odd (out n);
}.
(* end hide *)

Lemma Even_zero :
  Even zero.
(* begin hide *)
Proof.
  constructor; cbn; constructor.
Qed.
(* end hide *)

Lemma Odd_zero :
  ~ Odd zero.
(* begin hide *)
Proof.
  intros [H]; inversion H.
Qed.
(* end hide *)

Lemma Even_Omega :
  Even omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; econstructor; [now cbn |].
  apply CH.
Qed.
(* end hide *)

Lemma Odd_Omega :
  Odd omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; econstructor 2; [now cbn |].
  apply CH.
Qed.
(* end hide *)

Lemma Even_Odd_Infinite :
  forall n : conat,
    Even n -> Odd n -> Infinite n.
(* begin hide *)
Proof.
  cofix CH.
  intros n [HE] [HO].
  constructor.
  inversion HO; constructor.
  - rewrite <- H in HE.
    inversion HE; congruence.
  - constructor; rewrite H0; constructor.
    apply CH; [| easy].
    inversion HE; congruence.
Qed.
(* end hide *)

Lemma Even_succ :
  forall n : conat,
    Odd n -> Even (succ n).
(* begin hide *)
Proof.
  cofix CH.
  intros n [HO].
  constructor; cbn.
  inversion HO.
  - econstructor 2 with n0; [easy |].
Restart.

  cofix CH.
  constructor. destruct H as [[n' H | n1 n2 Hn1 Hn2 HOdd]].
    eright; cbn; eauto. constructor. left. assumption.
    eright; cbn; eauto. replace n1 with (succ n2).
      apply CH. assumption.
      apply eq_out. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Odd_succ :
  forall n : conat, Even n -> Odd (succ n).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[H | n1 n2 Hn1 Hn2 HOdd]].
    left with n; cbn; auto.
    right with n n1; cbn; auto. replace n1 with (succ n2).
      apply CH. assumption.
      apply eq_out. cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Even_succ_inv :
  forall n : conat, Odd (succ n) -> Even n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[n1 Hn1 | n1 n2 Hn1 Hn2 HOdd]].
    inv Hn1. left. assumption.
    inv Hn1. destruct HOdd as [[n3 Hn3 | n3 n4 Hn3 Hn4 HEven]].
      eright; cbn; eauto. apply CH.
        constructor; eleft; cbn; eauto.
      eright; cbn; eauto. apply CH.
        constructor; eright; cbn; eauto.
Qed.
(* end hide *)

Lemma Odd_succ_inv :
  forall n : conat, Even (succ n) -> Odd n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct H as [[]]; cbn in *.
    inv Hn.
    inv Hn1. destruct HEven as [[Hn2' | n3 n4 Hn3 Hn4 HEven]].
      left with n2; assumption.
      eright; cbn; try eassumption. apply CH. replace (succ n3) with n2.
        constructor; eright; cbn; eassumption.
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
  destruct 1 as [[n' Hn | n1 n2 Hn1 Hn2 HEven]]; intro.
    replace (add n m) with (succ m).
      apply Even_succ. assumption.
      apply eq_out. cbn. rewrite Hn. f_equal.
        apply eq_out. cbn. rewrite Hn'. reflexivity.
    constructor. eright.
      cbn. rewrite Hn1. reflexivity.
      cbn. rewrite Hn2. reflexivity.
      apply CH; assumption.
Qed.
(* end hide *)

Lemma Even_add_Even :
  forall n m : conat, Even n -> Even m -> Even (add n m).
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [[Hn | n1 n2 Hn1 Hn2 HEven]]; intro.
    replace (add n m) with m.
      assumption.
      apply eq_out. cbn. rewrite Hn. reflexivity.
    constructor; eright.
      cbn. rewrite Hn1. reflexivity.
      cbn. rewrite Hn2. reflexivity.
      apply CH; assumption.
Qed.
(* end hide *)

Lemma Odd_add :
  forall n m : conat, Even n -> Odd m -> Odd (add n m).
(* begin hide *)
Proof.
  cofix CH.
  intros n m [[Hn | n1 n2 Hn1 Hn2 HEven]] HOdd.
    rewrite add_zero_l; assumption.
    constructor. eright.
      cbn. rewrite Hn1. reflexivity.
      cbn. rewrite Hn2. reflexivity.
      apply CH; assumption.
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
  constructor. destruct r as [[| r']]; cbn.
    eright; cbn; reflexivity.
    eright; cbn; try reflexivity. apply CH.
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
      [omega - omega = (omega + 1) - omega = 1], co prowadzi do sprzeczności

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
| S n', Datatypes.S m' => subn n' m'
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
    rewrite !add_succ_r in H0.
      apply sim_succ_inv in H0. apply IHFinite. assumption.
Qed.

Lemma Finite_sim :
  forall n m : conat,
    sim n m -> Finite n -> Finite m.
Proof.
  intros until 2. revert m H.
  induction H0; intros.
    destruct H as [[]]; cbn in *.
      replace m with zero.
        apply Finite_zero.
        apply eq_out. cbn. congruence.
      inv Hn.
    destruct m as [[| m']].
      constructor.
      constructor. apply IHFinite. apply sim_succ_inv. exact H.
Qed.

Lemma Finite_add :
  forall n m : conat,
    Finite n -> Finite m -> Finite (add n m).
Proof.
  intros until 1. revert m.
  induction H; intros.
    rewrite add_zero_l.
      assumption.
      reflexivity.
    apply Finite_sim with (succ (add n m)).
      rewrite add_succ_l. reflexivity.
      constructor. apply IHFinite. assumption.
Qed.

Lemma Finite_add_inv_l :
  forall n m : conat,
    Finite (add n m) -> Finite n.
Proof.
  intros.
  remember (add n m) as c. revert n m Heqc.
  induction H; intros.
    destruct n as [[| n']].
      constructor.
      apply (f_equal out) in Heqc. cbn in Heqc. inv Heqc.
    destruct n0 as [[| n']].
      constructor.
      apply (f_equal out) in Heqc. inv Heqc.
        constructor. eapply IHFinite. reflexivity.
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

(* begin hide *)
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
(* end hide *)

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
  intros [[| n']] [[| m']] acc1 acc2 H.
    1-3: rewrite !mul'_zero_l, ?mul'_zero_r; cbn; auto.
    constructor. eright; cbn; try reflexivity. apply CH. rewrite <- !add_assoc. apply sim_add.
      apply add_comm.
      assumption.
Qed.
(* end hide *)

Lemma mul'_one_l :
  forall c acc : conat,
    sim (mul' (succ zero) c acc) (add c acc).
(* begin hide *)
Proof.
  destruct c as [[| c']]; constructor; cbn.
    destruct acc as [[| acc']]; cbn; eauto.
      eright; cbn; reflexivity.
    eright; cbn; try reflexivity. rewrite mul'_zero_l, add_zero_l; cbn; reflexivity.
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
  destruct c as [[| c']]; constructor; cbn in *.
    congruence.
    eright; cbn; try reflexivity. destruct c' as [[| c'']].
      rewrite mul'_zero_r, (add_zero_l _ acc).
        apply add_omega_l.
        1-2: reflexivity.
      apply CH. cbn. inversion 1.
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

(* Inductive Finite' : conat -> Prop :=
| Finite'_zero :
    forall n : conat, out n = Z -> Finite' n
| Finite'_succ :
    forall n n' : conat, out n = S n' -> Finite' n' -> Finite' n.

#[global] Hint Constructors Finite' : core. *)

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
  intros n [[| m']] acc.
    rewrite !mul'_zero_r, add_zero_l; reflexivity.
    constructor; eright; cbn; try reflexivity.
      rewrite !mul'_acc.
Admitted.
(* end hide *)

Lemma Finite_mul' :
  forall n m acc : conat,
    Finite n -> Finite m -> Finite acc ->
      Finite (mul' n m acc).
(* begin hide *)
Proof.
  intros n m acc Hn Hm Hacc.
  revert m acc Hm Hacc.
  induction Hn as [| n' Hn IH]; intros.
    rewrite mul'_zero_l. assumption.
    eapply Finite_sim.
      symmetry. apply mul'_succ_l.
      apply Finite_add.
        assumption.
        apply IH; assumption.
Qed.
(* end hide *)

Lemma mul'_assoc :
  forall a b c acc1 acc1' acc2 acc2' : conat,
    sim acc1 acc1' -> sim acc2 acc2' ->
      sim (mul' a (mul' b c acc1) acc2) (mul' (mul' a b acc1') c acc2').
(* begin hide *)
Proof.
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
    exists n' : conat,
      out n = S n' /\ Even2 n';
}.
(* end hide *)

Module Even2_v2.

Inductive Even2F (n : conat) (P : conat -> Prop) : Prop :=
| Even2_Z  :
    forall Hn : out n = Z, Even2F n P
| Even2_SS :
    forall (n' : conat) (Hn : out n = S n'),
      P n' -> Even2F n P.

Inductive Odd2F (n : conat) (P : conat -> Prop) : Prop :=
| Odd2_S :
    forall (n' : conat) (Hn : out n = S n') (HOdd : P n'), Odd2F n P.

CoInductive Even2' (n : conat) : Prop :=
{
  Even2'' : Even2F n Odd2'
}

with Odd2' (n : conat) : Prop :=
{
  Odd2'' : Odd2F n Even2'
}.

Lemma Even2_Even2' :
  forall n : conat, Even2 n -> Even2' n

with Odd2_Odd2' :
  forall n : conat, Odd2 n -> Odd2' n.
(* begin hide *)
Proof.
  intros n [[Hn | [n' [Hn HOdd]]]]; constructor.
    left. assumption.
    right with n'.
      assumption.
      apply Odd2_Odd2'. assumption.

  intros n [[n' [Hn HEven]]]. constructor. exists n'.
    assumption.
    apply Even2_Even2'. assumption.
Qed.
(* end hide *)

Lemma Even2'_Even2 :
  forall n : conat, Even2' n -> Even2 n

with Odd2'_Odd2 :
  forall n : conat, Odd2' n -> Odd2 n.
(* begin hide *)
Proof.
  intros n [[Hn | n' Hn HOdd]]; constructor.
    left. assumption.
    right. exists n'. split.
      assumption.
      apply Odd2'_Odd2. assumption.

  intros n [[n' Hn HEven]]. constructor. exists n'. split.
    assumption.
    apply Even2'_Even2. assumption.
Qed.
(* end hide *)

End Even2_v2.

Lemma Even2_add_Odd2 :
  forall n m : conat, Odd2 n -> Odd2 m -> Even2 (add n m)

with Even2_add_Odd2_Even2 :
  forall n m : conat, Even2 n -> Odd2 m -> Odd2 (add n m).
(* begin hide *)
Proof.
  constructor. destruct H as [(n' & H1 & H2)].
    cbn. rewrite H1. right. eexists. intuition.
  constructor.
  destruct H as [[H | (n' & H1 & H2)]],
          H0 as [(m' & H1' & H2')]; subst; cbn.
    rewrite H. exists m'. intuition.
    rewrite H1. exists (add n' m). intuition. apply Even2_add_Odd2.
      assumption.
      constructor. exists m'. auto.
Qed.
(* end hide *)

(** * Liczby naturalne i konaturalne *)

(** Zdefiniuj funkcję [from_nat], która przekształca liczbę naturalną
    w odpowiadającą jej skończoną liczbę konaturalną. *)

(* begin hide *)
Fixpoint from_nat (n : nat) : conat :=
match n with
| 0 => zero
| Datatypes.S n' => succ (from_nat n')
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
| lec_S : forall (c : conat) (n : nat), lec c n -> lec (succ c) (Datatypes.S n).

Inductive gtc : conat -> nat -> Prop :=
| gtc_zero : forall c : conat, gtc (succ c) 0
| gtc_S : forall (c : conat) (n : nat), gtc c n -> gtc (succ c) (Datatypes.S n).

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
      left. constructor.
      right. constructor.
    destruct c as [[| c']].
      left. constructor.
      destruct (IHn' c') as [IH | IH].
        left. constructor. assumption.
        right. constructor. assumption.
Qed.

Lemma Infinite_not_from_nat :
  forall c : conat,
    (forall n : nat, c <> from_nat n) -> Infinite c.
Proof.
  cofix CH.
  intros [[| c']] H.
    specialize (H 0). cbn in H. contradiction H. reflexivity.
    constructor. exists c'.
      cbn. reflexivity.
      apply CH. intros n H'. apply (H (Datatypes.S n)). subst. cbn. reflexivity.
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
  intros [[| c']] H.
    exfalso. apply H. left. constructor.
    constructor. exists c'.
      cbn. reflexivity.
      apply CH. intros [H' | H']; apply H.
        left. constructor. assumption.
        right. constructor. exists c'.
          cbn. reflexivity.
          assumption.
Qed.
(* end hide *)