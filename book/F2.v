(** * F2: Strumienie [TODO] *)

Set Primitive Projections.
(* Set Warnings "+cannot-define-projection".
(* Set Warnings "+non-primitive-record". *) *)

(** W tym rozdziale będą ćwiczenia dotyczące strumieni, czyli ogólnie
    wesołe koinduktywne zabawy, o których jeszcze nic nie napisałem. *)

CoInductive Stream (A : Type) : Type := Cons
{
  hd : A;
  tl : Stream A;
}.

Arguments hd {A}.
Arguments tl {A}.

(** * Bipodobieństwo *)

CoInductive sim {A : Type} (s1 s2 : Stream A) : Prop :=
{
  hds : hd s1 = hd s2;
  tls : sim (tl s1) (tl s2);
}.

Lemma sim_refl :
  forall (A : Type) (s : Stream A),
    sim s s.
(* begin hide *)
Proof.
  cofix CH.
  now constructor.
Qed.
(* end hide *)

Lemma sim_sym :
  forall (A : Type) (s1 s2 : Stream A),
    sim s1 s2 -> sim s2 s1.
(* begin hide *)
Proof.
  cofix CH.
  intros A s1 s2 [hds tls].
  constructor; [easy |].
  now apply CH.
Qed.
(* end hide *)

Lemma sim_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    sim s1 s2 -> sim s2 s3 -> sim s1 s3.
(* begin hide *)
Proof.
  cofix CH.
  intros A s1 s2 s3 [hds1 tls1] [hds2 tls2].
  constructor; [congruence |].
  now apply CH with (tl s2).
Qed.
(* end hide *)

Require Import Setoid.

#[export]
Instance Equiv_sim (A : Type) : Equivalence (@sim A).
(* begin hide *)
Proof.
  split; red.
  - now apply sim_refl.
  - now apply sim_sym.
  - now apply sim_trans.
Defined.
(* end hide *)

(** * [sapp] *)

(** Zdefiniuj funkcję [sapp], która skleja dwa strumienie. Czy taka
    funkcja w ogóle ma sens?*)

CoFixpoint sapp {A : Type} (s1 s2 : Stream A) : Stream A :=
{|
  hd := hd s1;
  tl := sapp (tl s1) s2;
|}.

(* begin hide *)
Ltac coind := cofix CH; constructor; cbn; auto.
(* end hide *)

Lemma sapp_pointless :
  forall (A : Type) (s1 s2 : Stream A),
    sim (sapp s1 s2) s1.
(* begin hide *)
Proof.
  cofix CH.
  now constructor; cbn.
Qed.
(* end hide *)

(** * [lsapp] *)

(** Zdefiniuj funkcję [lsapp], która dokleja listę na początek
    strumienia. *)

(* begin hide *)
Fixpoint lsapp {A : Type} (l : list A) (s : Stream A) : Stream A :=
match l with
| nil => s
| cons h t => {| hd := h; tl := lsapp t s; |}
end.
(* end hide *)

(** * [map] *)

(** Zdefiniuj funkcję [map], która aplikuje funkcję [f : A -> B] do
    każdego elementu strumienia. *)

(* begin hide *)
CoFixpoint map {A B : Type} (f : A -> B) (s : Stream A) : Stream B :=
{|
  hd := f (hd s);
  tl := map f (tl s);
|}.
(* end hide *)

Lemma map_id :
  forall (A : Type) (s : Stream A),
    sim (map (@id A) s) s.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; [easy |].
  now apply CH.
Qed.
(* end hide *)

Lemma map_map :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (s : Stream A),
    sim (map g (map f s)) (map (fun x => g (f x)) s).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; [easy |].
  now apply CH.
Qed.
(* end hide *)

(** * [zipWith] i [unzip] (TODO) *)

(** Zdefiniuj funkcję [zipWith], która ze dwóch strumieni elementów
    [A] oraz [B] robi strumień elementów [C], mając do dyspozycji
    funkcję [f : A -> B -> C ].

    Następnie zdefiniuj funkcję [unzip], która ze strumienia par
    robi parę strumieni wiadomo w jaki sposób.

    Czy [zipWithh pair] i [unzip] są swoimi odwrotnościami? *)

(* begin hide *)
CoFixpoint zipWith
  {A B C : Type} (f : A -> B -> C)
  (s1 : Stream A) (s2 : Stream B) : Stream C :=
{|
  hd := f (hd s1) (hd s2);
  tl := zipWith f (tl s1) (tl s2);
|}.

Definition unzip
  {A B : Type} (s : Stream (A * B)) : Stream A * Stream B :=
    (map fst s, map snd s).

Lemma unzip_zipWith :
  forall {A B : Type} (s : Stream (A * B)),
    sim (zipWith pair (fst (unzip s)) (snd (unzip s))) s.
Proof.
  cofix CH.
  constructor; cbn.
  - now rewrite surjective_pairing.
  - now apply CH.
Qed.

Lemma zipWith_unzip :
  forall {A B : Type} (sa : Stream A) (sb : Stream B),
    let s' := unzip (zipWith pair sa sb) in
      sim (fst s') sa /\ sim (snd s') sb.
Proof.
  split; cbn.
  - revert sa sb.
    cofix CH.
    constructor; cbn; [easy |].
    now apply CH.
  - revert sa sb.
    cofix CH.
    constructor; cbn; [easy |].
    now apply CH.
Qed.

(** TODO: [unzis], cokolwiek to jest *)

(* end hide *)

(** * Inne funkcje (TODO) *)

(** Zdefiniuj resztę przydatnych funkcji podobnych do tych, które są
    dostępne dla list: [repeat], [iterate], [nth], [take], [drop],
    [splitAt], [insert], [replace], [scanl], [scanr], [intersperse],
    [merge].

    Zdefiniuj też funkcje, których zapomniałem (albo nie chciało mi
    się) wymienić. *)

(* begin hide *)
CoFixpoint repeat {A : Type} (x : A) : Stream A :=
{|
  hd := x;
  tl := repeat x;
|}.

CoFixpoint iterate {A : Type} (f : A -> A) (x : A) : Stream A :=
{|
  hd := x;
  tl := iterate f (f x);
|}.

Fixpoint nth (n : nat) {A : Type} (s : Stream A) : A :=
match n with
| 0 => hd s
| S n' => nth n' (tl s)
end.

Fixpoint take (n : nat) {A : Type} (s : Stream A) : list A :=
match n with
| 0 => nil
| S n' => cons (hd s) (take n' (tl s))
end.

Fixpoint drop (n : nat) {A : Type} (s : Stream A) : Stream A :=
match n with
| 0 => s
| S n' => drop n' (tl s)
end.

Fixpoint splitAt
  (n : nat) {A : Type} (s : Stream A) : list A * A * Stream A :=
match n with
| 0 => (nil, hd s, tl s)
| S n' => let '(l, x, s') := splitAt n' (tl s) in (cons (hd s) l, x, s')
end.

CoFixpoint from (n : nat) : Stream nat :=
{|
  hd := n;
  tl := from (S n);
|}.

Fixpoint insert (n : nat) {A : Type} (x : A) (s : Stream A) : Stream A :=
match n with
| 0 => {| hd := x; tl := s; |}
| S n' => {| hd := hd s; tl := insert n' x (tl s); |}
end.

Fixpoint replace (n : nat) {A : Type} (x : A) (s : Stream A) : Stream A :=
match n with
| 0 => {| hd := x; tl := tl s; |}
| S n' => {| hd := hd s; tl := replace n' x (tl s); |}
end.

CoFixpoint diagonal {A : Type} (s : Stream (Stream A)) : Stream A :=
{|
  hd := hd (hd s);
  tl := diagonal (tl (map tl s));
|}.

CoFixpoint scanl
  {A B : Type} (f : A -> B -> A) (x : A) (s : Stream B) : Stream A :=
{|
  hd := f x (hd s);
  tl := scanl f (f x (hd s)) (tl s);
|}.

CoFixpoint scanr
  {A B : Type} (f : A -> B -> B) (x : B) (s : Stream A) : Stream B :=
{|
  hd := f (hd s) x;
  tl := scanr f (f (hd s) x) (tl s);
|}.

CoFixpoint intersperse {A : Type} (x : A) (s : Stream A) : Stream A :=
{|
  hd := hd s;
  tl :=
  {|
    hd := x;
    tl := intersperse x (tl s);
  |};
|}.

CoFixpoint merge {A : Type} (s1 s2 : Stream A) : Stream A :=
{|
  hd := hd s1;
  tl :=
  {|
    hd := hd s2;
    tl := merge (tl s1) (tl s2);
  |};
|}.
(* end hide *)

Lemma merge_repeat :
  forall (A : Type) (x : A) (s : Stream A),
    sim (merge s (repeat x)) (intersperse x s).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; [easy |].
  constructor; cbn; [easy |].
  now apply CH.
Qed.
(* end hide *)

(* TODO: uporządkować *)

Lemma sim_map :
  forall {A B : Type} (f : A -> B) (s1 s2 : Stream A),
    sim s1 s2 -> sim (map f s1) (map f s2).
(* begin hide *)
Proof.
  cofix CH.
  intros * [hds tls].
  constructor; cbn; [now congruence |].
  now apply CH.
Qed.
(* end hide *)

Lemma sim_diagonal :
  forall {A : Type} (s1 s2 : Stream (Stream A)),
    sim s1 s2 -> sim (diagonal s1) (diagonal s2).
(* begin hide *)
Proof.
  cofix CH.
  intros * [hds tls].
  constructor; cbn; [now congruence |].
  now apply CH, sim_map.
Qed.
(* end hide *)

Compute take 10 (diagonal (map from (from 0))).
Compute take 10 (iterate (fun n => S (S n)) 0).

(* TODO *) Lemma diagonal_from :
  forall n : nat,
    sim
      (diagonal (map from (from n)))
      (iterate (fun n => S (S n)) n).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn; [easy |].
Abort.
(* end hide *)

Lemma nth_insert :
  forall {A : Type} (n : nat) (x : A) (s : Stream A),
    nth n (insert n x s) = x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now apply IHn'.
Qed.
(* end hide *)

Lemma nth_replace :
  forall {A : Type} (n : nat) (x : A) (s : Stream A),
    nth n (replace n x s) = x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now apply IHn'.
Qed.
(* end hide *)

Lemma drop_map :
  forall {A B : Type} (f : A -> B) (n : nat) (s : Stream A),
    drop n (map f s) = map f (drop n s).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now apply IHn'.
Qed.
(* end hide *)

(* TODO: take_map dla strumieni *)
(*
Lemma take_map :
  forall {A B : Type} (f : A -> B) (n : nat) (s : Stream A),
    take n (map f s) = D5.map f (take n s).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.
*)

(** * Predykaty i relacje na strumieniach (TODO) *)

(** Zdefiniuj różne użyteczne predykaty i relacje podobne do tych
    listowych, w tym [Elem], [Dup], [NoDup], [Exists], [Forall] i
    wszystkie inne, o których zapomniałem. *)

(* begin hide *)
Inductive Elem {A : Type} (x : A) (s : Stream A) : Prop :=
| Elem_hd : x = hd s -> Elem x s
| Elem_tl : Elem x (tl s) -> Elem x s.
(* end hide *)

#[global] Hint Constructors Elem : core.

(* begin hide *)
Inductive Dup {A : Type} (s : Stream A) : Prop :=
| Dup_hd : Elem (hd s) (tl s) -> Dup s
| Dup_tl : Dup (tl s) -> Dup s.
(* end hide *)

Ltac inv H := inversion H; subst; clear H.

Require Import Arith.

Lemma Elem_nth :
  forall (A : Type) (x : A) (s : Stream A),
    Elem x s <-> exists n : nat, nth n s = x.
(* begin hide *)
Proof.
  split.
  - induction 1; subst.
    + now exists 0; cbn.
    + destruct IHElem as [n p].
      now exists (S n); cbn.
  - intros [n <-]; revert s.
    induction n as [| n']; cbn; intros.
    + now left.
    + now right; apply IHn'.
Qed.
(* end hide *)

Lemma nth_from :
  forall n m : nat,
    nth n (from m) = n + m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now rewrite IHn', <- plus_n_Sm.
Qed.
(* end hide *)

Lemma Elem_from_add :
  forall n m : nat,
    Elem n (from m) ->
      forall k : nat, Elem (k + n) (from m).
(* begin hide *)
Proof.
  intros.
  rewrite Elem_nth in *.
  destruct H as [l H].
  exists (k + l).
  rewrite nth_from in *.
  now rewrite <- Nat.add_assoc, H.
Qed.
(* end hide *)

Require Import Lia.

Lemma Elem_from :
  forall n m : nat,
    Elem n (from m) <-> m <= n.
(* begin hide *)
Proof.
  intros.
  rewrite Elem_nth.
  split.
  - intros [k <-].
    rewrite nth_from.
    now apply le_plus_r.
  - intros H.
    exists (n - m).
    rewrite nth_from.
    now apply Nat.sub_add.
Qed.
(* end hide *)

Lemma Dup_spec :
  forall (A : Type) (s : Stream A),
    Dup s <-> exists n m : nat, n <> m /\ nth n s = nth m s.
(* begin hide *)
Proof.
  split.
  - induction 1.
    + apply Elem_nth in H as [n H].
      now exists 0, (S n); cbn.
    + destruct IHDup as (n & m & IH1 & IH2).
      exists (S n), (S m); cbn.
      now split; [congruence |].
  - intros (n & m & H1 & H2).
    revert s m H1 H2.
    induction n as [| n']; cbn; intros.
    + left; rewrite Elem_nth.
      exists (m - 1).
      rewrite H2.
      destruct m as [| m']; cbn; [contradiction |].
      now rewrite Nat.sub_0_r.
    + destruct m as [| m'].
      * left; rewrite Elem_nth.
        exists n'.
        now rewrite H2; cbn.
      * right.
        now apply (IHn' _ m'); [congruence |].
Qed.
(* end hide *)

Lemma NoDup_from :
  forall n : nat,
    ~ Dup (from n).
(* begin hide *)
Proof.
  intros n H.
  apply Dup_spec in H as (m1 & m2 & H1 & H2).
  rewrite 2!nth_from, Nat.add_cancel_r in H2.
  contradiction.
Qed.
(* end hide *)

(* begin hide *)
Inductive Exists {A : Type} (P : A -> Prop) (s : Stream A) : Prop :=
| Exists_hd : P (hd s) -> Exists P s
| Exists_tl : Exists P (tl s) -> Exists P s.
(* end hide *)

Lemma Exists_spec :
  forall (A : Type) (P : A -> Prop) (s : Stream A),
    Exists P s <-> exists n : nat, P (nth n s).
(* begin hide *)
Proof.
  split.
  - induction 1 as [| s H [n IH]].
    + now exists 0; cbn.
    + now exists (S n).
  - intros [n H]; revert s H.
    induction n as [| n']; cbn; intros.
    + now left.
    + now right; apply IHn'.
Qed.
(* end hide *)

(* begin hide *)
CoInductive Forall {A : Type} (s : Stream A) (P : A -> Prop) : Prop :=
{
  Forall_hd : P (hd s);
  Forall_tl : Forall (tl s) P;
}.
(* end hide *)

Lemma Forall_spec :
  forall (A : Type) (s : Stream A) (P : A -> Prop),
    Forall s P <-> forall n : nat, P (nth n s).
(* begin hide *)
Proof.
  split; intros; revert s H.
  - induction n as [| n']; cbn; intros.
    + now apply Forall_hd.
    + now apply IHn', Forall_tl.
  - cofix CH.
    constructor.
    + now apply (H 0).
    + apply CH; intros n.
      now apply (H (S n)).
Qed.
(* end hide *)

Lemma Forall_spec' :
  forall (A : Type) (s : Stream A) (P : A -> Prop),
    Forall s P <-> forall x : A, Elem x s -> P x.
(* begin hide *)
Proof.
  intros A s P.
  setoid_rewrite Elem_nth.
  split.
  - intros HF x [n <-].
    now apply Forall_spec.
  - intros H.
    apply Forall_spec; intros n.
    apply H.
    now exists n.
Qed.
(* end hide *)

Lemma Forall_Exists :
  forall (A : Type) (P : A -> Prop) (s : Stream A),
    Forall s P -> Exists P s.
(* begin hide *)
Proof.
  constructor.
  now apply Forall_hd.
Qed.
(* end hide *)

(* begin hide *)
(* #[projections(primitive = no)] *)
Variant SubstreamF {A : Type} (F : Stream A -> Stream A -> Prop) (s1 s2 : Stream A) : Prop :=
| MkSubstreamF :
    forall n : nat, hd s1 = nth n s2 -> F (tl s1) (drop (S n) s2) -> SubstreamF F s1 s2.
{
  pos : nat;
  nth_pos_hd : hd s1 = nth pos s2;
  SubstreamT' : F (tl s1) (drop (S pos) s2);
}.

CoInductive Substream {A : Type} (s1 s2 : Stream A) : Prop :=
{
  Substream_out : SubstreamT Substream s1 s2;
}.

CoInductive SubstreamT {A : Type} (s1 s2 : Stream A) : Type :=
{
  pos : nat;
  nth_pos_hd : hd s1 = nth pos s2;
  SubstreamT' : SubstreamT (tl s1) (drop (S pos) s2);
}.

Definition Substream {A : Type} (s1 s2 : Stream A) : Prop :=
  inhabited (SubstreamT s1 s2).
(* end hide *)

Lemma drop_tl :
  forall (A : Type) (n : nat) (s : Stream A),
    drop n (tl s) = drop (S n) s.
(* begin hide *)
Proof.
  reflexivity.
Qed.
(* end hide *)

Lemma hd_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    hd (drop n s) = nth n s.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now apply IHn'.
Qed.
(* end hide *)

Lemma tl_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    tl (drop n s) = drop n (tl s).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now apply IHn'.
Qed.
(* end hide *)

Lemma nth_drop :
  forall (A : Type) (n m : nat) (s : Stream A),
    nth n (drop m s) = nth (n + m) s.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
  - now apply hd_drop.
  - now rewrite tl_drop, IHn'.
Qed.
(* end hide *)

Lemma drop_drop :
  forall (A : Type) (n m : nat) (s : Stream A),
    drop m (drop n s) = drop (n + m) s.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now apply IHn'.
Qed.
(* end hide *)

Lemma Substream_tl :
  forall (A : Type) (s1 s2 : Stream A),
    Substream s1 s2 -> Substream (tl s1) (tl s2).
(* begin hide *)
Proof.
  intros A s1 s2 [[n p [m q H]]].
  rewrite nth_drop, <- plus_n_Sm in q.
  constructor; econstructor; [now apply q |].
  now rewrite drop_drop, <- plus_n_Sm, plus_Sn_m, Nat.add_comm in H.
Qed.
(* end hide *)

Lemma Substream_tl_l :
  forall (A : Type) (s1 s2 : Stream A),
    Substream s1 s2 -> Substream (tl s1) s2.
(* begin hide *)
Proof.
  intros A s1 s2 [[n p [m q H]]].
  constructor; econstructor.
  - now rewrite q, nth_drop.
  - now rewrite drop_drop, Nat.add_comm, plus_Sn_m in H.
Qed.
(* end hide *)

Lemma Substream_drop :
  forall (A : Type) (n : nat) (s1 s2 : Stream A),
    Substream s1 s2 -> Substream (drop n s1) (drop n s2).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now apply IHn', Substream_tl.
Qed.
(* end hide *)

Lemma Substream_drop_l :
  forall (A : Type) (n : nat) (s1 s2 : Stream A),
    Substream s1 s2 -> Substream (drop n s1) s2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now apply IHn', Substream_tl_l.
Qed.
(* end hide *)

Lemma Substream_refl :
  forall (A : Type) (s : Stream A),
    Substream s s.
(* begin hide *)
Proof.
  constructor; revert s.
  cofix CH.
  econstructor 1 with (pos := 0); cbn; [easy |].
  now apply CH.
Qed.
(* end hide *)

Lemma Substream_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    Substream s1 s2 -> Substream s2 s3 -> Substream s1 s3.
(* begin hide *)
Proof.
  intros A s1 s2 s3 [H12] H23; constructor; revert s1 s2 s3 H12 H23.
  cofix CH.
  intros s1 s2 s3 [n1 p1 H12'] H23.
  destruct (Substream_drop _ n1 _ _ H23) as [n2 p2 H2].
  econstructor 1 with (n := n1 + n2); cbn.
  - now rewrite Nat.add_comm, <- nth_drop, <- p2, hd_drop.
  - apply CH with (tl (drop n1 s2)).
    + now rewrite tl_drop.
    + now rewrite drop_tl, plus_n_Sm, <- drop_drop.
Qed.
(* end hide *)

Lemma Substream_not_antisymm :
  exists (A : Type) (s1 s2 : Stream A),
    Substream s1 s2 /\ Substream s2 s1 /\ ~ sim s1 s2.
(* begin hide *)
Proof.
  exists bool, (iterate negb true), (iterate negb false).
  repeat split.
  - econstructor 1 with (n := 1); cbn; [easy |].
    now apply Substream_refl.
  - econstructor 1 with (n := 1); cbn; [easy |].
    now apply Substream_refl.
  - intros [[=] tls].
Qed.
(* end hide *)

(* begin hide *)
Inductive Suffix {A : Type} : Stream A -> Stream A -> Prop :=
| Suffix_refl :
    forall s : Stream A, Suffix s s
| Suffix_tl :
    forall s1 s2 : Stream A,
      Suffix (tl s1) s2 -> Suffix s1 s2.
(* end hide *)

Fixpoint snoc {A : Type} (x : A) (l : list A) : list A :=
match l with
| nil => cons x nil
| cons h t => cons h (snoc x t)
end.

Lemma Suffix_spec :
  forall (A : Type) (s1 s2 : Stream A),
    Suffix s1 s2 <-> exists n : nat, s2 = drop n s1.
(* begin hide *)
Proof.
  split.
  - induction 1 as [| s1 s2 H [n IH]].
    + now exists 0.
    + now exists (S n).
  - intros [n ->]; revert s1.
    induction n as [| n']; cbn; intros.
    + now left.
    + now right; apply IHn'.
Qed.
(* end hide *)

(* begin hide *)
Definition Incl {A : Type} (s1 s2 : Stream A) : Prop :=
  forall x : A, Elem x s1 -> Elem x s2.

Definition SetEquiv {A : Type} (s1 s2 : Stream A) : Prop :=
  Incl s1 s2 /\ Incl s2 s1.
(* end hide *)

Lemma sim_Elem :
  forall (A : Type) (x : A) (s1 s2 : Stream A),
    sim s1 s2 -> Elem x s1 -> Elem x s2.
(* begin hide *)
Proof.
  intros A x s1 s2 Hs Hel1; revert s2 Hs.
  induction Hel1; intros s2 [hds tls].
  - now left; congruence.
  - now right; apply IHHel1.
Qed.
(* end hide *)

Lemma sim_Incl :
  forall (A : Type) (s1 s1' s2 s2' : Stream A),
    sim s1 s1' -> sim s2 s2' -> Incl s1 s2 -> Incl s1' s2'.
(* begin hide *)
Proof.
  unfold Incl.
  intros A s1 s1' s2 s2' Hs1 Hs2 Hincl x Hel.
  eapply sim_Elem; [now apply Hs2 |].
  apply Hincl.
  eapply sim_Elem; [| now eassumption].
  now apply sim_sym, Hs1.
Qed.
(* end hide *)

Lemma sim_SetEquiv :
  forall (A : Type) (s1 s1' s2 s2' : Stream A),
    sim s1 s1' -> sim s2 s2' -> SetEquiv s1 s2 -> SetEquiv s1' s2'.
(* begin hide *)
Proof.
  unfold SetEquiv.
  now split; eapply sim_Incl; firstorder eauto.
Qed.
(* end hide *)

Definition scons {A : Type} (x : A) (s : Stream A) : Stream A :=
{|
  hd := x;
  tl := s;
|}.

(** * Permutacje strumieni *)

(** Zdefiniuj relację [SPermutation], która jest analogiczna do
    relacji [Permutation], którą znasz z list. Udowodnij jej
    specyfikację. *)

(* begin hide *)
Inductive SPermutation {A : Type} : Stream A -> Stream A -> Prop :=
| SPerm_refl :
    forall s : Stream A, SPermutation s s
| SPerm_skip :
    forall (x : A) (s1 s2 : Stream A),
      SPermutation s1 s2 -> SPermutation (scons x s1) (scons x s2)
| SPerm_swap :
    forall (x y : A) (s1 s2 : Stream A),
      SPermutation s1 s2 ->
        SPermutation (scons x (scons y s1)) (scons y (scons x s2))
| SPerm_trans :
    forall s1 s2 s3 : Stream A,
      SPermutation s1 s2 -> SPermutation s2 s3 -> SPermutation s1 s3.

#[global] Hint Constructors SPermutation : core.
(* end hide *)

(* TODO *) Require Import Permutation.

Lemma lsapp_scons :
  forall (A : Type) (l : list A) (x : A) (s : Stream A),
    lsapp l (scons x s) = lsapp (snoc x l) s.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma SPermutation_Permutation_lsapp :
  forall (A : Type) (l1 l2 : list A) (s1 s2 : Stream A),
    Permutation l1 l2 -> SPermutation s1 s2 ->
      SPermutation (lsapp l1 s1) (lsapp l2 s2).
(* begin hide *)
Proof.
  intros until 2. revert s1 s2 H0.
  induction H; intros; cbn; eauto.
  constructor. induction l as [| h t]; cbn.
    assumption.
    constructor. apply IHt.
Qed.
(* end hide *)

Lemma take_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    sim s (lsapp (take n s) (drop n s)).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [now apply sim_refl |].
  constructor; cbn; [easy |].
  now apply IHn'.
Qed.
(* end hide *)

Lemma take_add :
  forall (A : Type) (n m : nat) (s : Stream A),
    take (n + m) s = List.app (take n s) (take m (drop n s)).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now rewrite IHn'.
Qed.
(* end hide *)

Lemma SPermutation_spec :
  forall (A : Type) (s1 s2 : Stream A),
    SPermutation s1 s2 <->
    exists n : nat,
      Permutation (take n s1) (take n s2) /\
      drop n s1 = drop n s2.
(* begin hide *)
Proof.
  split.
    - induction 1 as
    [
    | x s1 s2 H (n & IH1 & IH2)
    | x y s1 s2 H (n & IH1 & IH2)
    | s1 s2 s3 H1 (n1 & IH11 & IH12) H2 (n2 & IH21 & IH22)
    ]; cbn.
      + now exists 0; cbn.
      + now exists (S n); cbn; auto.
      + exists (S (S n)); cbn.
        split; [| easy].
        now rewrite perm_swap, IH1.
      + exists (n1 + n2).
        split; cycle 1.
        * now rewrite <- drop_drop, IH12, Nat.add_comm, <- drop_drop, <- IH22, !drop_drop,
            Nat.add_comm.
        * replace (take (n1 + n2) s3) with (take (n2 + n1) s3) by now rewrite Nat.add_comm.
          now rewrite 2!take_add, IH11, IH12, <- IH22, <- IH21, <- 2!take_add, Nat.add_comm.
    - intros (n & H1 & H2). admit.
Admitted.
(*
      + rewrite (take_drop _ n s1), (take_drop _ n s2), H2.
      + apply SPermutation_Permutation_lsapp.
        * assumption.
        * apply SPerm_refl.
Qed.
*)
(* end hide *)

(** * Permutacje strumieni v2 *)

(** Poprzedni podrozdział jest trochę lipny, bo tamtejsza definicja nie uchwytuje wszystkich możliwych
    permutacji strumieni - wymusza ona, żeby każda permutacja składa się z jedynie skończonej liczby
    przestawień. *)

CoFixpoint swap {A : Type} (s : Stream A) : Stream A :=
{|
  hd := hd (tl s);
  tl :=
  {|
    hd := hd s;
    tl := swap (tl (tl s));
  |}
|}.

(** Widać, że dla strumienia pokroju [s = cocons 0 (cocons 1 (cocons 2 ...))] zdanie
    [SPermutation s (swap s)] nie zachodzi, bo przestawienia elementów ciągną się w
    nieskończoność.

    Potrzebna jest nam zatem jakaś lepsza definicja permutacji. *)

Lemma SPermutation_not_swap :
  forall {A : Type} (s : Stream A),
    SPermutation s (swap s) -> sim s (swap s).
(* begin hide *)
Proof.
  intros A s1 H.
  remember (swap s1) as s2.
  revert Heqs2.
  induction H; intros.
    apply sim_refl.
Admitted.
(* end hide *)

(** * Strumienie za pomocą przybliżeń (TODO) *)

Require Import Program.Equality.

Module approx.

Inductive Vec (A : Type) : nat -> Type :=
| vnil : Vec A 0
| vcons : forall n : nat, A -> Vec A n -> Vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} {n}.

Definition vhd {A : Type} {n : nat} (v : Vec A (S n)) : A :=
match v with
| vcons h _ => h
end.

Definition vtl {A : Type} {n : nat} (v : Vec A (S n)) : Vec A n :=
match v with
| vcons _ t => t
end.

Lemma vhd_vtl :
  forall (A : Type) (n : nat) (v : Vec A (S n)),
    v = vcons (vhd v) (vtl v).
(* begin hide *)
Proof.
  dependent destruction v. cbn. reflexivity.
Qed.
(* end hide *)

Fixpoint vtake {A : Type} (s : Stream A) (n : nat) : Vec A n :=
match n with
| 0 => vnil
| S n' => vcons (hd s) (vtake (tl s) n')
end.

Fixpoint vtake' {A : Type} (s : Stream A) (n : nat) : Vec A (S n) :=
match n with
| 0 => vcons (hd s) vnil
| S n' => vcons (hd s) (vtake' (tl s) n')
end.

CoFixpoint unvtake {A : Type} (f : forall n : nat, Vec A (S n)) : Stream A :=
{|
  hd := vhd (f 0);
  tl := unvtake (fun n : nat => vtl (f (S n)))
|}.

Fixpoint vnth {A : Type} {n : nat} (v : Vec A n) (k : nat) : option A :=
match v, k with
| vnil, _ => None
| vcons h t, 0 => Some h
| vcons h t, S k' => vnth t k'
end.

Ltac depdestr x :=
  let x' := fresh "x" in remember x as x'; dependent destruction x'.

Lemma unvtake_vtake' :
  forall (A : Type) (n : nat) (f : forall n : nat, Vec A (S n)),
    (forall m1 m2 k : nat, k <= m1 -> k <= m2 ->
      vnth (f m1) k = vnth (f m2) k) ->
       vtake' (unvtake f) n = f n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    remember (f 0) as v. dependent destruction v. cbn. f_equal.
      dependent destruction v. reflexivity.
    rewrite IHn'.
      rewrite vhd_vtl. f_equal.
        specialize (H 0 (S n') 0 ltac:(auto) ltac:(apply le_0_n)).
        depdestr (f 0). depdestr (f (S n')). cbn in *.
        inversion H. reflexivity.
      intros. specialize (H (S m1) (S m2) (S k)).
        depdestr (f (S m1)). depdestr (f (S m2)). cbn in *.
        apply H; apply le_n_S; assumption.
Qed.
(* end hide *)

Lemma vtake_unvtake :
  forall (A : Type) (s : Stream A),
    sim (unvtake (vtake' s)) s.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply CH.
Qed.
(* end hide *)

End approx.

(** * Pomysł dawno zapomniany: (ko)induktywne specyfikacje funkcji (TODO) *)

Inductive Filter {A : Type} (f : A -> bool) : Stream A -> Stream A -> Prop :=
| Filter_true :
    forall s r r' : Stream A,
      f (hd s) = true -> Filter f (tl s) r ->
        hd r' = hd s -> tl r' = r -> Filter f s r'
| Filter_false :
    forall s r : Stream A,
      f (hd s) = false -> Filter f (tl s) r -> Filter f s r.

Lemma Filter_bad :
  forall (A : Type) (f : A -> bool) (s r : Stream A),
    Filter f s r -> (forall x : A, f x = false) -> False.
(* begin hide *)
Proof.
  induction 1; intros.
    specialize (H3 (hd s)). congruence.
    apply IHFilter. assumption.
Qed.
(* end hide *)

CoInductive Filter' {A : Type} (f : A -> bool) (s r : Stream A) : Prop :=
{
  Filter'_true :
    f (hd s) = true -> hd s = hd r /\ Filter' f (tl s) (tl r);
  Filter'_false :
    f (hd s) = false -> Filter' f (tl s) r;
}.

Lemma Filter'_const_false :
  forall (A : Type) (s r : Stream A),
    Filter' (fun _ => false) s r.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
    inversion 1.
    intros _. apply CH.
Qed.
(* end hide *)

Lemma Filter'_const_true :
  forall (A : Type) (s r : Stream A),
    Filter' (fun _ => true) s r -> sim s r.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
    destruct H. firstorder.
    apply CH. destruct H. firstorder.
Qed.
(* end hide *)

(* begin hide *)

Lemma Stream_coiter :
  forall (A X : Type),
    (X -> A) -> (X -> X) -> X -> Stream A.
Proof.
  cofix CH.
  constructor.
    apply X0, X2.
    apply (CH _ _ X0 X1 (X1 X2)).
Defined.

Definition from' : nat -> Stream nat.
Proof.
  apply Stream_coiter.
    exact (fun n => n).
    exact S.
Defined.

Definition Stream' (A : Type) : Type :=
  {X : Type & X * (X -> A) * (X -> X)}%type.

Lemma Stream'_Stream {A : Type} (s : Stream' A) : Stream A.
Proof.
(*  cofix CH.*)
  destruct s as [X [[x hd] tl]].
  apply (Stream_coiter A X).
    exact hd.
    exact tl.
    exact x.
Defined.

Definition Stream_Stream' {A : Type} (s : Stream A) : Stream' A.
Proof.
  red. exists (Stream A). exact ((s, hd), tl).
Defined.

Lemma Streams :
  forall (A : Type) (s : Stream A),
    sim (Stream'_Stream (Stream_Stream' s)) s.
Proof.
  cofix CH.
  constructor.
    cbn. reflexivity.
    cbn. apply CH.
Qed.

Lemma Streams' :
  forall (A : Type) (s : Stream' A),
    Stream_Stream' (Stream'_Stream s) = s.
Proof.
  destruct s as [X [[x hd] tl]]. cbn.
  unfold Stream_Stream'.
Abort.

(* end hide *)

(** * Bijekcja między [Stream unit] i [unit] (TODO) *)

Require Import FinFun ZArith.

CoFixpoint theChosenOne : Stream unit :=
{|
  hd := tt;
  tl := theChosenOne;
|}.

Lemma all_chosen_unit_aux :
  forall s : Stream unit,
    sim s theChosenOne.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
    destruct (hd s). cbn. reflexivity.
    cbn. apply CH.
Qed.
(* end hide *)

Lemma all_chosen_unit :
  forall x y : Stream unit,
    sim x y.
(* begin hide *)
Proof.
  intros.
  rewrite (all_chosen_unit_aux x), (all_chosen_unit_aux y).
  reflexivity.
Qed.
(* end hide *)

Axiom sim_eq :
  forall (A : Type) (x y : Stream A), sim x y -> x = y.

Theorem all_eq :
  forall x y : Stream unit,
    x = y.
(* begin hide *)
Proof.
  intros; apply sim_eq, all_chosen_unit.
Qed.
(* end hide *)

Definition unit_to_stream (u : unit) : Stream unit := theChosenOne.
Definition stream_to_unit (s : Stream unit) : unit := tt.

Lemma unit_is_Stream_unit :
  Bijective unit_to_stream.
(* begin hide *)
Proof.
  red. exists stream_to_unit.
  split; intros.
    destruct x; trivial.
    apply all_eq.
Qed.
(* end hide *)

(** * Trochę losowości (TODO) *)

CoFixpoint rand (seed n1 n2 : Z) : Stream Z :=
{|
  hd := Zmod seed n2;
  tl := rand (Zmod seed n2 * n1) n1 n2;
|}.

CoFixpoint rand' (seed n1 n2 : Z) : Stream Z :=
{|
  hd := Zmod seed n2;
  tl := rand' (Zmod (seed * n1) n2) n1 n2;
|}.