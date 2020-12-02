(** * F3: Strumienie [TODO] *)

(** W tym rozdziale będą ćwiczenia dotyczące strumieni, czyli ogólnie
    wesołe koinduktywne zabawy, o których jeszcze nic nie napisałem. *)

CoInductive Stream (A : Type) : Type :=
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
  forall (A : Type) (s : Stream A), sim s s.
(* begin hide *)
Proof.
  cofix CH. constructor; auto.
Qed.
(* end hide *)

Lemma sim_sym :
  forall (A : Type) (s1 s2 : Stream A),
    sim s1 s2 -> sim s2 s1.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [hds tls]. constructor; auto.
Qed.
(* end hide *)

Lemma sim_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    sim s1 s2 -> sim s2 s3 -> sim s1 s3.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [hds1 tls1], 1 as [hds2 tls2].
  constructor; eauto. rewrite hds1. assumption.
Qed.
(* end hide *)

(** * [sapp] *)

(** Zdefiniuj funkcję [sapp], która skleja dwa strumienie. Czy taka
    funkcja w ogóle ma sens?

    Zdefiniuj funkcję [lsapp], która dokleja listę na początek
    strumienia. *)

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
  coind.
Qed.
(* end hide *)

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
  forall (A : Type) (s : Stream A), sim (map (@id A) s) s.
(* begin hide *)
Proof.
  coind.
Qed.
(* end hide *)

Lemma map_map :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (s : Stream A),
    sim (map g (map f s)) (map (fun x => g (f x)) s).
(* begin hide *)
Proof.
  coind.
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
    sim
      (zipWith pair (fst (unzip s)) (snd (unzip s)))
      s.
Proof.
  cofix CH.
  constructor; cbn.
    destruct s as [[ha hb] s']; cbn. reflexivity.
    apply CH.
Qed.

(* TODO *) Lemma zipWith_unzip :
  forall {A B : Type} (sa : Stream A) (sb : Stream B),
    let s' := unzip (zipWith pair sa sb) in
      sim (fst s') sa /\ sim (snd s') sb.
Proof.
  split; cbn.
    revert sa sb. cofix CH. intros. constructor; cbn.
      reflexivity.
      apply CH.
    revert sa sb. cofix CH. intros. constructor; cbn.
      reflexivity.
      apply CH.
Qed.

(** TODO: unzis, cokolwiek to jest *)

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
    | S n' =>
        let '(l, x, s') := splitAt n' (tl s) in (cons (hd s) l, x, s')
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
  constructor; cbn.
    reflexivity.
    constructor; cbn.
      reflexivity.
      apply CH.
Qed.

(* TODO: uporządkować *)

Lemma sim_map :
  forall {A B : Type} (f : A -> B) (s1 s2 : Stream A),
    sim s1 s2 -> sim (map f s1) (map f s2).
Proof.
  cofix CH.
  constructor; destruct H; cbn.
    f_equal. assumption.
    apply CH. assumption.
Qed.

Require Import Setoid.

Lemma sim_diagonal :
  forall {A : Type} (s1 s2 : Stream (Stream A)),
    sim s1 s2 -> sim (diagonal s1) (diagonal s2).
Proof.
  cofix CH.
  constructor; destruct H; cbn.
    f_equal. assumption.
    apply CH. apply sim_map. assumption.
Qed.

Compute take 10 (diagonal (map from (from 0))).
Compute take 10 (iterate (fun n => S (S n)) 0).

(* TODO *) Lemma diagonal_from :
  forall n : nat,
    sim
      (diagonal (map from (from n)))
      (iterate (fun n => S (S n)) n).
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    eapply sim_trans.
Abort.

Lemma nth_insert :
  forall {A : Type} (n : nat) (x : A) (s : Stream A),
    nth n (insert n x s) = x.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    apply IHn'.
Qed.

Lemma nth_replace :
  forall {A : Type} (n : nat) (x : A) (s : Stream A),
    nth n (replace n x s) = x.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    apply IHn'.
Qed.

Lemma drop_map :
  forall {A B : Type} (f : A -> B) (n : nat) (s : Stream A),
    drop n (map f s) = map f (drop n s).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

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

(* end hide *)

(** * Predykaty i relacje na strumieniach (TODO) *)

(** Zdefiniuj różne użyteczne predykaty i relacje podobne do tych
    listowych, w tym [Elem], [Dup], [NoDup], [Exists], [Forall] i
    wszystkie inne, o których zapomniałem. *)

(* begin hide *)
Inductive Elem {A : Type} (x : A) (s : Stream A) : Prop :=
    | Elem_hd : x = hd s -> Elem x s
    | Elem_tl : Elem x (tl s) -> Elem x s.
(* end hide *)

Hint Constructors Elem.

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
    induction 1; subst.
      exists 0. cbn. reflexivity.
      destruct IHElem as [n p]. exists (S n). cbn. assumption.
    intros [n p]. rewrite <- p. clear p. revert s.
      induction n as [| n']; cbn.
        left. reflexivity.
        right. apply IHn'.
Qed.
(* end hide *)

Lemma nth_from :
  forall n m : nat,
    nth n (from m) = n + m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    specialize (IHn' (S m)). rewrite <- plus_n_Sm in IHn'. assumption.
Qed.
(* end hide *)

Lemma Elem_from_add :
  forall n m : nat, Elem n (from m) ->
    forall k : nat, Elem (k + n) (from m).
(* begin hide *)
Proof.
  intros.
  rewrite Elem_nth in *.
  destruct H as [l H].
  exists (k + l). revert m l n H. induction k as [| k']; intros.
    cbn. assumption.
    rewrite Nat.add_succ_comm. rewrite (IHk' _ _ (S n)).
      rewrite <- plus_n_Sm. cbn. reflexivity.
      rewrite nth_from in *. cbn. f_equal. assumption.
Qed.
(* end hide *)

Lemma Elem_from :
  forall n m : nat, Elem n (from m) <-> m <= n.
(* begin hide *)
Proof.
  split.
    remember (from m) as s. intro H. revert m Heqs.
      induction H; intros; subst; cbn in *.
        apply le_n.
        apply Nat.le_trans with (S m).
          apply le_S, le_n.
          apply IHElem. reflexivity.
    induction 1.
      constructor. cbn. reflexivity.
      rewrite Elem_nth in *. destruct IHle as [n IH].
        exists (S n). rewrite nth_from in *. cbn.  f_equal. assumption.
Qed.
(* end hide *)

Lemma Dup_spec :
  forall (A : Type) (s : Stream A),
    Dup s <-> exists n m : nat, n <> m /\ nth n s = nth m s.
(* begin hide *)
Proof.
  split.
    induction 1.
      rewrite Elem_nth in H. destruct H as [n H]. exists 0, (S n). split.
        inversion 1.
        cbn. rewrite H. reflexivity.
      destruct IHDup as [n [m [IH1 IH2]]]. exists (S n), (S m). split.
        inversion 1. contradiction.
        cbn. assumption.
    intros (n & m & H1 & H2). revert m H1 H2.
      revert s. induction n as [| n']; cbn; intros.
        left. rewrite Elem_nth. exists (m - 1). rewrite H2.
          destruct m as [| m']; cbn.
            contradiction.
            rewrite Nat.sub_0_r. reflexivity.
        destruct m as [| m'].
          left. rewrite Elem_nth. exists n'. rewrite H2. cbn. reflexivity.
          right. apply (IHn' _ m').
            intro. apply H1. f_equal. assumption.
            cbn in H2. assumption.
Qed.
(* end hide *)

Lemma NoDup_from :
  forall n : nat, ~ Dup (from n).
(* begin hide *)
Proof.
  intros n H. rewrite Dup_spec in H.
  destruct H as (m1 & m2 & H1 & H2).
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
    induction 1 as [| s H [n IH]].
      exists 0. cbn. assumption.
      exists (S n). cbn. assumption.
    intros [n H]. revert s H. induction n as [| n']; intros; cbn in *.
      left. assumption.
      right. apply IHn'. assumption.
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
  split; intros.
    revert s H. induction n as [| n']; cbn; intros.
      inv H. assumption.
      apply IHn'. inv H. assumption.
    revert s H. cofix CH. constructor.
      apply (H 0).
      apply CH. intro. specialize (H (S n)). cbn in H. assumption.
Qed.
(* end hide *)

Lemma Forall_spec' :
  forall (A : Type) (s : Stream A) (P : A -> Prop),
    Forall s P <-> forall x : A, Elem x s -> P x.
(* begin hide *)
Proof.
  split.
    Focus 2. revert s. cofix CH. constructor.
      apply H. constructor. reflexivity.
      apply CH. intros. apply H. right. assumption.
    intros H1 x H2. revert H1. induction H2; destruct 1; subst.
      assumption.
      apply IHElem. assumption.
Qed.
(* end hide *)

Lemma Forall_Exists :
  forall (A : Type) (P : A -> Prop) (s : Stream A),
    Forall s P -> Exists P s.
(* begin hide *)
Proof.
  constructor. destruct H. assumption.
Qed.
(* end hide *)

(* begin hide *)
CoInductive Substream {A : Type} (s1 s2 : Stream A) : Prop :=
{
    n : nat;
    p : hd s1 = nth n s2;
    Substream' : Substream (tl s1) (drop (S n) s2);
}.
(* end hide *)

Lemma drop_tl :
  forall (A : Type) (n : nat) (s : Stream A),
    drop n (tl s) = drop (S n) s.
(* begin hide *)
Proof.
  reflexivity.
Qed.
(* end hide *)

Lemma tl_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    tl (drop n s) = drop n (tl s).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    apply IHn'.
Qed.
(* end hide *)

Lemma nth_drop :
  forall (A : Type) (n m : nat) (s : Stream A),
    nth n (drop m s) = nth (n + m) s.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    revert s. induction m as [| m']; cbn; intros.
      reflexivity.
      apply IHm'.
    rewrite <- IHn'. cbn. rewrite tl_drop. reflexivity.
Qed.
(* end hide *)

Lemma drop_drop :
  forall (A : Type) (n m : nat) (s : Stream A),
    drop m (drop n s) = drop (n + m) s.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    apply IHn'.
Qed.
(* end hide *)

Lemma Substream_tl :
  forall (A : Type) (s1 s2 : Stream A),
    Substream s1 s2 -> Substream (tl s1) (tl s2).
(* begin hide *)
Proof.
  destruct 1 as [n p [m q H]]. econstructor.
    rewrite q, nth_drop, <- plus_n_Sm. cbn. reflexivity.
    rewrite drop_drop in H. cbn in H. rewrite Nat.add_comm in H.
      cbn in *. assumption.
Qed.
(* end hide *)

Lemma Substream_drop :
  forall (A : Type) (n : nat) (s1 s2 : Stream A),
    Substream s1 s2 -> Substream (drop n s1) (drop n s2).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    apply IHn', Substream_tl, H.
Qed.
(* end hide *)

Lemma hd_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    hd (drop n s) = nth n s.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    apply IHn'.
Qed.
(* end hide *)

Lemma Substream_drop_add :
  forall (A : Type) (n m : nat) (s1 s2 : Stream A),
    Substream s1 (drop n s2) -> Substream s1 (drop (n + m) s2).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
Abort.

Lemma Substream_refl :
  forall (A : Type) (s : Stream A), Substream s s.
(* begin hide *)
Proof.
  cofix CH.
  intros. econstructor.
    instantiate (1 := 0). cbn. reflexivity.
    apply CH.
Qed.
(* end hide *)

Lemma Substream_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    Substream s1 s2 -> Substream s2 s3 -> Substream s1 s3.
(* begin hide *)
Proof.
  cofix CH.
  intros A s1 s2 s3 [n1 p1 H1] H.
  destruct (Substream_drop _ n1 _ _ H) as [n2 p2 H2].
  econstructor.
    rewrite hd_drop in p2. rewrite p1, p2, nth_drop, Nat.add_comm.
      reflexivity.
    cbn. apply CH with (tl (drop n1 s2)).
      rewrite tl_drop. cbn in H1. assumption.
      rewrite drop_drop, <- plus_n_Sm in H2. cbn in H2. assumption.
Qed.
(* end hide *)

Lemma Substream_not_antisymm :
  exists (A : Type) (s1 s2 : Stream A),
    Substream s1 s2 /\ Substream s2 s1 /\ ~ sim s1 s2.
(* begin hide *)
Proof.
  exists bool, (iterate negb true), (iterate negb false).
  repeat split.
    econstructor.
      instantiate (1 := 1). cbn. reflexivity.
      cbn. apply Substream_refl.
    econstructor.
      instantiate (1 := 1). cbn. reflexivity.
      cbn. apply Substream_refl.
    destruct 1. cbn in *. inversion hds0.
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
    Suffix s1 s2 <-> exists l : list A, s1 = lsapp l s2.
(* begin hide *)
Proof.
  split.
    induction 1 as [| s1 s2 H [l IH]].
      exists nil. cbn. reflexivity.
      exists (cons (hd s1) l). cbn. rewrite <- IH.
        destruct s1. cbn. reflexivity.
    intros [l H]. revert s1 s2 H. induction l as [| h t]; cbn; intros.
      subst. constructor.
      right. apply IHt. rewrite H. cbn. reflexivity.
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
  intros until 2. revert s2 H. induction H0; intros.
    left. inv H0. assumption.
    right. apply IHElem. inv H. assumption.
Qed.
(* end hide *)

Lemma sim_Incl :
  forall (A : Type) (s1 s1' s2 s2' : Stream A),
    sim s1 s1' -> sim s2 s2' -> Incl s1 s2 -> Incl s1' s2'.
(* begin hide *)
Proof.
  unfold Incl. intros A s1 s1' s2 s2' H1 H2 H x H'.
  eapply sim_Elem; eauto. apply H.
  eapply sim_Elem; eauto. apply sim_sym. assumption.
Qed.
(* end hide *)

Lemma sim_SetEquiv :
  forall (A : Type) (s1 s1' s2 s2' : Stream A),
    sim s1 s1' -> sim s2 s2' -> SetEquiv s1 s2 -> SetEquiv s1' s2'.
(* begin hide *)
Proof.
  unfold SetEquiv. destruct 3; split; eapply sim_Incl; eauto.
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

Hint Constructors SPermutation.
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
    s = lsapp (take n s) (drop n s).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite <- IHn'. destruct s; reflexivity.
Qed.
(* end hide *)

Lemma take_add :
  forall (A : Type) (n m : nat) (s : Stream A),
    take (n + m) s = List.app (take n s) (take m (drop n s)).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
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
    induction 1 as
    [
    | x s1 s2 H (n & IH1 & IH2)
    | x y s1 s2 H (n & IH1 & IH2)
    | s1 s2 s3 H1 (n1 & IH11 & IH12) H2 (n2 & IH21 & IH22)
    ]; cbn.
      exists 0. cbn. split; auto.
      exists (S n). cbn. auto.
      exists (S (S n)). cbn. split.
        rewrite perm_swap, IH1. reflexivity.
        assumption.
      exists (n1 + n2).
        assert (drop (n1 + n2) s1 = drop (n1 + n2) s3).
          apply (@f_equal _ _ (drop n2)) in IH12.
          apply (@f_equal _ _ (drop n1)) in IH22.
          rewrite <- drop_drop, IH12, drop_drop, Nat.add_comm.
          rewrite <- drop_drop, IH22, drop_drop, Nat.add_comm.
          reflexivity.
        split; try assumption.
          assert (forall s : Stream A, take (n1 + n2) s = take (n2 + n1) s).
            rewrite Nat.add_comm. reflexivity.
          rewrite (H0 s3), 2!take_add, IH11, IH12, <- IH22, <- IH21,
                  <- 2!take_add, <- (H0 s2).
          reflexivity.
    destruct 1 as [n [H1 H2]].
      rewrite (take_drop _ n s1), (take_drop _ n s2), H2.
      apply SPermutation_Permutation_lsapp.
        assumption.
        apply SPerm_refl.
Qed.
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
    [SPermutation s (swap s)] nie zachodzi, bo przestawienia elementów ciągna się w
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

Module approx.

Print take.

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

Require Import Program.Equality.

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
    tl :=
      unvtake (fun n : nat => vtl (f (S n)))
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