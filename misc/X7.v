(** * X7: Strumienie *)

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A}.
Arguments tl {A}.

CoInductive bisim {A : Type} (s1 s2 : Stream A) : Prop :=
{
    hds : hd s1 = hd s2;
    tls : bisim (tl s1) (tl s2);
}.

Lemma bisim_refl :
  forall (A : Type) (s : Stream A), bisim s s.
Proof.
  cofix CH. constructor; auto.
Qed.

Lemma bisim_sym :
  forall (A : Type) (s1 s2 : Stream A),
    bisim s1 s2 -> bisim s2 s1.
Proof.
  cofix CH.
  destruct 1 as [hds tls]. constructor; auto.
Qed.

Lemma bisim_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    bisim s1 s2 -> bisim s2 s3 -> bisim s1 s3.
Proof.
  cofix CH.
  destruct 1 as [hds1 tls1], 1 as [hds2 tls2].
  constructor; eauto. rewrite hds1. assumption.
Qed.

CoFixpoint app {A : Type} (s1 s2 : Stream A) : Stream A :=
{|
    hd := hd s1;
    tl := app (tl s1) s2;
|}.

Ltac coind := cofix CH; constructor; cbn; auto.

Lemma app_pointless :
  forall (A : Type) (s1 s2 : Stream A),
    bisim (app s1 s2) s1.
Proof.
  coind.
Qed.

Fixpoint lsapp {A : Type} (l : list A) (s : Stream A) : Stream A :=
match l with
    | nil => s
    | cons h t => {| hd := h; tl := lsapp t s; |}
end.

CoFixpoint map {A B : Type} (f : A -> B) (s : Stream A) : Stream B :=
{|
    hd := f (hd s);
    tl := map f (tl s);
|}.

Lemma map_id :
  forall (A : Type) (s : Stream A), bisim (map (@id A) s) s.
Proof.
  coind.
Qed.

Lemma map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (s : Stream A),
    bisim (map g (map f s)) (map (fun x => g (f x)) s).
Proof.
  coind.
Qed.

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

(*
CoFixpoint unzipWith
  {A B C : Type} (f : C -> A * B) (s : Stream C) : Stream A * Stream B
*)

(** TODO: join : Stream (Stream A) -> Stream A,
          unzis *)

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

Compute insert 5 42 (from 0).

Fixpoint replace (n : nat) {A : Type} (x : A) (s : Stream A) : Stream A :=
match n with
    | 0 => {| hd := x; tl := tl s; |}
    | S n' => {| hd := hd s; tl := replace n' x (tl s); |}
end.

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

Lemma intersperse_merge_repeat :
  forall (A : Type) (x : A) (s : Stream A),
    bisim (intersperse x s) (merge s (repeat x)).
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    constructor; cbn.
      reflexivity.
      apply CH.
Qed.

(* Raczej się nie da. *)
(*
Parameter splitBy :
  forall A : Type, (A -> bool) -> list A -> list (list A).

Parameter groupBy :
  forall A : Type, (A -> A -> bool) -> list A -> list (list A).
*)

(* Dlaczego [s] nie musi tu być indeksem? *)
Inductive Elem {A : Type} (x : A) (s : Stream A) : Prop :=
    | Elem_hd : x = hd s -> Elem x s
    | Elem_tl : Elem x (tl s) -> Elem x s.

Hint Constructors Elem.

Inductive Dup {A : Type} (s : Stream A) : Prop :=
    | Dup_hd : Elem (hd s) (tl s) -> Dup s
    | Dup_tl : Dup (tl s) -> Dup s.

Ltac inv H := inversion H; subst; clear H.

Require Import Arith.

Lemma Elem_nth :
  forall (A : Type) (x : A) (s : Stream A),
    Elem x s <-> exists n : nat, nth n s = x.
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

Lemma nth_from :
  forall n m : nat,
    nth n (from m) = n + m.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    specialize (IHn' (S m)). rewrite <- plus_n_Sm in IHn'. assumption.
Qed.

Lemma Elem_from_add :
  forall n m : nat, Elem n (from m) ->
    forall k : nat, Elem (k + n) (from m).
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

Lemma Elem_from :
  forall n m : nat, Elem n (from m) <-> m <= n.
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

Lemma Dup_spec :
  forall (A : Type) (s : Stream A),
    Dup s <-> exists n m : nat, n <> m /\ nth n s = nth m s.
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

Lemma NoDup_from :
  forall n : nat, ~ Dup (from n).
Proof.
  intros n H. rewrite Dup_spec in H.
  destruct H as (m1 & m2 & H1 & H2).
  rewrite 2!nth_from, Nat.add_cancel_r in H2.
  contradiction.
Qed.

Inductive Exists {A : Type} (P : A -> Prop) : Stream A -> Prop :=
    | Exists_hd : forall s : Stream A, P (hd s) -> Exists P s
    | Exists_tl : forall s : Stream A, Exists P (tl s) -> Exists P s.

Lemma Exists_spec :
  forall (A : Type) (P : A -> Prop) (s : Stream A),
    Exists P s <-> exists n : nat, P (nth n s).
Proof.
  split.
    induction 1 as [| s H [n IH]].
      exists 0. cbn. assumption.
      exists (S n). cbn. assumption.
    intros [n H]. revert s H. induction n as [| n']; intros; cbn in *.
      left. assumption.
      right. apply IHn'. assumption.
Qed.

CoInductive Forall {A : Type} (s : Stream A) (P : A -> Prop) : Prop :=
{
    Forall_hd : P (hd s);
    Forall_tl : Forall (tl s) P;
}.

Lemma Forall_spec :
  forall (A : Type) (s : Stream A) (P : A -> Prop),
    Forall s P <-> forall n : nat, P (nth n s).
Proof.
  split; intros.
    revert s H. induction n as [| n']; cbn; intros.
      inv H. assumption.
      apply IHn'. inv H. assumption.
    revert s H. cofix CH. constructor.
      apply (H 0).
      apply CH. intro. specialize (H (S n)). cbn in H. assumption.
Qed.

(*
CoInductive Substream2 {A : Type} (s1 s2 : Stream A) : Prop :=
{
    Substream2' :
      (hd s1 = hd s2 /\ Substream2 (tl s1) (tl s2)) \/
      Substream2 s1 (tl s2);
}.

Lemma Substream2_bad :
  forall (A : Type) (s1 s2 : Stream A), Substream2 s1 s2.
Proof.
  coind.
Qed.
*)

CoInductive Substream {A : Type} (s1 s2 : Stream A) : Prop :=
{
    n : nat;
    p : hd s1 = nth n s2;
    Substream' : Substream (tl s1) (drop (S n) s2);
}.

Lemma drop_tl :
  forall (A : Type) (n : nat) (s : Stream A),
    drop n (tl s) = drop (S n) s.
Proof.
  reflexivity.
Qed.

Lemma tl_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    tl (drop n s) = drop n (tl s).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    apply IHn'.
Qed.

Lemma nth_drop :
  forall (A : Type) (n m : nat) (s : Stream A),
    nth n (drop m s) = nth (n + m) s.
Proof.
  induction n as [| n']; cbn; intros.
    revert s. induction m as [| m']; cbn; intros.
      reflexivity.
      apply IHm'.
    rewrite <- IHn'. cbn. rewrite tl_drop. reflexivity.
Qed.

Lemma drop_drop :
  forall (A : Type) (n m : nat) (s : Stream A),
    drop m (drop n s) = drop (n + m) s.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    apply IHn'.
Qed.

Require Import Arith.

Lemma Substream_tl :
  forall (A : Type) (s1 s2 : Stream A),
    Substream s1 s2 -> Substream (tl s1) (tl s2).
Proof.
  destruct 1 as [n p [m q H]]. econstructor.
    rewrite q, nth_drop, <- plus_n_Sm. cbn. reflexivity.
    rewrite drop_drop in H. cbn in H. rewrite Nat.add_comm in H.
      cbn in *. assumption.
Qed.

Lemma Substream_drop :
  forall (A : Type) (n : nat) (s1 s2 : Stream A),
    Substream s1 s2 -> Substream (drop n s1) (drop n s2).
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    apply IHn', Substream_tl, H.
Qed.

Lemma hd_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    hd (drop n s) = nth n s.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    apply IHn'.
Qed.

Lemma Substream_drop_add :
  forall (A : Type) (n m : nat) (s1 s2 : Stream A),
    Substream s1 (drop n s2) -> Substream s1 (drop (n + m) s2).
Proof.
  induction n as [| n']; cbn; intros.
Abort.

Lemma Substream_refl :
  forall (A : Type) (s : Stream A), Substream s s.
Proof.
  cofix CH.
  intros. econstructor.
    instantiate (1 := 0). cbn. reflexivity.
    apply CH.
Qed.

Lemma Substream_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    Substream s1 s2 -> Substream s2 s3 -> Substream s1 s3.
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

Lemma Substream_not_antisymm :
  exists (A : Type) (s1 s2 : Stream A),
    Substream s1 s2 /\ Substream s2 s1 /\ ~ bisim s1 s2.
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

Inductive Suffix {A : Type} : Stream A -> Stream A -> Prop :=
    | Suffix_refl : forall s : Stream A, Suffix s s
    | Suffix_tl :
        forall s1 s2 : Stream A,
          Suffix (tl s1) s2 -> Suffix s1 s2.

Fixpoint snoc {A : Type} (x : A) (l : list A) : list A :=
match l with
    | nil => cons x nil
    | cons h t => cons h (snoc x t)
end.

Lemma Suffix_spec :
  forall (A : Type) (s1 s2 : Stream A),
    Suffix s1 s2 <-> exists l : list A, s1 = lsapp l s2.
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

Definition Incl {A : Type} (s1 s2 : Stream A) : Prop :=
  forall x : A, Elem x s1 -> Elem x s2.

Definition SetEquiv {A : Type} (s1 s2 : Stream A) : Prop :=
  Incl s1 s2 /\ Incl s2 s1.

Lemma bisim_Elem :
  forall (A : Type) (x : A) (s1 s2 : Stream A),
    bisim s1 s2 -> Elem x s1 -> Elem x s2.
Proof.
  intros until 2. revert s2 H. induction H0; intros.
    left. inv H0. assumption.
    right. apply IHElem. inv H. assumption.
Qed.

Lemma bisim_Incl :
  forall (A : Type) (s1 s1' s2 s2' : Stream A),
    bisim s1 s1' -> bisim s2 s2' -> Incl s1 s2 -> Incl s1' s2'.
Proof.
  unfold Incl. intros A s1 s1' s2 s2' H1 H2 H x H'.
  eapply bisim_Elem; eauto. apply H.
  eapply bisim_Elem; eauto. apply bisim_sym. assumption.
Qed.

Lemma bisim_SetEquiv :
  forall (A : Type) (s1 s1' s2 s2' : Stream A),
    bisim s1 s1' -> bisim s2 s2' -> SetEquiv s1 s2 -> SetEquiv s1' s2'.
Proof.
  unfold SetEquiv. destruct 3; split; eapply bisim_Incl; eauto.
Qed.

Definition scons {A : Type} (x : A) (s : Stream A) : Stream A :=
{|
    hd := x;
    tl := s;
|}.

Inductive SPermutation {A : Type} : Stream A -> Stream A -> Prop :=
    | SPerm_refl : forall s : Stream A, SPermutation s s
    | SPerm_skip :
        forall (x : A) (s1 s2 : Stream A),
          SPermutation s1 s2 -> SPermutation (scons x s1) (scons x s2)
    | SPerm_swap : forall (x y : A) (s1 s2 : Stream A),
        SPermutation s1 s2 ->
        SPermutation (scons x (scons y s1)) (scons y (scons x s2))
    | SPerm_trans : forall s1 s2 s3 : Stream A,
        SPermutation s1 s2 -> SPermutation s2 s3 -> SPermutation s1 s3.

Hint Constructors SPermutation.

(*
Definition stake n {A} s := @take n A s.

Require Import CoqBookPL.book.X3.
*)

Require Import Permutation.

Lemma lsapp_scons :
  forall (A : Type) (l : list A) (x : A) (s : Stream A),
    lsapp l (scons x s) = lsapp (snoc x l) s.
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.

Lemma SPermutation_Permutation_lsapp :
  forall (A : Type) (l1 l2 : list A) (s1 s2 : Stream A),
    Permutation l1 l2 -> SPermutation s1 s2 ->
      SPermutation (lsapp l1 s1) (lsapp l2 s2).
Proof.
  intros until 2. revert s1 s2 H0.
  induction H; intros; cbn; eauto.
  constructor. induction l as [| h t]; cbn.
    assumption.
    constructor. apply IHt.
Qed.

Lemma take_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    s = lsapp (take n s) (drop n s).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite <- IHn'. destruct s; reflexivity.
Qed.

Lemma take_add :
  forall (A : Type) (n m : nat) (s : Stream A),
    take (n + m) s = List.app (take n s) (take m (drop n s)).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

Lemma SPermutation_spec :
  forall (A : Type) (s1 s2 : Stream A),
    SPermutation s1 s2 <->
    exists n : nat,
      Permutation (take n s1) (take n s2) /\
      drop n s1 = drop n s2.
Proof.
  split.
    induction 1; cbn.
      exists 0. cbn. split; auto.
      destruct IHSPermutation as [n [IH1 IH2]].
        exists (S n). cbn. auto.
      destruct IHSPermutation as [n [IH1 IH2]].
        exists (S (S n)). cbn. split.
          eapply perm_trans.
            apply perm_swap.
            do 2 apply perm_skip. assumption.
          assumption.
        destruct IHSPermutation1 as [n1 [IH11 IH12]],
                 IHSPermutation2 as [n2 [IH21 IH22]].
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
            rewrite (H2 s3), 2!take_add, IH11, IH12, <- IH22, <- IH21,
                    <- 2!take_add, <- (H2 s2).
            reflexivity.
    destruct 1 as [n [H1 H2]].
      rewrite (take_drop _ n s1), (take_drop _ n s2), H2.
      apply SPermutation_Permutation_lsapp.
        assumption.
        apply SPerm_refl.
Qed.