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

(*
CoFixpoint unzipWith
  {A B C : Type} (f : C -> A * B) (s : Stream C) : Stream A * Stream B
*)

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

(*Fixpoint take (n : nat) {A : Type} (s : Stream A) : list A :=
*)

Fixpoint drop (n : nat) {A : Type} (s : Stream A) : Stream A :=
match n with
    | 0 => s
    | S n' => drop n' (tl s)
end.

Fixpoint nth (n : nat) {A : Type} (s : Stream A) : A :=
match n with
    | 0 => hd s
    | S n' => nth n' (tl s)
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



Parameter splitBy :
  forall A : Type, (A -> bool) -> list A -> list (list A).
Parameter groupBy :
  forall A : Type, (A -> A -> bool) -> list A -> list (list A).


CoFixpoint from (n : nat) : Stream nat :=
{|
    hd := n;
    tl := from (S n);
|}.



CoInductive Elem {A : Type} (x : A) (s : Stream A) : Prop :=
{
    Elem' : hd s = x \/ Elem x (tl s);
}.


Lemma Elem_0_from_1 :
  forall n m : nat, Elem n (from m).
Proof.
  cofix CH.
  constructor. cbn. right. apply CH.
Qed.

CoInductive Forall {A : Type} (s : Stream A) (P : A -> Prop) : Prop :=
{
    Forall_hd : P (hd s);
    Forall_tl : Forall (tl s) P;
}.

CoInductive Exists2 {A : Type} (s : Stream A) (P : A -> Prop) : Prop :=
{
    Exists2' : P (hd s) \/ Exists2 (tl s) P;
}.

Lemma Exists2_bad :
  forall (A : Type) (s : Stream A) (P : A -> Prop), Exists2 s P.
Proof.
  cofix CH.
  constructor. right. apply CH.
Qed.

Inductive Exists {A : Type} (P : A -> Prop) : Stream A -> Prop :=
    | Exists_hd : forall s : Stream A, P (hd s) -> Exists P s
    | Exists_tl : forall s : Stream A, Exists P (tl s) -> Exists P s.

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

(*
Inductive Substream2 {A : Type} : Stream A -> Stream A -> Prop :=
    | Substream2_here :
        forall (h : A) (s1 s2 : Stream A),
          Substream s1 s2 -> Substream (
*)