Require Import Equality Lia.

Set Primitive Projections.

Record StreamF (F : Type -> Type) (A : Type) : Type := ConsF
{
  hd : A;
  tl : F A;
}.

Arguments ConsF {F A} _ _.
Arguments hd {F A} _.
Arguments tl {F A} _.

CoInductive Stream (A : Type) : Type := MkStream
{
  out : StreamF Stream A;
}.

Arguments MkStream {A} _.
Arguments out {A} _.

Notation Stream' A := (StreamF Stream A).
Notation Cons h t := (MkStream (ConsF h t)).

Record BisimF
  {A1 A2 : Type} (R : A1 -> A2 -> Prop)
  {F1 F2 : Type -> Type} (Knot : F1 A1 -> F2 A2 -> Prop)
  (s1 : StreamF F1 A1) (s2 : StreamF F2 A2) : Prop :=
{
  BisimF_hd : R (hd s1) (hd s2);
  BisimF_tl : Knot (tl s1) (tl s2);
}.

CoInductive Bisim {A : Type} (s1 s2 : Stream A) : Prop :=
{
  Bisim_out : BisimF eq Bisim (out s1) (out s2);
}.

Lemma StreamF_eq :
  forall {F : Type -> Type} {A : Type} (s1 s2 : StreamF F A),
    hd s1 = hd s2 -> tl s1 = tl s2 -> s1 = s2.
Proof.
  now intros F A [] []; cbn; intros -> ->.
Qed.

Module nondep.

Inductive PartialStream (A : Type) : Type :=
| Undefined : PartialStream A
| Defined : StreamF PartialStream A -> PartialStream A.

Arguments Undefined {A}.
Arguments Defined   {A} _.

Fixpoint size {A : Type} (ps : PartialStream A) : nat :=
match ps with
| Undefined => 0
| Defined s => 1 + size (tl s)
end.

Definition ptl {A : Type} (ps : PartialStream A) : option (PartialStream A) :=
match ps with
| Undefined => None
| Defined s => Some (tl s)
end.

Fixpoint shrink {A : Type} (ps : PartialStream A) : option (PartialStream A) :=
match ps with
| Undefined => None
| Defined s =>
    match shrink (tl s) with
    | None => Some Undefined
    | Some s' => Some (Defined {| hd := hd s; tl := s'; |})
    end
end.

Inductive Approx {A : Type} : PartialStream A -> PartialStream A -> Prop :=
| Approx_Undefined :
    forall ps : PartialStream A, Approx Undefined ps
| Approx_Defined :
    forall s1 s2 : StreamF PartialStream A,
      BisimF eq Approx s1 s2 -> Approx (Defined s1) (Defined s2).

Lemma Approx_refl :
  forall {A : Type} (ps : PartialStream A),
    Approx ps ps.
Proof.
  fix IH 2.
  destruct ps as [| [h t]].
  - now constructor.
  - constructor.
    constructor; cbn; [easy |].
    now apply IH.
Qed.

Lemma Approx_antisym :
  forall {A : Type} (ps1 ps2 : PartialStream A),
    Approx ps1 ps2 -> Approx ps2 ps1 -> ps1 = ps2.
Proof.
  fix IH 4.
  intros A ps1 ps2 [| s1 s2 H12] H21.
  - now inversion H21.
  - inversion H12.
    f_equal.
    apply StreamF_eq; [easy |].
    apply IH; [easy |].
    now inversion H21; inversion H1.
Qed.

Lemma Approx_trans :
  forall {A : Type} (ps1 ps2 ps3 : PartialStream A),
    Approx ps1 ps2 -> Approx ps2 ps3 -> Approx ps1 ps3.
Proof.
  fix IH 5.
  intros A ps1 ps2 ps3 [| s1 s2 H12].
  - now constructor.
  - inversion 1 as [| ? s3 H23]; subst.
    constructor.
    inversion H12; inversion H23.
    constructor; [congruence |].
    now apply IH with (tl s2).
Qed.

Record ApproximateStream (A : Type) : Type :=
{
  approx : nat -> PartialStream A;
  size_approx : forall n : nat, size (approx n) = n;
(*   approx_monotone :
    forall {n m : nat}, n <= m -> Approx (approx n) (approx m); *)
  approx_0 : approx 0 = Undefined;
  approx_S : forall n : nat, ptl (approx (S n)) = Some (approx n);
  shrink_approx :
    forall n : nat, shrink (approx (S n)) = Some (approx n);
}.

Arguments approx {A} _.
(* Arguments approx_monotone {A} _ {n m} _. *)

Fixpoint approx_Stream {A : Type} (s : Stream A) (n : nat) : PartialStream A :=
match n with
| 0 => Undefined
| S n' => Defined {| hd := hd (out s); tl := approx_Stream (tl (out s)) n'; |}
end.

Lemma size_approx_Stream :
  forall {A : Type} (n : nat) (s : Stream A),
    size (approx_Stream s n) = n.
Proof.
  now induction n as [| n']; cbn; intros; [| rewrite IHn'].
Qed.

Lemma approx_Stream_monotone :
  forall {A : Type} (s : Stream A) (n1 n2 : nat),
    n1 <= n2 -> Approx (approx_Stream s n1) (approx_Stream s n2).
Proof.
  intros A s n1; revert s.
  induction n1 as [| n1']; cbn; intros; [now constructor |].
  destruct n2 as [| n2']; cbn; [now inversion H |].
  constructor; constructor; cbn; [easy |].
  now apply IHn1', le_S_n.
Qed.

CoFixpoint unapprox_Stream {A : Type} (s : ApproximateStream A) : Stream A.
Proof.
  destruct s as [f size_f f_0 f_S shrink_approx].
  destruct (f 1) eqn: Heq.
  - now apply (f_equal shrink) in Heq; rewrite shrink_approx in Heq; cbn in Heq.
  - refine (MkStream {| hd := hd s; tl := _; |}).
    apply unapprox_Stream.
    unshelve econstructor.
    +
Abort.
  (*
    Nie za bardzo idzie to zdefiniować - skąd mamy wiedzieć, że [f 0] ma głowę
    tak jak byśmy się spodziewali?
  *)

End nondep.

Module dep.

Fixpoint PartialStream (n : nat) (A : Type) : Type :=
  StreamF
    (match n with
    | 0 => fun _ => unit
    | S n' => PartialStream n'
    end)
    A.

Definition phd {n : nat} {A : Type} : PartialStream n A -> A :=
match n with
| 0 => hd
| S n' => hd
end.

Definition ptl {n : nat} {A : Type} : PartialStream (S n) A -> PartialStream n A :=
match n with
| 0 => tl
| S n' => tl
end.

CoFixpoint unapprox {A : Type} (f : forall n : nat, PartialStream n A) : Stream A :=
  Cons (hd (f 0)) (unapprox (fun n => tl (f (S n)))).

Fixpoint approx_Stream {A : Type} (s : Stream A) (n : nat) : PartialStream n A.
Proof.
  destruct n as [| n']; cbn.
  - exact {| hd := hd (out s); tl := tt; |}.
  - exact {| hd := hd (out s); tl := approx_Stream A (tl (out s)) n'; |}.
Defined.

Lemma approx_unapprox :
  forall {A : Type} (s : Stream A),
    Bisim (unapprox (approx_Stream s)) s.
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out s) as [h t]; cbn.
  constructor; cbn; [easy |].
  apply CH.
Qed.

Lemma unapprox_approx :
  forall {A : Type} (f : forall n : nat, PartialStream n A),
    (forall n : nat, ptl (f (S n)) = f n) ->
      forall n : nat, approx_Stream (unapprox f) n = f n.
Proof.
  intros A f H n; revert f H.
  induction n as [| n']; cbn; intros.
  - now destruct (f 0) as [h []]; cbn.
  - rewrite IHn'.
    + apply StreamF_eq; cbn; [| easy].
      admit.
    + intros n.
      specialize (H n); unfold ptl in H.
Admitted.

End dep.

Module AlternativeDef.

Definition PartialStream' (n : nat) (A : Type) : Type :=
  StreamF
    ((fix PartialStream' (n : nat) : Type -> Type :=
      match n with
      | 0 => fun _ => unit
      | S n' => StreamF (PartialStream' n')
      end) n)
    A.

Fixpoint approx'_Stream {A : Type} (s : Stream A) (n : nat) : PartialStream' n A.
Proof.
  constructor.
  - exact (hd (out s)).
  - destruct n as [| n'].
    + exact tt.
    + exact (approx'_Stream A (tl (out s)) n').
Defined.

End AlternativeDef.

Module Inductive.

Inductive PartialStream (A : Type) : nat -> Type :=
| Undefined : PartialStream A 0
| Defined : forall {n : nat}, StreamF (fun A => PartialStream A n) A -> PartialStream A (S n).

Arguments Undefined {A}.
Arguments Defined   {A n} _.

Inductive Approx {A : Type}
  : forall {n1 n2 : nat}, PartialStream A n1 -> PartialStream A n2 -> Prop :=
| Approx_Undefined :
    forall {n : nat} (ps : PartialStream A n), Approx Undefined ps
| Approx_Defined :
    forall
      {n1 : nat} {s1 : StreamF (fun A => PartialStream A n1) A}
      {n2 : nat} {s2 : StreamF (fun A => PartialStream A n2) A},
        BisimF eq (@Approx A n1 n2) s1 s2 -> Approx (Defined s1) (Defined s2).

Definition phd {n : nat} {A : Type} (ps : PartialStream A (S n)) : A :=
match ps with
| Defined s => hd s
end.

Definition ptl {n : nat} {A : Type} (ps : PartialStream A (S n)) : PartialStream A n :=
match ps with
| Defined s => tl s
end.

Fixpoint shrink {n : nat} {A : Type} {struct n} : PartialStream A (S n) -> PartialStream A n.
Proof.
  destruct n as [| n'].
  - exact (fun _=> Undefined).
  - intros ps; dependent destruction ps.
    exact (Defined {| hd := hd s; tl := shrink _ _ (tl s); |}).
Defined.

Lemma phd_shrink :
  forall {A : Type} (f : forall n : nat, PartialStream A n),
    (forall n : nat, shrink (f (S n)) = f n) ->
      forall n : nat, phd (f (S n)) = phd (f 1).
Proof.
  induction n as [| n']; [easy |].
  specialize (H (S n')).
  remember (f (S (S n'))) as x.
  dependent destruction x; cbn in *.
  apply (f_equal phd) in H; cbn in H.
  now congruence.
Qed.

CoFixpoint unapprox {A : Type} (f : forall n : nat, PartialStream A n) : Stream A :=
  Cons (phd (f 1)) (unapprox (fun n => ptl (f (S n)))).

Fixpoint approx_Stream {A : Type} (s : Stream A) (n : nat) : PartialStream A n :=
match n with
| 0 => Undefined
| S n' => Defined {| hd := hd (out s); tl := approx_Stream (tl (out s)) n'; |}
end.

Lemma approx_unapprox :
  forall {A : Type} (s : Stream A),
    Bisim (unapprox (approx_Stream s)) s.
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out s) as [h t]; cbn.
  constructor; cbn; [easy |].
  apply CH.
Qed.

Lemma PartialStream_0 :
  forall {A : Type} (s : PartialStream A 0),
    s = Undefined.
Proof.
  now dependent destruction s.
Qed.

Lemma PartialStream_S :
  forall {A : Type} (n : nat) (s : PartialStream A (S n)),
    s = Defined {| hd := phd s; tl := ptl s; |}.
Proof.
  now dependent destruction s.
Qed.

Lemma unapprox_approx :
  forall {A : Type} (f : forall n : nat, PartialStream A n),
    (forall n : nat, shrink (f (S n)) = f n) ->
      forall n : nat, approx_Stream (unapprox f) n = f n.
Proof.
  intros A f H n; revert f H.
  induction n as [| n']; cbn; intros.
  - now rewrite PartialStream_0.
  - rewrite PartialStream_S, IHn'.
    + do 2 f_equal.
      now unshelve erewrite (phd_shrink _ _ n').
    + intros n; specialize (H (S n)).
      remember (f (S (S n))) as x.
      dependent destruction x; cbn in *.
      apply (f_equal ptl) in H; cbn in H.
      now congruence.
Qed.

End Inductive.