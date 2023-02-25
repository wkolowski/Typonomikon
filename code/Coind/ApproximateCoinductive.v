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

Fixpoint PartialStream (A : Type) (n : nat) : Type :=
match n with
| 0 => unit
| S n' => StreamF (fun A => PartialStream A n') A
end.

Definition Undefined {A : Type} : PartialStream A 0 := tt.

Definition Defined
  {n : nat} {A : Type} (ps : PartialStream A (S n)) : PartialStream A (S n) := ps.

Lemma eta_PartialStream_S :
  forall {A : Type} (n : nat) (ps : PartialStream A (S n)),
    ps = Defined {| hd := hd ps; tl := tl ps; |}.
Proof. easy. Qed.

Fixpoint shrink
  {n : nat} {A : Type} {struct n} : PartialStream A (S n) -> PartialStream A n :=
match n with
| 0 => fun _ => Undefined
| S n' => fun ps => Defined {| hd := hd ps; tl := shrink (tl ps); |}
end.

Lemma hd_succ :
  forall {A : Type} (f : forall n : nat, PartialStream A n),
    (forall n : nat, shrink (f (S n)) = f n) ->
      forall n : nat, hd (f (S n)) = hd (f 1).
Proof.
  induction n as [| n']; [easy |].
  now rewrite <- IHn', <- (H (S n')).
Qed.

Fixpoint approx {A : Type} (s : Stream A) (n : nat) : PartialStream A n :=
match n with
| 0 => Undefined
| S n' => Defined {| hd := hd (out s); tl := approx (tl (out s)) n'; |}
end.

Lemma shrink_approx :
  forall {A : Type} (s : Stream A) (n : nat),
    shrink (approx s (S n)) = approx s n.
Proof.
  intros A s n; revert s.
  induction n as [| n']; cbn; intros; [easy |].
  now rewrite <- (IHn' (tl (out s))).
Qed.

CoFixpoint unapprox {A : Type} (f : forall n : nat, PartialStream A n) : Stream A :=
  Cons (hd (f 1)) (unapprox (fun n => tl (f (S n)))).

Lemma approx_unapprox :
  forall {A : Type} (s : Stream A),
    Bisim (unapprox (approx s)) s.
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out s) as [h t]; cbn.
  constructor; cbn; [easy |].
  apply CH.
Qed.

Lemma unapprox_approx :
  forall {A : Type} (f : forall n : nat, PartialStream A n),
    (forall n : nat, shrink (f (S n)) = f n) ->
      forall n : nat, approx (unapprox f) n = f n.
Proof.
  intros A f H n; revert f H.
  induction n as [| n']; cbn; intros.
  - now destruct (f 0).
  - rewrite eta_PartialStream_S, IHn', (hd_succ _ H n'); [easy |].
    now intros; rewrite <- (H (S n)).
Qed.