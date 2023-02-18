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
  {A : Type} (R : A -> A -> Prop)
  {F : Type -> Type} (Knot : F A -> F A -> Prop) (s1 s2 : StreamF F A) : Prop :=
{
  BisimF_hd : R (hd s1) (hd s2);
  BisimF_tl : Knot (tl s1) (tl s2);
}.

CoInductive Bisim {A : Type} (s1 s2 : Stream A) : Prop :=
{
  Bisim_out : BisimF eq Bisim (out s1) (out s2);
}.

Inductive PartialStream (A : Type) : Type :=
| Undefined : PartialStream A
| Defined : StreamF PartialStream A -> PartialStream A.

Arguments Undefined {A}.
Arguments Defined   {A} _.

Inductive Approx {A : Type} : PartialStream A -> PartialStream A -> Prop :=
| Approx_Undefined :
    forall ps : PartialStream A, Approx Undefined ps
| Approx_Defined :
    forall s1 s2 : StreamF PartialStream A,
      BisimF eq Approx s1 s2 -> Approx (Defined s1) (Defined s2).

Lemma StreamF_eq :
  forall {F : Type -> Type} {A : Type} (s1 s2 : StreamF F A),
    hd s1 = hd s2 -> tl s1 = tl s2 -> s1 = s2.
Proof.
  now intros F A [] []; cbn; intros -> ->.
Qed.

Lemma Stream_eq :
  forall {A : Type} (s1 s2 : Stream A),
    hd (out s1) = hd (out s2) -> tl (out s1) = tl (out s2) -> s1 = s2.
Proof.
  intros A s1 s2.
  destruct (out s1) as [h1 t1] eqn: Heq1, (out s2) as [h2 t2] eqn: Heq2; cbn.
  intros -> ->.
Abort.

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

(* Nic z tego. *)
(*
Lemma Approx_inf :
  forall {A : Type} (ps1 ps2 : PartialStream A),
    {ps : PartialStream A | Approx ps ps1 /\ Approx ps ps2}.
Proof.
  fix IH 2.
  intros A [| s1] ps2.
  - exists Undefined.
    now split; constructor.
  - destruct ps2 as [| s2].
    + exists Undefined.
      now split; constructor.
*)

Record ApproximateStream (A : Type) : Type :=
{
  approx : nat -> PartialStream A;
  approx_monotone :
    forall {n m : nat}, n <= m -> Approx (approx n) (approx m);
}.

Arguments approx {A} _.
Arguments approx_monotone {A} _ {n m} _.

Fixpoint approx_Stream {A : Type} (s : Stream A) (n : nat) : PartialStream A :=
match n with
| 0 => Undefined
| S n' => Defined {| hd := hd (out s); tl := approx_Stream (tl (out s)) n'; |}
end.

Lemma approx_Stream_monotone :
  forall {A : Type} (s : Stream A) (n1 n2 : nat),
    n1 <= n2 -> Approx (approx_Stream s n1) (approx_Stream s n2).
Proof.
  intros A s n1; revert s.
  induction n1 as [| n1']; cbn; intros.
  - now constructor.
  - destruct n2 as [| n2']; cbn.
    + now inversion H.
    + constructor; constructor; cbn; [easy |].
      now apply IHn1', le_S_n.
Qed.

Fixpoint PartialStream' (n : nat) (A : Type) : Type :=
  StreamF 
    (match n with
    | 0 => fun _ => unit
    | S n' => PartialStream' n'
    end)
    A.

CoFixpoint unapprox {A : Type} (f : forall n : nat, PartialStream' n A) : Stream A :=
  Cons (hd (f 0)) (unapprox (fun n => tl (f (S n)))).

Fixpoint approx'_Stream {A : Type} (s : Stream A) (n : nat) : PartialStream' n A.
Proof.
  destruct n as [| n']; cbn.
  - exact {| hd := hd (out s); tl := tt; |}.
  - exact {| hd := hd (out s); tl := approx'_Stream A (tl (out s)) n'; |}.
Defined.

Lemma approx_unapprox :
  forall {A : Type} (s : Stream A),
    Bisim (unapprox (approx'_Stream s)) s.
Proof.
  cofix CH.
  constructor; cbn.
  destruct (out s) as [h t]; cbn.
  constructor; cbn; [easy |].
  apply CH.
Qed.

Lemma unapprox_approx :
  forall {A : Type} (f : forall n : nat, PartialStream' n A),
    forall n : nat, approx'_Stream (unapprox f) n = f n.
Proof.
  intros A f n; revert f.
  induction n as [| n']; cbn; intros.
  - now destruct (f 0) as [h []]; cbn.
  - rewrite IHn'.
    apply StreamF_eq; cbn; [| easy].
    admit. (* Kłamstwo. *)
Admitted.