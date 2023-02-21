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

Inductive PartialStream (A : Type) : nat -> Type :=
| Undefined : PartialStream A 0
| Defined : forall {n : nat}, StreamF (fun A => PartialStream A n) A -> PartialStream A (S n).

Arguments Undefined {A}.
Arguments Defined   {A n} _.

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

From Equations Require Import Equations.

Equations shrink' {A : Type} (n : nat) (ps : PartialStream A (S n)) : PartialStream A n :=
| 0, ps => Undefined
| S n', Defined s => Defined {| hd := hd s; tl := shrink' n' (tl s); |}.

Arguments shrink' {A n} _.

Lemma phd_shrink :
  forall {A : Type} {n : nat} (ps : PartialStream A (S (S n))),
    phd (shrink ps) = phd ps.
Proof.
  now intros; dependent destruction ps.
Qed.

Lemma phd_shrink' :
  forall {A : Type} {n : nat} (ps : PartialStream A (S (S n))),
    phd (shrink' ps) = phd ps.
Proof.
  intros A n ps.
  funelim (shrink' ps); cbn.
  now rewrite shrink'_equation_2; cbn.
Qed.

Lemma ptl_shrink :
  forall {A : Type} {n : nat} (ps : PartialStream A (S (S n))),
    ptl (shrink ps) = shrink (ptl ps).
Proof.
  now intros; dependent destruction ps.
Qed.

Lemma ptl_shrink' :
  forall {A : Type} {n : nat} (ps : PartialStream A (S (S n))),
    ptl (shrink' ps) = shrink' (ptl ps).
Proof.
  intros A n ps.
  funelim (shrink' ps); cbn.
  now rewrite shrink'_equation_2; cbn.
Qed.

Lemma phd_succ :
  forall {A : Type} (f : forall n : nat, PartialStream A n),
    (forall n : nat, shrink (f (S n)) = f n) ->
      forall n : nat, phd (f (S n)) = phd (f 1).
Proof.
  induction n as [| n']; [easy |].
  now rewrite <- IHn', <- (H (S n')), phd_shrink.
Qed.

CoFixpoint unapprox {A : Type} (f : forall n : nat, PartialStream A n) : Stream A :=
  Cons (phd (f 1)) (unapprox (fun n => ptl (f (S n)))).

Fixpoint approx {A : Type} (s : Stream A) (n : nat) : PartialStream A n :=
match n with
| 0 => Undefined
| S n' => Defined {| hd := hd (out s); tl := approx (tl (out s)) n'; |}
end.

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

Lemma eta_PartialStream_0 :
  forall {A : Type} (s : PartialStream A 0),
    s = Undefined.
Proof.
  now dependent destruction s.
Qed.

Lemma eta_PartialStream_S :
  forall {A : Type} (n : nat) (ps : PartialStream A (S n)),
    ps = Defined {| hd := phd ps; tl := ptl ps; |}.
Proof.
  now dependent destruction ps.
Qed.

Lemma unapprox_approx :
  forall {A : Type} (f : forall n : nat, PartialStream A n),
    (forall n : nat, shrink (f (S n)) = f n) ->
      forall n : nat, approx (unapprox f) n = f n.
Proof.
  intros A f H n; revert f H.
  induction n as [| n']; cbn; intros.
  - now rewrite eta_PartialStream_0.
  - rewrite eta_PartialStream_S, IHn', (phd_succ _ H n'); [easy |].
    now intros; rewrite <- ptl_shrink, H.
Qed.

Inductive Approx {A : Type}
  : forall {n1 n2 : nat}, PartialStream A n1 -> PartialStream A n2 -> Prop :=
| Approx_Undefined : Approx Undefined Undefined
| Approx_Defined :
    forall
      {n1 : nat} {ps1 : PartialStream A (S n1)}
      {n2 : nat} {ps2 : PartialStream A (S n2)},
        phd ps1 = phd ps2 -> Approx (ptl ps1) (ptl ps2) -> Approx ps1 ps2.
(*     forall
      {n1 : nat} {s1 : StreamF (fun A => PartialStream A n1) A}
      {n2 : nat} {s2 : StreamF (fun A => PartialStream A n2) A},
        BisimF eq (@Approx A n1 n2) s1 s2 -> Approx (Defined s1) (Defined s2).
        phd *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) : P x -> P y :=
match p with
| eq_refl => id
end.

Lemma Approx_eq :
  forall
    {A : Type} {n1 n2 : nat}
    {ps1 : PartialStream A n1} {ps2 : PartialStream A n2} (p : n1 = n2),
      Approx ps1 ps2 -> transport _ p ps1 = ps2.
Proof.
  induction 1.
  - admit.
  - inversion H as [hds tls]. inversion 
Qed.

Lemma unapprox_approx' :
  forall {A : Type} (f : forall n : nat, PartialStream A n),
    (forall n : nat, shrink' (f (S n)) = f n) ->
      forall n : nat, approx (unapprox f) n = f n.
Proof.
  intros A f H n; revert f H.
  induction n as [| n']; cbn; intros.
  - remember (f 0) as f0. now dependent destruction f0.
(*     now rewrite eta_PartialStream_0. *)
  - Axiom wut : False. destruct wut.
    (* rewrite eta_PartialStream_S, IHn', (phd_succ _ H n'); [easy |].
    now intros; rewrite <- ptl_shrink, H. *)
Qed.

Print Assumptions unapprox_approx'.