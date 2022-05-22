Require Import CoqAlgs.Base.

Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | ncons : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments ncons [A] _ _.

Fixpoint last {A : Type} (l : nel A) : A :=
match l with
    | singl x => x
    | ncons _ t => last t
end.

Fixpoint len {A : Type} (l : nel A) : nat :=
match l with
    | singl _ => 1
    | ncons _ l' => S (len l')
end.

(* PNNS stands for PositionalNaturalNumberSystem. *)
Class PNNS : Type :=
{
    digit : Type;
    weight : nat -> nat;
    dvalue : digit -> nat;
}.

(* A number in some PNNS is a nonempty sequence of digits (with the least
   significant digit at the head of the list) such that the value of the
   most significant digit (i. e. the last one) is not zero. *)
Definition num (sys : PNNS) : Type :=
  {l : nel digit | dvalue (last l) <> 0}.

Fixpoint nvalue_aux {sys : PNNS} (ds : nel digit) (i : nat) : nat :=
match ds with
    | singl d => dvalue d * weight i
    | ncons d ds' => dvalue d * weight i + nvalue_aux ds' (S i)
end.

Definition nvalue {sys : PNNS} (n : num sys) : nat :=
  nvalue_aux (proj1_sig n) 0.

Instance unary : PNNS :=
{
    digit := unit;
    weight := fun _ => 1;
    dvalue tt := 1
}.

Lemma nvalue_aux_len :
  forall (ds : nel unit) (i : nat),
    @nvalue_aux unary ds i = len ds.
Proof.
  induction ds as [d | d ds']; cbn; intros; rewrite ?IHds'; reflexivity.
Qed.

Theorem nvalue_len :
  forall n : num unary,
    nvalue n = len (proj1_sig n).
Proof.
  destruct n. cbn. apply nvalue_aux_len.
Qed.

Definition nat_to_unary (n : nat) : num unary.
Proof.
  induction n as [| n'].
    exists (singl tt). cbn. congruence.
    destruct IHn' as [ds H]. exists (ncons tt ds). cbn. congruence.
Defined.

Definition complete (sys : PNNS) : Prop :=
  forall n : nat, exists rep : num sys, nvalue rep = n.

Theorem unary_not_complete :
  ~ complete unary.
Proof.
  unfold complete. intro. destruct (H 0) as [[ds wut] H'].
  cbn in *; clear wut. destruct ds; cbn in H'; congruence.
Qed.

Definition redundant (sys : PNNS) : Prop :=
  exists rep1 rep2 : num sys,
    proj1_sig rep1 <> proj1_sig rep2 /\ nvalue rep1 = nvalue rep2.

Lemma unary_nvalue_aux_inj :
  forall (ds1 ds2 : nel (@digit unary)) (i : nat),
    nvalue_aux ds1 i = nvalue_aux ds2 i -> ds1 = ds2.
Proof.
  induction ds1 as [[] | [] ds1'];
  destruct ds2 as [[] | [] ds2']; cbn in *; intros.
    reflexivity.
    destruct ds2'; cbn in H; try congruence.
    destruct ds1'; cbn in H; try congruence.
    f_equal. inv H. exact (IHds1' _ _ H1).
Qed.

Theorem unary_not_redundant :
  ~ redundant unary.
Proof.
  unfold redundant. intro.
  destruct H as [[ds1 H1] [[ds2 H2] [H H']]]; cbn in *; clear H1 H2.
  apply unary_nvalue_aux_inj in H'. contradiction.
Qed.