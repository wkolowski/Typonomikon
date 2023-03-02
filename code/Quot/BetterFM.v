Require Import Recdef StrictProp Bool Lia.

Inductive FM (A : Type) : Type :=
| e  : FM A
| i  : A -> FM A
| op : FM A -> FM A -> FM A.

Arguments e  {A}.
Arguments i  {A} _.
Arguments op {A} _ _.

Inductive NF {A : Type} : FM A -> Prop :=
| NF_e  : NF e
| NF_i  : forall a : A, NF (i a)
| NF_op : forall (a : A) (y : FM A), NF y -> y <> e -> NF (op (i a) y).

Record FM' (A : Type) : Type :=
{
  cf : FM A;
  NF_cf : Squash (NF cf);
}.

(*
  Normalizacja:
  n e = e
  n (i a) = op (i a) e
  n (
*)

Inductive Graph {A : Type} : FM A -> FM A -> Type :=
| Graph_e  : Graph e e
| Graph_i  :
    forall a : A, Graph (i a) (op (i a) e)
| Graph_op_e :
    forall x y r : FM A,
      Graph x e -> Graph y r -> Graph (op x y) r
| Graph_op_i :
    forall (x y r : FM A) (a : A),
      Graph x (i a) -> Graph y r -> Graph (op x y) (op (i a) r)
| Graph_op_op :
    forall x rx1 rx2 y r : FM A,
      Graph x (op rx1 rx2) -> Graph (op rx2 y) r ->
        Graph (op x y) (op rx1 r).

Inductive Dom {A : Type} : FM A -> Type :=
| Dom_e : Dom e
| Dom_i :
    forall a : A, Dom (i a)
| Dom_op_e :
    forall x y : FM A, Graph x e -> Dom y -> Dom (op x y)
| Dom_op_i :
    forall (x y : FM A) (a : A),
      Graph x (i a) -> Dom y -> Dom (op x y)
| Dom_op_op :
    forall x y r1 r2 : FM A,
      Graph x (op r1 r2) -> Dom (op r2 y) -> Dom (op x y).

Definition norm' :
  forall {A : Type} {x : FM A} (d : Dom x),
    {r : FM A & Graph x r}.
Proof.
  intros A x d; induction d.
  - exists e. constructor.
  - exists (op (i a) e). constructor.
  - destruct IHd as [r IH].
    exists r.
    now constructor.
  - destruct IHd as [r IH].
    exists (op (i a) r).
    now constructor 4.
  - destruct IHd as [r IH].
    exists (op r1 r).
    now econstructor 5; eassumption.
Defined.

Function size {A : Type} (x : FM A) : nat :=
match x with
| e   => 0
| i a => 1
| op (i a) e => 1
| op x y => size x + size y
end.

Lemma Graph_size :
  forall {A : Type} (x r : FM A),
    Graph x r -> size r <= size x.
Proof.
  induction 1; cbn in *; try lia.
  - destruct x, y; cbn in *; try lia.
  - destruct r, x, y; cbn in *; try lia.
  - destruct rx1, rx2, r, x, y; cbn in *; try lia.
Qed.

Fixpoint size {A : Type} (x : FM A) : nat :=
match x with
| e   => 0
| i a => 1
| op x y => 1 + size x + size y
end.

Inductive InvStep {A : Type} : FM A -> FM A -> Prop :=
| InvStep_i :
    forall a : A, InvStep (i a) (op (i a) e)
| InvStep_op_e :
    forall x y r : FM A,
      InvStep x e -> InvStep y r -> InvStep (op x y) r
| InvStep_op_i :
    forall (x y r : FM A) (a : A),
      InvStep x (i a) -> InvStep y r -> InvStep (op x y) (op (i a) r)
| InvStep_op_op :
    forall x rx1 rx2 y r : FM A,
      InvStep x (op rx1 rx2) -> InvStep (op rx2 y) r ->
        InvStep (op x y) (op rx1 r).

Lemma InvStep_size :
  forall {A : Type} (x r : FM A),
    InvStep x r -> size r <= 1 + size x.
Proof.
  induction 1; cbn in *; try lia.
  - inversion H; subst; cbn; lia.
  - inversion H; subst; cbn.
Abort.

Lemma InvStep_e :
  forall {A : Type} (x y : FM A),
    InvStep x y -> y <> e.
Proof.
  now induction 1; inversion 1.
Qed.

Lemma InvStep_irrefl :
  forall {A : Type} (x y : FM A),
    InvStep x y -> x <> y.
Proof.
  induction 1.
  - inversion 1.
  - now apply InvStep_e in H.
  - now inversion 1; subst.
  - inversion 1; subst.
Definition Step {A : Type} (x y : FM A) : Prop := InvStep y x.

Lemma wf_Graph :
  forall {A : Type},
    well_founded (@Step A).
Proof.
  intros A x.
  induction x.
  - constructor; inversion 1.
  - constructor; inversion 1; subst.
    constructor; inversion 1; subst.
    + inversion H5.
    + inversion H5.
    + inversion H3; subst; clear H3.
      unfold Step in *.
      
      
    inversion H.
    intros y [H]; inversion H; subst.
    constructor.

Fixpoint size {A : Type} (x : FM A) : nat :=
match x with
| e   => 0
| i a => 31
| op x y => 12 + size x + size y
end.

Lemma Graph_size :
  forall {A : Type} (x r : FM A),
    Graph x r -> size r <= size x.
Proof.
  induction 1; cbn in *; try lia.
  - destruct x, y; cbn in *; try lia.
  - destruct r, x, y; cbn in *; try lia.
  - destruct rx1, rx2, r, x, y; cbn in *; try lia.
Qed.

Lemma Dom_all :
  forall {A : Type} (x : FM A),
    Dom x.
Proof.
  intros A.
  apply well_founded_induction_type with (fun x y => size x < size y).
  - apply Wf_nat.well_founded_ltof.
  - destruct x; cbn; intro IH.
    + constructor.
    + constructor.
    + destruct (norm' (IH x1 ltac:(lia))) as [[] G].
      * constructor.
        -- assumption.
        -- apply IH. lia.
      * destruct (norm' (IH x2 ltac:(lia))) as [[] G'].
        -- econstructor 5; eassumption.
        -- econstructor 6.
           ++ eassumption.
           ++ apply IH. lia.
        -- econstructor 6.
           ++ eassumption.
           ++ apply IH. lia.
      * econstructor 4.
        -- eassumption.
        -- apply IH. apply Graph_size in G. cbn in *. lia.
Defined.

Definition norm {A : Type} (x : FM A) : FM A :=
match norm' (Dom_all x) with
| existT _ r _ => r
end.

Lemma norm'_correct :
  forall {A : Type} (x : FM A),
    Graph x (norm x).
Proof.
  intros A x.
  unfold norm; destruct (norm' _) as [r G].
  assumption.
Qed.

Ltac inv H := inversion H; subst; clear H.

#[global] Hint Constructors Graph : core.

Lemma norm'_det :
  forall {A : Type} {x r1 r2 : FM A},
    Graph x r1 -> Graph x r2 -> r1 = r2.
Proof.
  intros A x r1 r2 G1 G2; revert r2 G2.
  induction G1; intros.
  - inv G2. reflexivity.
  - inv G2. reflexivity.
  - inv G2; firstorder congruence.
  - inv G2.
    + firstorder congruence.
    + apply IHG1_1 in X. inv X. firstorder congruence.
    + firstorder congruence.
    + firstorder congruence.
  - inv G2; firstorder congruence.
  - inv G2; firstorder congruence.
Qed.

Lemma norm_eq :
  forall {A : Type} (x : FM A),
    norm x
      =
    match x with
    | e      => e
    | i a    => i a
    | op x y =>
      match norm x, norm y with
      | e, y'        => y'
      | op x1 x2, y' => op x1 (norm (op x2 y'))
      | x', e        => x'
      | x', y'       => op x' y'
      end
    end.
Proof.
Admitted.

Compute norm (op (op (i 5) (op (i 3) (i 10))) (i 123)).

Lemma NF_norm :
  forall {A : Type} (x : FM A),
    NF (norm x).
Proof.
  intros A x.
  unfold norm; destruct (norm' _) as [r G].
  induction G; try (try constructor; assumption; fail).
  inv IHG1.
  constructor.
  - assumption.
  - intros ->. inv G2. inv X.
    + congruence.
    + inv X1; inv H1.
Qed.

Function isNormal {A : Type} (x : FM A) : bool :=
match x with
| e   => true
| i _ => true
| op l r =>
  match l, r with
  | _  , e => false
  | i _, _ => isNormal r
  | _  , _ => false
  end
end.

Lemma isNormal_NF :
  forall {A : Type} (x : FM A),
    reflect (NF x) (isNormal x).
Proof.
  intros A x; functional induction isNormal x
  ; do 2 try constructor.
  - inversion 1. congruence.
  - inversion IHb; repeat constructor.
    + assumption.
    + intro. rewrite H1 in y. contradiction.
    + inversion 1. subst. contradiction.
  - inversion 1. subst. destruct r; contradiction.
Defined.