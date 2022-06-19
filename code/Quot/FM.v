Require Import Recdef StrictProp Bool Lia.

Inductive FM (A : Type) : Type :=
| e  : FM A
| i  : A -> FM A
| op : FM A -> FM A -> FM A.

Arguments e  {A}.
Arguments i  {A} _.
Arguments op {A} _ _.

Inductive NF {A : Type} : FM A -> Prop :=
| Ce   : NF e
| Ci   : forall a : A, NF (i a)
| Cop1 : forall (a : A) (y : FM A), NF y -> y <> e -> NF (op (i a) y).

Record FM' (A : Type) : Type :=
{
    cf : FM A;
    NF_cf : NF cf;
}.

Inductive Graph {A : Type} : FM A -> FM A -> Type :=
| Graph_e  : Graph e e
| Graph_i  :
    forall a : A, Graph (i a) (i a)
| Graph_op_e :
    forall x y r : FM A,
      Graph x e -> Graph y r -> Graph (op x y) r
| Graph_op_op :
    forall x rx1 rx2 y r : FM A,
      Graph x (op rx1 rx2) -> Graph (op rx2 y) r ->
        Graph (op x y) (op rx1 r)
| Graph_op_e' :
    forall (x y : FM A) (a : A),
      Graph x (i a) -> Graph y e -> Graph (op x y) (i a)
| Graph_op :
    forall (x y r : FM A) (a : A),
      Graph x (i a) -> Graph y r -> r <> e -> Graph (op x y) (op (i a) r).

Inductive Dom {A : Type} : FM A -> Type :=
| Dom_e  : Dom e
| Dom_i  :
    forall a : A, Dom (i a)
| Dom_op_e :
    forall x y : FM A, Graph x e -> Dom y -> Dom (op x y)
| Dom_op_op :
    forall x y r1 r2 : FM A,
      Graph x (op r1 r2) -> Dom (op r2 y) -> Dom (op x y)
| Dom_op_e' :
    forall (x y : FM A) (a : A),
      Graph x (i a) -> Graph y e -> Dom (op x y)
| Dom_op :
    forall (x y : FM A) (a : A),
      Graph x (i a) -> Dom y -> Dom (op x y).

Definition norm' :
  forall {A : Type} {x : FM A} (d : Dom x),
    {r : FM A & Graph x r}.
Proof.
  intros A x d.
  induction d.
  - exists e. constructor.
  - exists (i a). constructor.
  - destruct IHd as [r IH]. exists r. constructor; assumption.
  - destruct IHd as [r IH]. exists (op r1 r). econstructor 4; eassumption.
  - exists (i a). constructor 5; assumption.
  - destruct IHd as [r IH]. destruct r.
    + exists (i a). constructor 5; assumption.
    + exists (op (i a) (i a0)). constructor 6; try assumption. inversion 1.
    + exists (op (i a) (op r1 r2)). constructor 6; try assumption. inversion 1.
Defined.

Fixpoint size {A : Type} (x : FM A) : nat :=
match x with
| e   => 0
| i a => 1
| op x y => 1 + size x + size y
end.

Lemma Graph_size :
  forall {A : Type} (x r : FM A),
    Graph x r -> size r <= size x.
Proof.
  induction 1; cbn in *; try lia.
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
  intros.
  unfold norm.
  destruct (norm' _).
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

(* Functional Scheme norm_ind' := Induction for norm Sort SProp. *)

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