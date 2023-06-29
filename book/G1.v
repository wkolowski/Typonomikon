(** * G1: Typy ilorazowe i smart konstruktory [TODO] *)

Require Import Recdef StrictProp Bool Lia.

(** * Liczby całkowite (TODO) *)

Module Z_pair.

Inductive Z : Type :=
| pair : nat -> nat -> Z.

Function norm' (n m : nat) : nat * nat :=
match n, m with
| S n', S m' => norm' n' m'
| _   , _    => (n, m)
end.

Definition norm (k : Z) : Z :=
match k with
| pair n m => let (n', m') := norm' n m in pair n' m'
end.

Record Z' : Type :=
{
  num : Z;
  norm_num : Squash (norm num = num);
}.

Lemma norm'_idempotent :
  forall n m n' m' : nat,
    norm' n m = (n', m') ->
      norm' n' m' = (n', m').
Proof.
  intros n m n' m' Hnorm.
  functional induction norm' n m.
  - apply IHp; assumption.
  - destruct n, m; inversion Hnorm; subst; cbn.
    1-3: reflexivity.
    contradiction.
Qed.

Lemma norm_norm :
  forall k : Z,
    norm (norm k) = norm k.
Proof.
  intros [n m].
  unfold norm.
  destruct (norm' n m) eqn: Heq1.
  destruct (norm' n0 n1) eqn: Heq2.
  erewrite norm'_idempotent in Heq2.
  - congruence.
  - eassumption.
Qed.

End Z_pair.

(** * Liczby całkowite inaczej (TODO) *)

Module Z_peano.

Ltac inv H := inversion H; subst; clear H; auto.

Inductive Z : Type :=
| z : Z
| s : Z -> Z
| p : Z -> Z.

Inductive NF : Z -> Prop :=
| NF_z  : NF z
| NF_sz : NF (s z)
| NF_s  : forall k : Z, NF (s k) -> NF (s (s k))
| NF_pz : NF (p z)
| NF_p  : forall k : Z, NF (p k) -> NF (p (p k)).

#[global] Hint Constructors NF : core.

Function isNormal (k : Z) : bool :=
match k with
| z    => true
| s k' =>
  match k' with
  | p _ => false
  | _   => isNormal k'
  end
| p k' =>
  match k' with
  | s _ => false
  | _   => isNormal k'
  end
end.

Function norm (k : Z) : Z :=
match k with
| z    => z
| s k' =>
  match norm k' with
  | p k'' => k''
  | k''   => s k''
  end
| p k' =>
  match norm k' with
  | s k'' => k''
  | k''   => p k''
  end
end.

Compute norm (s (s (s (p (p (p z)))))).
(* ===> = z : Z *)

Definition z' : Z := z.

Definition s' (k : Z) : Z :=
match k with
| z    => s z
| s k' => s (s k')
| p k' => k'
end.

Definition p' (k : Z) : Z :=
match k with
| z    => p z
| s k' => k'
| p k' => p (p k')
end.

Function norm' (k : Z) : Z :=
match k with
| z => z'
| s k' => s' (norm' k')
| p k' => p' (norm' k')
end.

Function abs (k : Z) : Z :=
match k with
| z => z
| s k' => s k'
| p k' => s (abs k')
end.

Function inv (k : Z) : Z :=
match k with
| z    => z
| s k' => p (inv k')
| p k' => s (inv k')
end.

Function add (k l : Z) : Z :=
match k with
| z => l
| s k' => s (add k' l)
| p k' => p (add k' l)
end.

Function sub (k l : Z) : Z :=
match l with
| z    => k
| s l' => p (sub k l')
| p l' => s (sub k l')
end.

Function mul (k l : Z) : Z :=
match k with
| z    => z
| s k' => add l (mul k' l)
| p k' => sub (mul k' l) l
end.

Function min (k1 k2 : Z) : Z :=
match k1, k2 with
| z    , p _   => k2
| z    , _     => z
| s k1', s k2' => s (min k1' k2')
| s k1', _     => k2
| p k1', p k2' => p (min k1' k2')
| p k1', _     => k1
end.

Definition max (k1 k2 : Z) : Z := min (inv k1) (inv k2).

Function fromNat (n : nat) : Z :=
match n with
| 0    => z
| S n' => s (fromNat n')
end.

Function succNegative (n : nat) : Z :=
match n with
| 0    => p z
| S n' => p (succNegative n')
end.

Compute abs (min (fromNat 5) (fromNat 6)).
Compute abs (min (succNegative 7) (fromNat 5)).

Lemma isNormal_spec :
  forall k : Z, reflect (NF k) (isNormal k).
Proof.
  intros k; functional induction isNormal k
  ; repeat constructor.
  - intro H; inv H.
  - inv IHb; repeat constructor.
    + inv H0; contradiction.
    + intro H1; inv H1.
  - intro H; inv H.
  - inv IHb; repeat constructor.
    + inv H0; contradiction.
    + intro H1; inv H1.
Defined.

Lemma NF_norm :
  forall k : Z,
    NF (norm k).
Proof.
  intros k; functional induction norm k.
  - constructor.
  - rewrite e0 in IHz0; inv IHz0.
  - destruct (norm k'); intuition.
  - rewrite e0 in IHz0; inv IHz0.
  - destruct (norm k'); intuition.
Qed.

Lemma isNormal_norm :
  forall k : Z,
    isNormal (norm k) = true.
Proof.
  intros k. destruct (isNormal_spec (norm k)).
  - reflexivity.
  - contradiction n. apply NF_norm.
Qed.

Lemma norm_NF :
  forall k : Z,
    NF k -> norm k = k.
Proof.
  induction 1.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - rewrite norm_equation, IHNF; reflexivity.
  - cbn; reflexivity.
  - rewrite norm_equation, IHNF; reflexivity.
Qed.

Lemma norm_NF_conv :
  forall k : Z,
    norm k = k -> NF k.
Proof.
  intros k Heq.
  destruct (isNormal_spec k).
  - assumption.
  - rewrite <- Heq. apply NF_norm.
Qed.

Lemma norm_NF' :
  forall k : Z,
    NF k <-> norm k = k.
Proof.
  split.
  - apply norm_NF.
  - apply norm_NF_conv.
Qed.

Lemma norm_norm :
  forall k : Z,
    norm (norm k) = norm k.
Proof.
  intros k.
  apply norm_NF.
  apply NF_norm.
Qed.

Lemma norm_isNormal :
  forall k : Z,
    isNormal k = true -> norm k = k.
Proof.
  intros k; functional induction norm k; cbn; intro Heq.
  2-5: destruct k'; cbn in *; intuition congruence.
  reflexivity.
Qed.

Lemma norm'_norm :
  forall k : Z,
    norm' k = norm k.
Proof.
  reflexivity.
Qed.

Lemma abs_abs :
  forall k : Z, abs (abs k) = abs k.
Proof.
  induction k; cbn; reflexivity.
Qed.

Lemma add_z_l :
  forall k : Z,
    add z k = k.
Proof.
  reflexivity.
Qed.

Lemma add_z_r :
  forall k : Z,
    add k z = k.
Proof.
  induction k; cbn; rewrite ?IHk; reflexivity.
Qed.

Lemma add_s_r :
  forall k l : Z,
    norm (add k (s l)) = norm (s (add k l)).
Proof.
  induction k; cbn; intros l.
  - reflexivity.
  - rewrite IHk. cbn. reflexivity.
  - rewrite IHk. cbn. destruct (norm (add k l)).
    + reflexivity.
    + destruct z0; try reflexivity.
Restart.
  intros.
  functional induction (add k l); cbn; [easy | ..].
  - now rewrite IHz0.
  - rewrite IHz0.
    destruct (add k' l); cbn; [easy | ..].
Admitted.

Lemma add_p_r :
  forall k l : Z,
    norm (add k (p l)) = norm (p (add k l)).
Proof.
  induction k; cbn; intros l.
  - reflexivity.
  - rewrite IHk. cbn. destruct (norm (add k l)).
Admitted.

Lemma add_s_r' :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> add k (s l) = s (add k l).
Proof.
  intros k l HN1 HN2.
Admitted.

Lemma add_p_r' :
  forall k l : Z,
    norm (add k (p l)) = norm (p (add k l)).
Proof.
  induction k as [| k' | k']; cbn; intros.
Admitted.

Lemma add_comm :
  forall k l : Z,
    norm (add k l) = norm (add l k).
Proof.
  induction k; cbn; intros.
  - rewrite add_z_r. reflexivity.
  - rewrite add_s_r, IHk; cbn; reflexivity.
  - rewrite add_p_r, IHk; cbn; reflexivity.
Qed.

Lemma sub_spec :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> sub k l = add (inv l) k.
Proof.
  induction l; cbn; intros.
  - reflexivity.
  - rewrite IHl; intuition. destruct l; congruence.
  - rewrite IHl; intuition. destruct l; congruence.
Qed.

Lemma norm_sub :
  forall k l : Z,
    norm (sub k l) = norm (add (inv l) k).
Proof.
  induction l; cbn; rewrite ?IHl; reflexivity.
Qed.

Lemma abs_inv :
  forall k : Z,
    isNormal k = true -> abs (inv k) = abs k.
Proof.
  induction k; cbn; intros.
  - reflexivity.
  - destruct k; cbn in *.
    + reflexivity.
    + rewrite (IHk H); reflexivity.
    + congruence.
  - destruct k; cbn in *.
    + reflexivity.
    + congruence.
    + rewrite (IHk H); reflexivity.
Qed.

Lemma abs_inv' :
  forall k : Z,
    NF k ->
      norm (abs (inv k)) = norm (abs k).
Proof.
  intros k HNF.
  rewrite abs_inv.
  - reflexivity.
  - destruct (isNormal_spec k); intuition.
Qed.

Lemma NF_min :
  forall k1 k2 : Z,
    NF k1 -> NF k2 -> NF (min k1 k2).
Proof.
  intros k1 k2.
  functional induction min k1 k2; cbn; intros H1 H2.
  - assumption.
  - assumption.
  - inversion H1; inversion H2; subst; clear H1 H2; cbn; constructor.
    apply IHz0; assumption.
  - assumption.
  - inversion H1; inversion H2; subst; clear H1 H2; cbn; constructor.
    1-2: assumption.
    apply IHz0; assumption.
  - assumption.
Qed.

Module Z_NF.

Record Z' : Type :=
{
  canonical : Z;
  NF_canonical : Squash (NF canonical);
}.

End Z_NF.

Module Z_norm.

Record Z' : Type :=
{
  canonical : Z;
  norm_canonical : Squash (norm canonical = canonical);
}.

End Z_norm.

Module Z_isNormal.

Record Z' : Type :=
{
  canonical : Z;
  isNormal_canonical : Squash (isNormal canonical = true);
}.

End Z_isNormal.

Module Z_SmartConstructors.

Record Z' : Type :=
{
  canonical : Z;
  isNormal_canonical : Squash (isNormal canonical = true);
}.

Function abs' (k : Z) : Z :=
match k with
| z    => z
| s k' => s k'
| p k' => s (abs' k')
end.

Function inv' (k : Z) : Z :=
match k with
| z    => z'
| s k' => p' (inv' k')
| p k' => s' (inv' k')
end.

Function add' (k l : Z) : Z :=
match k with
| z => l
| s k' => s' (add' k' l)
| p k' => p' (add' k' l)
end.

Function sub' (k l : Z) : Z :=
match l with
| z    => k
| s l' => p' (sub' k l')
| p l' => s' (sub' k l')
end.

Lemma abs'_abs' :
  forall k : Z, abs' (abs' k) = abs k.
Proof.
  induction k; cbn; reflexivity.
Qed.

Lemma abs'_inv :
  forall k : Z,
    isNormal k = true -> abs' (inv k) = abs' k.
Proof.
  induction k; cbn; intros.
    reflexivity.
    destruct k; cbn in *.
      reflexivity.
Admitted.

Lemma abs'_inv' :
  forall k : Z,
    isNormal k = true -> abs' (inv' k) = abs' k.
Proof.
  induction k; cbn; intros; [easy | ..].
  - destruct k; cbn; [easy | ..].
Admitted.

End Z_SmartConstructors.

Module Z_wut.

Definition succ (k : Z) : Z := norm (s k).
Definition pred (k : Z) : Z := norm (p k).

Definition inv' (k : Z) : Z := norm (inv k).

Definition add' (k1 k2 : Z) : Z := norm (add k1 k2).

Function abs (k : Z) : nat :=
match k with
| z    => 0
| s k' => S (abs k')
| p k' => S (abs k')
end.

Definition abs' (k : Z) : nat := abs (norm k).

Definition sub' (k1 k2 : Z) : Z := norm (sub k1 k2).

Definition mul' (k1 k2 : Z) : Z := norm (mul k1 k2).

Definition min' (k1 k2 : Z) : Z := min (norm k1) (norm k2).

Lemma norm_inv' :
  forall k : Z,
    norm (inv' k) = inv' k.
Proof.
  intros k.
  unfold inv'.
  rewrite norm_norm.
  reflexivity.
Qed.

Lemma norm_add' :
  forall k1 k2 : Z,
    norm (add' k1 k2) = add' k1 k2.
Proof.
  intros k1 k2.
  unfold add'.
  rewrite norm_norm.
  reflexivity.
Qed.

End Z_wut.

End Z_peano.

(** * Wolne monoidy (TODO) *)

(* begin hide *)
(* TODO: Wolne monoidy nie mogą pojawić się przed wprowadzeniem do algebry. *)
(* end hide *)

Module FM.

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
  intros A x d; induction d.
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

End FM.

(** ** Wolniejsze monoidy (TODO) *)

Module BetterFM.

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
  n (op l r) =
    match n l with
    | e           => n r
    | op (i a) l2 => op (i a) (n (op l2 r))
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

Fixpoint size' {A : Type} (x : FM A) : nat :=
match x with
| e   => 0
| i a => 1
| op x y => 1 + size' x + size' y
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
Abort.

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
Abort.

Fixpoint size'' {A : Type} (x : FM A) : nat :=
match x with
| e   => 0
| i a => 31
| op x y => 12 + size'' x + size'' y
end.

Lemma Dom_all :
  forall {A : Type} (x : FM A),
    Dom x.
Proof.
  intros A.
  apply well_founded_induction_type with (fun x y => size' x < size' y).
  - apply Wf_nat.well_founded_ltof.
  - destruct x; cbn; intro IH.
    + constructor.
    + constructor.
    + destruct (norm' (IH x1 ltac:(lia))) as [[] G].
      * constructor.
        -- assumption.
        -- apply IH. lia.
      * destruct (norm' (IH x2 ltac:(lia))) as [[] G'].
Admitted.

End BetterFM.