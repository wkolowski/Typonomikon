Require Import Recdef Lia.

Inductive Z : Type :=
| Pos  : nat -> Z
| Zero : Z
| Neg  : nat -> Z.

Function inv (k : Z) : Z :=
match k with
| Pos k' => Neg k'
| Zero   => Zero
| Neg k' => Pos k'
end.

Function succ (k : Z) : Z :=
match k with
| Pos n     => Pos (S n)
| Zero      => Pos 0
| Neg 0     => Zero
| Neg (S n) => Neg n
end.

Function pred (k : Z) : Z :=
match k with
| Pos 0     => Zero
| Pos (S n) => Pos n
| Zero      => Neg 0
| Neg n     => Neg (S n)
end.

Function add (k1 k2 : Z) : Z :=
match k1, k2 with
| Zero   , _       => k2
| _      , Zero    => k1
| Pos k1', Pos k2' => Pos (1 + k1' + k2')
| Pos k1', Neg k2' =>
  match Nat.compare k1' k2' with
  | Lt => Neg (k2' - k1' - 1)
  | Eq => Zero
  | Gt => Pos (k1' - k2' - 1)
  end
| Neg k1', Pos k2' =>
  match Nat.compare k1' k2' with
  | Lt => Pos (k2' - k1' - 1)
  | Eq => Zero
  | Gt => Neg (k1' - k2' - 1)
  end
| Neg k1', Neg k2' => Neg (1 + k1' + k2')
end.

Definition size (k : Z) : nat :=
match k with
| Zero => 0
| Pos k' => 1 + k'
| Neg k' => 1 + k'
end.

Function add' (k1 k2 : Z) {measure size k1} : Z :=
match k1 with
| Zero        => k2
| Pos 0       => succ k2
| Pos (S k1') => succ (add' (Pos k1') k2)
| Neg 0       => pred k2
| Neg (S k1') => pred (add' (Neg k1') k2)
end.
Proof.
  - intros; cbn; lia.
  - intros; cbn; lia.
Defined.

Definition sub (k1 k2 : Z) :=
  add k1 (inv k2).

Function mul (k1 k2 : Z) : Z :=
match k1, k2 with
| Zero   , _       => Zero
| _      , Zero    => Zero
| Pos k1', Pos k2' => Pos (S k1' * S k2' - 1)
| Pos k1', Neg k2' => Neg (S k1' * S k2' - 1)
| Neg k1', Pos k2' => Neg (S k1' * S k2' - 1)
| Neg k1', Neg k2' => Pos (S k1' * S k2' - 1)
end.

Function mul' (k1 k2 : Z) {measure size k1} : Z :=
match k1 with
| Zero      => Zero
| Pos 0     => k2
| Pos (S n) => add' k2 (mul' (Pos n) k2)
| Neg 0     => inv k2
| Neg (S n) => add' (inv k2) (mul' (Neg n) k2)
end.
Proof.
  - intros; cbn; lia.
  - intros; cbn; lia.
Defined.

Function min (k1 k2 : Z) : Z :=
match k1, k2 with
| Neg n1, Neg n2 => Neg (Nat.max n1 n2)
| Neg n1, _      => Neg n1
| _     , Neg n2 => Neg n2
| Zero  , _      => Zero
| _     , Zero   => Zero
| Pos n1, Pos n2 => Pos (Nat.min n1 n2)
end.

Function max (k1 k2 : Z) : Z :=
match k1, k2 with
| Pos n1, Pos n2 => Pos (Nat.max n1 n2)
| Pos _ , _      => k1
| _     , Pos _  => k2
| Zero  , _      => Zero
| _     , Zero   => Zero
| Neg n1, Neg n2 => Neg (Nat.min n1 n2)
end.

Compute add (Pos 5) (Pos 6).
Compute add (Pos 5) (Neg 2).
Compute add (Pos 2) (Neg 3).
Compute add (Neg 2) (Pos 5).
Compute add (Neg 2) (Pos 3).

Compute mul (Neg 1) (Pos 1).
Compute mul (Neg 1) (Neg 1).

Compute min (Pos 5) (Pos 6).
Compute min (Pos 5) (Neg 5).
Compute min (Neg 5) (Neg 6).

Lemma inv_inv :
  forall k : Z,
    inv (inv k) = k.
Proof.
  destruct k; reflexivity.
Qed.

Lemma inv_succ :
  forall k : Z,
    inv (succ k) = pred (inv k).
Proof.
  intros k; functional induction (succ k); cbn; reflexivity.
Qed.

Lemma inv_pred :
  forall k : Z,
    inv (pred k) = succ (inv k).
Proof.
  intros k; functional induction (pred k); cbn; reflexivity.
Qed.

Lemma succ_pred :
  forall k : Z,
    succ (pred k) = k.
Proof.
  intros k; functional induction (pred k); cbn; reflexivity.
Qed.

Lemma pred_succ :
  forall k : Z,
    pred (succ k) = k.
Proof.
  intros k; functional induction (succ k); cbn; reflexivity.
Qed.

Lemma add_Zero_l :
  forall k : Z,
    add Zero k = k.
Proof.
  reflexivity.
Qed.

Lemma add_Zero_r :
  forall k : Z,
    add k Zero = k.
Proof.
  destruct k; reflexivity.
Qed.

Lemma add_comm :
  forall k1 k2 : Z,
    add k1 k2 = add k2 k1.
Proof.
  intros k1 k2; functional induction (add k1 k2)
  ; cbn; rewrite ?add_Zero_r, 1?PeanoNat.Nat.compare_antisym, ?e1; cbn
  ; f_equal; reflexivity + lia.
Qed.

Lemma add_inv :
  forall k1 k2 : Z,
    add (inv k1) (inv k2) = inv (add k1 k2).
Proof.
  intros k1 k2; functional induction (add k1 k2)
  ; cbn; rewrite ?add_Zero_r, ?e1
  ; f_equal; reflexivity + lia.
Qed.

Lemma add_assoc :
  forall k1 k2 k3 : Z,
    add (add k1 k2) k3 = add k1 (add k2 k3).
Proof.
  intros k1 k2 k3; functional induction (add k1 k2)
  ; rewrite ?add_Zero_l; try reflexivity.
Admitted.

Lemma add'_inv :
  forall k1 k2 : Z,
    add' (inv k1) (inv k2) = inv (add' k1 k2).
Proof.
  intros k1 k2; functional induction (add' k1 k2)
  ; cbn; rewrite ?add'_Zero_r.
  - reflexivity.
  - rewrite inv_succ; reflexivity.
  - rewrite add'_equation, inv_succ, <- IHz; cbn; reflexivity.
  - rewrite inv_pred; reflexivity.
  - rewrite add'_equation, inv_pred, <- IHz; cbn; reflexivity.
Qed.

Lemma inv_add' :
  forall k1 k2 : Z,
    inv (add' k1 k2) = add' (inv k1) (inv k2).
Proof.
  intros k1 k2; rewrite add'_inv; reflexivity.
Qed.

Lemma add'_Zero_l :
  forall k : Z,
    add' Zero k = k.
Proof.
  reflexivity.
Qed.

Lemma add'_Zero_r :
  forall k : Z,
    add' k Zero = k.
Proof.
  destruct k as [n | | n]; cycle 1.
  - reflexivity.
  - induction n as [| n']; cbn.
    + reflexivity.
    + rewrite add'_equation, IHn'; cbn; reflexivity.
  - induction n as [| n']; cbn.
    + reflexivity.
    + rewrite add'_equation, IHn'; cbn; reflexivity.
Qed.

Lemma add'_Pos_r :
  forall (k : Z) (n : nat),
    add' k (Pos n)
      =
    match n with
    | 0    => succ k
    | S n' => succ (add' k (Pos n'))
    end.
Proof.
  intros [m | | m] n; cbn; cycle 1.
  - destruct n; reflexivity.
  - induction m as [| m']; destruct n as [| n']; cbn.
    + reflexivity.
    + destruct n'; reflexivity.
    + rewrite add'_equation, IHm'. destruct m'; reflexivity.
    + rewrite !(add'_equation (Neg (S m'))), IHm', pred_succ, succ_pred; reflexivity.
  - induction m as [| m']; destruct n as [| n']; cbn.
    + reflexivity.
    + reflexivity.
    + rewrite add'_equation, IHm'; cbn; reflexivity.
    + rewrite !(add'_equation (Pos (S m'))), IHm'; reflexivity.
Qed.

Lemma add'_Neg_r :
  forall (k : Z) (n : nat),
    add' k (Neg n)
      =
    match n with
    | 0    => pred k
    | S n' => pred (add' k (Neg n'))
    end.
Proof.
  intros k n.
  rewrite <- inv_inv, inv_add' at 1; cbn.
  rewrite add'_Pos_r.
  destruct n.
  - rewrite inv_succ, inv_inv; reflexivity.
  - rewrite inv_succ, inv_add', inv_inv; cbn; reflexivity.
Qed.

Lemma add'_succ_l :
  forall k1 k2 : Z,
    add' (succ k1) k2 = succ (add' k1 k2).
Proof.
  intros k1 k2; functional induction (succ k1); cbn.
  - rewrite add'_equation; reflexivity.
  - reflexivity.
  - rewrite succ_pred; reflexivity.
  - rewrite (add'_equation (Neg (S n))), succ_pred; reflexivity.
Qed.

Lemma add'_pred_l :
  forall k1 k2 : Z,
    add' (pred k1) k2 = pred (add' k1 k2).
Proof.
  intros k1 k2; functional induction (pred k1); cbn.
  - rewrite pred_succ; reflexivity.
  - rewrite (add'_equation (Pos (S n))), pred_succ; reflexivity.
  - reflexivity.
  - rewrite add'_equation; reflexivity.
Qed.

Lemma add'_comm :
  forall k1 k2 : Z,
    add' k1 k2 = add' k2 k1.
Proof.
  intros k1 k2; functional induction (add' k1 k2).
  - rewrite add'_Zero_r; reflexivity.
  - rewrite add'_Pos_r; reflexivity.
  - rewrite IHz, (add'_Pos_r k2 (S k1')); reflexivity.
  - rewrite add'_Neg_r; reflexivity.
  - rewrite IHz, (add'_Neg_r k2 (S k1')); reflexivity.
Qed.

Lemma add'_assoc :
  forall k1 k2 k3 : Z,
    add' (add' k1 k2) k3 = add' k1 (add' k2 k3).
Proof.
  intros k1 k2 k3; functional induction (add' k1 k2); cbn.
  - reflexivity.
  - rewrite add'_succ_l; reflexivity.
  - rewrite add'_succ_l, IHz, (add'_equation (Pos (S k1'))); reflexivity.
  - rewrite add'_pred_l; reflexivity.
  - rewrite add'_pred_l, IHz, (add'_equation (Neg (S k1'))); reflexivity.
Qed.

Lemma sub_diag :
  forall k : Z,
    add' k (inv k) = Zero.
Proof.
  intros [n | | n]; cbn; cycle 1.
  - reflexivity.
  - induction n as [| n']; cbn in *.
    + reflexivity.
    + rewrite add'_equation, add'_Pos_r, IHn', pred_succ; reflexivity.
  - induction n as [| n']; cbn in *.
    + reflexivity.
    + rewrite add'_equation, add'_Neg_r, IHn', succ_pred; reflexivity.
Qed.

Lemma mul_Zero_r :
  forall k : Z,
    mul k Zero = Zero.
Proof.
  destruct k; reflexivity.
Qed.

Lemma mul_comm :
  forall k1 k2 : Z,
    mul k1 k2 = mul k2 k1.
Proof.
  intros k1 k2; functional induction (mul k1 k2)
  ; cbn; rewrite ?mul_Zero_r
  ; f_equal; reflexivity + lia.
Qed.

Lemma mul_assoc :
  forall k1 k2 k3 : Z,
    mul (mul k1 k2) k3 = mul k1 (mul k2 k3).
Proof.
  intros k1 k2 k3; functional induction (mul k1 k2)
  ; cbn; rewrite ?mul_Zero_r
  ; try reflexivity
  ; destruct k3 as [k3' | | k3']
  ; cbn; rewrite ?mult_n_Sm
  ; f_equal; try reflexivity.
  all: cbn; rewrite <- ?mult_n_Sm, PeanoNat.Nat.sub_0_r.
Abort.

Lemma inv_mul'_r :
  forall k1 k2 : Z,
    inv (mul' k1 k2) = mul' k1 (inv k2).
Proof.
  intros k1 k2. functional induction (mul' k1 k2); cbn.
  1-2: reflexivity.
  - rewrite inv_add', IHz, (mul'_equation (Pos (S n))); reflexivity.
  - reflexivity.
  - rewrite inv_add', IHz, (mul'_equation (Neg (S n))); reflexivity.
Qed.

Lemma mul'_Zero_r :
  forall k : Z,
    mul' k Zero = Zero.
Proof.
  destruct k as [n | | n]; cbn; cycle 1.
  - reflexivity.
  - induction n as [| n']; cbn.
    + reflexivity.
    + rewrite mul'_equation, IHn'; cbn; reflexivity.
  - induction n as [| n']; cbn.
    + reflexivity.
    + rewrite mul'_equation, IHn'; cbn; reflexivity.
Qed.

Lemma mul'_Pos_r :
  forall (k : Z) (n : nat),
    mul' k (Pos n)
      =
    match n with
    | 0    => k
    | S n' => add' k (mul' k (Pos n'))
    end.
Proof.
  intros [m | | m] n; cycle 1.
  - destruct n; reflexivity.
  - induction m as [| m'].
    + rewrite mul'_equation. destruct n; reflexivity.
    + rewrite mul'_equation, IHm'. unfold inv. destruct n as [| n'].
      * reflexivity.
      * rewrite (mul'_equation (Neg (S m'))); unfold inv.
        rewrite (add'_equation (Neg (S n'))), (add'_equation (Neg (S m'))); f_equal.
        rewrite <- !add'_assoc, (add'_comm (Neg n') (Neg m')).
        reflexivity.
  - induction m as [| m'].
    + rewrite mul'_equation. destruct n; reflexivity.
    + rewrite mul'_equation, IHm'. destruct n as [| n'].
      * reflexivity.
      * rewrite (mul'_equation (Pos (S m'))); unfold inv.
        rewrite (add'_equation (Pos (S n'))), (add'_equation (Pos (S m'))); f_equal.
        rewrite <- !add'_assoc, (add'_comm (Pos n') (Pos m')).
        reflexivity.
Qed.

Lemma mul'_Neg_r :
  forall (k : Z) (n : nat),
    mul' k (Neg n)
      =
    match n with
    | 0    => inv k
    | S n' => add' (inv k) (mul' k (Neg n'))
    end.
Proof.
  intros k n.
  rewrite <- inv_inv, inv_mul'_r at 1; cbn.
  rewrite mul'_Pos_r.
  destruct n as [| n']; cbn.
  - reflexivity.
  - rewrite inv_add', inv_mul'_r; cbn; reflexivity.
Qed.

Lemma mul'_comm :
  forall k1 k2 : Z,
    mul' k1 k2 = mul' k2 k1.
Proof.
  intros k1 k2; functional induction (mul' k1 k2)
  ; cbn; rewrite ?mul'_Zero_r.
  - reflexivity.
  - rewrite mul'_Pos_r; reflexivity.
  - rewrite mul'_Pos_r, IHz; reflexivity.
  - rewrite mul'_Neg_r; reflexivity.
  - rewrite mul'_Neg_r, IHz; reflexivity.
Qed.

Lemma mul'_succ_l :
  forall k1 k2 : Z,
    mul' (succ k1) k2 = add' k2 (mul' k1 k2).
Proof.
  intros k1 k2.
  functional induction (succ k1); cbn.
  - rewrite mul'_equation; reflexivity.
  - rewrite add'_Zero_r; reflexivity.
  - rewrite sub_diag; reflexivity.
  - rewrite (mul'_equation (Neg (S n))), <- add'_assoc, sub_diag; cbn; reflexivity.
Qed.

Lemma mul'_pred_l :
  forall k1 k2 : Z,
    mul' (pred k1) k2 = add' (inv k2) (mul' k1 k2).
Proof.
  intros k1 k2.
  functional induction (pred k1); cbn.
  - rewrite add'_comm, sub_diag; reflexivity.
  - rewrite (mul'_equation (Pos (S n))), <- add'_assoc, (add'_comm (inv _)), sub_diag; cbn.
    reflexivity.
  - rewrite add'_Zero_r; reflexivity.
  - rewrite mul'_equation. reflexivity.
Qed.

Lemma mul'_add'_l :
  forall k1 k2 k3 : Z,
    mul' (add' k1 k2) k3 = add' (mul' k1 k3) (mul' k2 k3).
Proof.
  intros k1 k2 k3.
  functional induction (add' k1 k2); cbn.
  - reflexivity.
  - rewrite mul'_succ_l; reflexivity.
  - rewrite mul'_succ_l, (mul'_equation (Pos (S k1'))), add'_assoc, IHz; reflexivity.
  - rewrite mul'_pred_l; reflexivity.
  - rewrite mul'_pred_l, (mul'_equation (Neg (S k1'))), add'_assoc, IHz; reflexivity.
Qed.

Lemma mul'_assoc :
  forall k1 k2 k3 : Z,
    mul' (mul' k1 k2) k3 = mul' k1 (mul' k2 k3).
Proof.
  intros k1 k2 k3; functional induction (mul' k1 k2); cbn.
  1-2: reflexivity.
  - rewrite (mul'_equation (Pos (S n))), mul'_add'_l, IHz; reflexivity.
  - rewrite mul'_comm, <- inv_mul'_r, mul'_comm; reflexivity.
  - rewrite (mul'_equation (Neg (S n))), (mul'_comm k2), inv_mul'_r, (mul'_comm _ (inv _)),
            mul'_add'_l, (mul'_comm (inv _)), IHz, (mul'_comm k2 k3).
    reflexivity.
Qed.

Lemma min_comm :
  forall k1 k2 : Z,
    min k1 k2 = min k2 k1.
Proof.
  intros k1 k2; functional induction (min k1 k2)
  ; cbn; f_equal; try (reflexivity + lia).
  - destruct k2; cbn; reflexivity + contradiction.
  - destruct k1; cbn; reflexivity + contradiction.
  - destruct k2; cbn; reflexivity + contradiction.
  - destruct k1; cbn; reflexivity + contradiction.
Qed.

Lemma min_inv :
  forall k1 k2 : Z,
    min (inv k1) (inv k2) = inv (max k1 k2).
Proof.
  intros k1 k2; functional induction (max k1 k2); cbn; f_equal.
  - destruct k2; cbn in *; reflexivity + contradiction.
  - destruct k1; cbn in *; reflexivity + contradiction.
  - destruct k2; cbn in *; reflexivity + contradiction.
  - destruct k1; cbn in *; reflexivity + contradiction.
Qed.

Lemma inv_min :
  forall k1 k2 : Z,
    inv (min k1 k2) = max (inv k1) (inv k2).
Proof.
  intros k1 k2.
  rewrite <- inv_inv, <- min_inv, !inv_inv.
  reflexivity.
Qed.