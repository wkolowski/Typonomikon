Require Import Recdef Lia.

Inductive Z : Type :=
| Pos  : nat -> Z
| Zero : Z
| Neg  : nat -> Z.

Definition inv (k : Z) : Z :=
match k with
| Pos k' => Neg k'
| Zero   => Zero
| Neg k' => Pos k'
end.

Definition succ (k : Z) : Z :=
match k with
| Pos n     => Pos (S n)
| Zero      => Pos 0
| Neg 0     => Zero
| Neg (S n) => Neg n
end.

Definition pred (k : Z) : Z :=
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
| Pos k1', Pos k2' => Pos (2 + k1' + k2')
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
| Neg k1', Neg k2' => Neg (2 + k1' + k2')
end.

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
  ; cbn; rewrite ?add_Zero_r.
Abort.

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
  ; f_equal.
Abort.

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
  intros k1 k2; functional induction (max k1 k2)
  ; cbn
  ; f_equal.
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

