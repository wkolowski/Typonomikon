(* 
Lemma succ_pred :
  forall k : Z,
    succ (pred k) = k.
Proof.
Admitted.

Lemma pred_succ :
  forall k : Z,
    pred (succ k) = k.
Proof.
Admitted.

Lemma add_0_l :
  forall k : Z,
    add 0 k = k.
Proof.
  reflexivity.
Admitted.

Lemma add_0_r :
  forall k : Z,
    add k 0 = k.
Proof.
  destruct k; reflexivity.
Admitted.

Lemma add_succ_l :
  forall k1 k2 : Z,
    add (succ k1) k2 = succ (add k1 k2).
Proof.
Admitted.

Lemma add_pred_l :
  forall k1 k2 : Z,
    add (pred k1) k2 = pred (add k1 k2).
Proof.
Admitted.

Lemma add_comm :
  forall k1 k2 : Z,
    add k1 k2 = add k2 k1.
Proof.
Admitted.

Lemma add_assoc :
  forall k1 k2 k3 : Z,
    add (add k1 k2) k3 = add k1 (add k2 k3).
Proof.
Admitted.

Lemma sub_diag :
  forall k : Z,
    add k (inv k) = 0.
Proof.
Admitted.

Lemma mul_0_l :
  forall k : Z,
    mul 0 k = 0.
Proof.
Admitted.

Lemma mul_0_r :
  forall k : Z,
    mul k 0 = 0.
Proof.
Admitted.

Lemma mul_succ_l :
  forall k1 k2 : Z,
    mul (succ k1) k2 = add k2 (mul k1 k2).
Proof.
Admitted.

Lemma mul_succ_r :
  forall k1 k2 : Z,
    mul k1 (succ k2) = add (mul k1 k2) k1.
Proof.
Admitted.

Lemma mul_pred_l :
  forall k1 k2 : Z,
    mul (pred k1) k2 = sub (mul k1 k2) k2.
Proof.
Admitted.

Lemma mul_pred_r :
  forall k1 k2 : Z,
    mul k1 (pred k2) = sub (mul k1 k2) k1.
Proof.
Admitted.

Lemma mul_comm :
  forall k1 k2 : Z,
    mul k1 k2 = mul k2 k1.
Proof.
Admitted.

Lemma mul_assoc :
  forall k1 k2 k3 : Z,
    mul (mul k1 k2) k3 = mul k1 (mul k2 k3).
Proof.
Abort.

Lemma mul_add_l :
  forall k1 k2 k3 : Z,
    mul (add k1 k2) k3 = add (mul k1 k3) (mul k2 k3).
Proof.
Admitted.

Lemma mul_add_r :
  forall k1 k2 k3 : Z,
    mul k1 (add k2 k3) = add (mul k1 k2) (mul k1 k3).
Proof.
Admitted.

Lemma min_comm :
  forall k1 k2 : Z,
    min k1 k2 = min k2 k1.
Proof.
Admitted.

Lemma min_assoc :
  forall k1 k2 k3 : Z,
    min (min k1 k2) k3 = min k1 (min k2 k3).
Proof.
Admitted.

Lemma max_comm :
  forall k1 k2 : Z,
    max k1 k2 = maxx k2 k1.
Proof.
Admitted.

Lemma max_assoc :
  forall k1 k2 k3 : Z,
    max (max k1 k2) k3 = max k1 (max k2 k3).
Proof.
Admitted.

 *)