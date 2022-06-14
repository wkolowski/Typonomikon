Require Import Recdef Lia.

From Typonomikon Require Import BinaryPos.

Inductive Nat : Type :=
| Z  : Nat
| NZ : Pos -> Nat.

Definition Nat2nat (n : Nat) : nat :=
match n with
| Z => 0
| NZ p => toNat p
end.

Compute Nat2nat (NZ (I (I (I (I I'))))).

Definition Zero : Nat := Z.

Definition One : Nat := NZ BinaryPos.I'.

Function succ (n : Nat) : Nat :=
match n with
| Z    => NZ I'
| NZ p => NZ (BinaryPos.succ p)
end.

Function pred (n : Nat) : Nat :=
match n with
| Z     => Z
| NZ I' => Z
| NZ p => NZ (BinaryPos.pred p)
end.

Function add (n1 n2 : Nat) : Nat :=
match n1, n2 with
| Z    , _     => n2
| _    , Z     => n1
| NZ p1, NZ p2 => NZ (BinaryPos.add p1 p2)
end.

(* Function sub (n1 n2 : Nat) : ontion Nat :=
match n1, n2 with
end. *)

Function double (n : Nat) : Nat :=
match n with
| Z    => Z
| NZ p => NZ (BinaryPos.double p)
end.

Function mul (n1 n2 : Nat) : Nat :=
match n1, n2 with
| Z    , _     => Z
| _    , Z     => Z
| NZ p1, NZ p2 => NZ (BinaryPos.mul p1 p2)
end.

(* Function pow (n1 n2 : Nat) : Nat :=
match n2 with
end. *)

Function compare (n1 n2 : Nat) : comparison :=
match n1, n2 with
| Z    , Z     => Eq
| Z    , _     => Lt
| _    , Z     => Gt
| NZ p1, NZ p2 => BinaryPos.compare p1 p2
end.

Definition eqb (n1 n2 : Nat) : bool :=
match compare n1 n2 with
| Eq => true
| _  => false
end.

Definition leb (n1 n2 : Nat) : bool :=
match compare n1 n2 with
| Gt => false
| _  => true
end.

Definition ltb (n1 n2 : Nat) : bool :=
match compare n1 n2 with
| Lt => true
| _  => false
end.

Definition max (n1 n2 : Nat) : Nat :=
match n1, n2 with
| Z    , _     => n2
| _    , Z     => n1
| NZ p1, NZ p2 => NZ (max p1 p2)
end.

(* match compare n1 n2 with
| Lt => n2
| _  => n1
end. *)

Definition min (n1 n2 : Nat) : Nat :=
match compare n1 n2 with
| Lt => n1
| _  => n2
end.

Function odd (n : Nat) : bool :=
match n with
| Z    => false
| NZ p => BinaryPos.odd p
end.

Definition even (n : Nat) : bool := negb (odd n).

Lemma pred_succ :
  forall n : Nat,
    pred (succ n) = n.
Proof.
  intros [| p]; cbn.
  - reflexivity.
  - destruct (BinaryPos.succ p) eqn: Heq.
    + functional inversion Heq.
    + functional inversion Heq; subst; cbn.
      * reflexivity.
      * destruct (BinaryPos.succ p') eqn: Heq'.
        -- functional inversion Heq'.
        -- cbn.
Admitted.

Lemma add_0_l :
  forall n : Nat,
    add Z n = n.
Proof.
  reflexivity.
Qed.

Lemma add_0_r :
  forall n : Nat,
    add n Z = n.
Proof.
  destruct n; reflexivity.
Qed.

Lemma add_succ_l :
  forall n1 n2 : Nat,
    add (succ n1) n2 = succ (add n1 n2).
Proof.
  intros [| p1] [| p2]; cbn.
  1-3: reflexivity.
  rewrite BinaryPos.add_succ_l.
  reflexivity.
Qed.

Lemma add_pred_l :
  forall n1 n2 : Nat,
    add (pred n1) n2 = pred (add n1 n2).
Proof.
  intros [| p1] [| p2]; cbn.
  - reflexivity.
  - 
Abort.

Lemma add_comm :
  forall n1 n2 : Nat,
    add n1 n2 = add n2 n1.
Proof.
  intros [| p1] [| p2]; cbn.
  1-3: reflexivity.
  rewrite BinaryPos.add_comm.
  reflexivity.
Qed.

Lemma add_assoc :
  forall n1 n2 n3 : Nat,
    add (add n1 n2) n3 = add n1 (add n2 n3).
Proof.
  intros [| p1] [| p2] [| p3]; cbn.
  1-7: reflexivity.
  rewrite BinaryPos.add_assoc.
  reflexivity.
Qed.

(* Lemma sub_diag :
  forall n : Nat,
    add n (inv n) = 0.
Proof.
Admitted. *)

Lemma mul_0_l :
  forall n : Nat,
    mul Z n = Z.
Proof.
  intros [| p]; cbn; reflexivity.
Qed.

Lemma mul_0_r :
  forall n : Nat,
    mul n Z = Z.
Proof.
  intros [| p]; cbn; reflexivity.
Qed.

Lemma mul_succ_l :
  forall n1 n2 : Nat,
    mul (succ n1) n2 = add n2 (mul n1 n2).
Proof.
  intros [| p1] [| p2]; cbn.
  1-3: reflexivity.
  rewrite BinaryPos.mul_succ_l.
  reflexivity.
Qed.

Lemma mul_succ_r :
  forall n1 n2 : Nat,
    mul n1 (succ n2) = add (mul n1 n2) n1.
Proof.
  intros [| p1] [| p2]; cbn.
  1-2: reflexivity.
  - rewrite BinaryPos.mul_I'_r; reflexivity.
  - rewrite BinaryPos.mul_succ_r, BinaryPos.add_comm; reflexivity.
Qed.

(*
Lemma mul_pred_l :
  forall n1 n2 : Nat,
    mul (pred n1) n2 = sub (mul n1 n2) n2.
Proof.
Admitted.

Lemma mul_pred_r :
  forall n1 n2 : Nat,
    mul n1 (pred n2) = sub (mul n1 n2) n1.
Proof.
Admitted.
*)

Lemma mul_comm :
  forall n1 n2 : Nat,
    mul n1 n2 = mul n2 n1.
Proof.
  intros [| p1] [| p2]; cbn.
  1-3: reflexivity.
  rewrite BinaryPos.mul_comm.
  reflexivity.
Qed.

Lemma mul_assoc :
  forall n1 n2 n3 : Nat,
    mul (mul n1 n2) n3 = mul n1 (mul n2 n3).
Proof.
  intros [| p1] [| p2] [| p3]; cbn.
  1-7: reflexivity.
  rewrite BinaryPos.mul_assoc.
  reflexivity.
Qed.

Lemma mul_add_l :
  forall n1 n2 n3 : Nat,
    mul (add n1 n2) n3 = add (mul n1 n3) (mul n2 n3).
Proof.
  intros [| p1] [| p2] [| p3]; cbn.
  1-7: reflexivity.
  rewrite BinaryPos.mul_add_l.
  reflexivity.
Qed.

Lemma mul_add_r :
  forall n1 n2 n3 : Nat,
    mul n1 (add n2 n3) = add (mul n1 n2) (mul n1 n3).
Proof.
  intros [| p1] [| p2] [| p3]; cbn.
  1-7: reflexivity.
  rewrite BinaryPos.mul_add_r.
  reflexivity.
Qed.

Lemma min_comm :
  forall n1 n2 : Nat,
    min n1 n2 = min n2 n1.
Proof.
  intros [| p1] [| p2]; cbn.
  1-3: reflexivity.
  unfold min; cbn.
  rewrite <- BinaryPos.CompOpp_compare.
  destruct (BinaryPos.compare p2 p1); cbn.
Abort.

Lemma min_assoc :
  forall n1 n2 n3 : Nat,
    min (min n1 n2) n3 = min n1 (min n2 n3).
Proof.
Admitted.

Lemma max_comm :
  forall n1 n2 : Nat,
    max n1 n2 = max n2 n1.
Proof.
  intros [| p1] [| p2]; cbn.
  1-3: reflexivity.
  rewrite <- BinaryPos.max_comm.
  reflexivity.
Qed.

Lemma max_assoc :
  forall n1 n2 n3 : Nat,
    max (max n1 n2) n3 = max n1 (max n2 n3).
Proof.
  intros [| p1] [| p2] [| p3]; cbn.
  1-7: reflexivity.
(*   rewrite BinaryPos.max_assoc. *)
Admitted.