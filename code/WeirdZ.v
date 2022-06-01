Require Import Recdef.

Inductive Z : Type :=
| Zero : Z
| MinusOne : Z
| Next : Z -> Z.

Function neg' (k : Z) : Z :=
match k with
| Zero => MinusOne
| MinusOne => Zero
| Next k' => Next (neg' k')
end.

Function abs (k : Z) : Z :=
match k with
| Zero => Zero
| MinusOne => Next Zero
| Next k' => Next (abs k')
end.

Function succ (k : Z) : Z :=
match k with
| Zero => Next Zero
| MinusOne => Zero
| Next Zero => Next (Next Zero)
| Next MinusOne => MinusOne
| Next k' => Next (succ k')
end.

Function pred (k : Z) : Z :=
match k with
| Zero => MinusOne
| MinusOne => Next MinusOne
| Next Zero => Zero
| Next MinusOne => Next (Next MinusOne)
| Next k' => Next (pred k')
end.

Definition neg (k : Z) : Z :=
  succ (neg' k).

Lemma neg'_neg' :
  forall k : Z, neg' (neg' k) = k.
Proof.
  intros k; functional induction (neg' k)
  ; cbn; rewrite ?IHz; reflexivity.
Qed.

Lemma abs_abs :
  forall k : Z, abs (abs k) = abs k.
Proof.
  intros k; functional induction (abs k)
  ; cbn; rewrite ?IHz; reflexivity.
Qed.

Lemma succ_pred :
  forall k : Z,
    succ (pred k) = k.
Proof.
  intros k; functional induction (pred k); cbn.
  1-4: reflexivity.
  rewrite IHz; clear IHz.
  functional induction (pred k'); cbn in *.
  1-2: contradiction.
  1-3: reflexivity.
Qed.

Lemma pred_succ :
  forall k : Z,
    pred (succ k) = k.
Proof.
  intros k; functional induction (succ k); cbn.
  1-4: reflexivity.
  rewrite IHz; clear IHz.
  functional induction (succ k'); cbn in *.
  1-2: contradiction.
  1-3: reflexivity.
Qed.

Lemma neg'_succ :
  forall k : Z, neg' (succ k) = pred (neg' k).
Proof.
  intros k; functional induction (succ k); cbn.
  1-4: reflexivity.
  rewrite IHz; clear IHz.
  functional induction (neg' k'); cbn.
  1-2: contradiction.
  reflexivity.
Qed.

Lemma neg_neg :
  forall k : Z, neg (neg k) = k.
Proof.
  intros k; unfold neg.
  rewrite neg'_succ, succ_pred, neg'_neg'.
  reflexivity.
Qed.