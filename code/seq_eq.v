Set Definitional UIP.

Inductive seq {A : Type} (x : A) : A -> SProp :=
| srefl : seq x x.

Lemma seq_eq :
  forall {A : Type} {x y : A},
    seq x y -> x = y.
Proof.
  intros A x y [].
  reflexivity.
Defined.

Lemma eq_seq :
  forall {A : Type} {x y : A},
    x = y -> seq x y.
Proof.
  intros A x y [].
  reflexivity.
Defined.

Lemma eq_seq_eq :
  forall {A : Type} {x y : A} (p : x = y),
    seq_eq (eq_seq p) = p.
Proof.
  intros A x y []; cbn.
  reflexivity.
Defined.

Inductive sseq {A : SProp} (x : A) : A -> SProp :=
| ssrefl : sseq x x.

Lemma seq_eq_seq :
  forall {A : Type} {x y : A} (p : seq x y),
    sseq (eq_seq (seq_eq p)) p.
Proof.
  intros A x y []; cbn.
  reflexivity.
Defined.

Lemma isSet_all :
  forall (A : Type) (x y : A) (p q : x = y),
    p = q.
Proof.
  intros A x y p q.
  rewrite <- (eq_seq_eq p), <- (eq_seq_eq q).
  reflexivity.
Defined.
