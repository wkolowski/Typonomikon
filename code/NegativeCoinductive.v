Module Record.

#[projections(primitive)]
Record product (A B : Type) : Type := Pair
{
  outl : A;
  outr : B;
}.

Arguments outl {A B} _.
Arguments outr {A B} _.

Lemma eq_product :
  forall {A B : Type} (p1 p2 : product A B),
    outl p1 = outl p2 -> outr p1 = outr p2 -> p1 = p2.
Proof.
  intros A B [a1 b1] [a2 b2]; cbn.
  now intros -> ->.
Qed.

End Record.

Module Inductive.

#[projections(primitive)]
Inductive product (A B : Type) : Type := Pair
{
  outl : A;
  outr : B;
}.

Arguments outl {A B} _.
Arguments outr {A B} _.

Lemma eq_product :
  forall {A B : Type} (p1 p2 : product A B),
    outl p1 = outl p2 -> outr p1 = outr p2 -> p1 = p2.
Proof.
  Fail intros A B [a1 b1] [a2 b2]; cbn.
Abort.

End Inductive.

Module CoInductive.

#[projections(primitive)]
CoInductive product (A B : Type) : Type := Pair
{
  outl : A;
  outr : B;
}.

Arguments outl {A B} _.
Arguments outr {A B} _.

Lemma eq_product :
  forall {A B : Type} (p1 p2 : product A B),
    outl p1 = outl p2 -> outr p1 = outr p2 -> p1 = p2.
Proof.
  Fail intros A B [a1 b1] [a2 b2]; cbn.
Abort.

End CoInductive.
