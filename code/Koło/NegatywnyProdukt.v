CoInductive product (A : Type) (B : Type) : Type :=
{
    fst : A;
    snd : B;
}.

Definition swap {A B : Type} (p : product A B) : product B A :=
{|
    fst := snd A B p;
    snd := fst A B p;
|}.

Definition para_liczb : product nat nat :=
{|
    fst := 42;
    snd := 1;
|}.

Compute fst nat nat para_liczb.
Compute snd nat nat para_liczb.

Lemma eq_product :
  forall {A B : Type} (p q : product A B),
    fst A B p = fst A B q -> snd A B p = snd A B q -> p = q.
Proof.
  destruct p, q. cbn. intros -> ->. reflexivity.
Qed.