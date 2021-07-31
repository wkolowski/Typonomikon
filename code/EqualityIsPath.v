(** https://homotopytypetheory.org/2012/01/22/univalence-versus-extraction/ *)

Inductive Path {A : Type} (x : A) : A -> Type :=
    | idp : Path x x.

Arguments idp {A x}.

Definition eq_to_Path {A : Type} {x y : A} (e : x = y) : Path x y :=
match e with
    | eq_refl => idp
end.

Definition Path_to_eq {A : Type} {x y : A} (p : Path x y) : x = y :=
match p with
    | idp => eq_refl
end.

Lemma eq_to_Path_to_eq :
  forall {A : Type} {x y : A} (e : x = y),
    Path_to_eq (eq_to_Path e) = e.
Proof.
  destruct e. cbn. reflexivity.
Qed.

Lemma Path_to_eq_to_Path :
  forall {A : Type} {x y : A} (p : Path x y),
    eq_to_Path (Path_to_eq p) = p.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma eq_to_Path_to_eq' :
  forall {A : Type} {x y : A} (e : x = y),
    Path (Path_to_eq (eq_to_Path e)) e.
Proof.
  destruct e. cbn. reflexivity.
Defined.

Lemma Path_to_eq_to_Path' :
  forall {A : Type} {x y : A} (p : Path x y),
    Path (eq_to_Path (Path_to_eq p)) p.
Proof.
  destruct p. cbn. reflexivity.
Defined.

(* Inductive Truncated *)

Class iso (A B : Type) : Type :=
{
    f : A -> B;
    linv : {g : B -> A | forall a : A, g (f a) = a};
    rinv : {h : B -> A | forall b : B, f (h b) = b};
}.

Definition ProofIrrelevance : Prop :=
  forall (P : Prop) (p1 p2 : P), p1 = p2.

Definition UA : Type :=
  forall A B : Type, iso (iso A B) (Path A B).

#[refine]
Instance iso_id : iso bool bool :=
{
    f := fun b => b;
}.
Proof.
  exists (fun b => b). reflexivity.
  exists (fun b => b). reflexivity.
Defined.

#[refine]
Instance iso_negb : iso bool bool :=
{
    f := negb;
}.
Proof.
  exists negb. destruct a; reflexivity.
  exists negb. destruct b; reflexivity.
Defined.

Lemma ProofIrrelevance_UA_inconsistent :
  ProofIrrelevance -> UA -> False.
Proof.
  unfold ProofIrrelevance, UA.
  intros pi ua.
  destruct (ua bool bool) as [F [G FG] [H HF]].
  assert (forall x y : iso bool bool, x = y).
    intros. rewrite <- FG, <- (Path_to_eq_to_Path (F y)), (pi _ (eq_to_Path (Path_to_eq (F y))) (F x)), FG.
    reflexivity.
  specialize (H0 iso_id iso_negb).
  assert (forall b : bool, @f _ _ iso_negb b = b).
    intro. rewrite <- H0. reflexivity.
  specialize (H1 true).
  cbn in H1. congruence.
Qed.