Definition UIP : Prop :=
  forall (A : Type) (x y : A) (p q : x = y), p = q.

Definition ProofIrrelevance : Prop :=
  forall (P : Prop) (p1 p2 : P), p1 = p2.

Definition PropExt : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Lemma PropExt_simpl :
  PropExt -> forall P : Prop, P -> P = True.
Proof.
  unfold PropExt.
  intros PropExt P p.
  now apply PropExt.
Qed.

Lemma PropExt_UIP :
  PropExt -> UIP.
Proof.
  unfold PropExt, UIP.
  intros PropExt A x y p q.
  assert ((x = y) = True) by firstorder.
  revert p q.
  rewrite H.
  now intros [] [].
Qed.

Theorem PropExt_implies_ProofIrrelevance :
  PropExt -> ProofIrrelevance.
Proof.
  unfold PropExt, ProofIrrelevance.
  intros PropExt P p1 p2.
  assert (P = True) by firstorder.
  revert p1 p2.
  rewrite H.
  now intros [] [].
Qed.

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

Definition UIP_Path : Prop :=
  forall (A : Type) (x y : A) (p q : Path x y), Path p q.

Definition ProofIrrelevance_Path : Prop :=
  forall (P : Prop) (p1 p2 : P), Path p1 p2.

Definition PropExt_Path : Prop :=
  forall (P Q : Prop), (P <-> Q) -> Path P Q.

Lemma PropExt_Path_simpl :
  PropExt_Path -> forall P : Prop, P -> Path P True.
Proof.
  unfold PropExt_Path.
  intros PropExt_Path P p.
  now apply PropExt_Path.
Qed.

Lemma PropExt_Path__UIP_Path :
  PropExt_Path -> UIP_Path.
Proof.
  unfold PropExt_Path, UIP_Path.
  intros PropExt_Path A x y p q.
  assert (Path (Path x y) True) by firstorder.
  revert p q.
  rewrite H.
  now intros [] [].
Qed.

Theorem PropExt_Path__ProofIrrelevance_Path :
  PropExt_Path -> ProofIrrelevance_Path.
Proof.
  unfold PropExt_Path, ProofIrrelevance_Path.
  intros PropExt_Path P p1 p2.
  assert (Path P True) by firstorder.
  revert p1 p2.
  rewrite H.
  now intros [] [].
Qed.

Lemma PropExt__PropExt_Path :
  PropExt -> PropExt_Path.
Proof.
  unfold PropExt, PropExt_Path.
  intros PE P Q H.
  apply eq_to_Path.
  now apply PE.
Defined.

Section UIP_Path.
  Variable (H : UIP).

  Definition UIP_Path' : forall (A : Type) (x y : A) (p q : Path x y), Path p q.
  Proof.
    unfold UIP in H.
    intros.
    rewrite <- (Path_to_eq_to_Path' p), <- (Path_to_eq_to_Path' q),
      (H A x y (Path_to_eq p) (Path_to_eq q)).
    exact idp.
  Defined.
End UIP_Path.