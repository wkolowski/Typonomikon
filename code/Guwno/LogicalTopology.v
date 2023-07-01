(**
  Wzięte z http://davidjaz.com/Talks/MHOTT-myers-slides.pdf
*)
Definition open {A : Type} (U : A -> Prop) : Prop :=
  forall x y : A, U x -> x <> y \/ U y.

Definition subtype (A : Type) : Type := A -> Prop.

Definition inclusion {A : Type} (P Q : subtype A) : Prop :=
  forall x : A, P x -> Q x.

Definition intersection {A : Type} (P Q : subtype A) : subtype A :=
  fun x : A => P x /\ Q x.

Definition union {A : Type} (P Q : subtype A) : subtype A :=
  fun x : A => P x \/ Q x.

Definition complement {A : Type} (P : subtype A) : subtype A :=
  fun x : A => ~ P x.

Definition MerelyInhabited {A : Type} (U : subtype A) : Prop :=
  exists x : A, U x.

Definition detachable {A : Type} (U : subtype A) : Prop :=
  forall x : A, U x \/ ~ U x.

Definition LogicallyConnected {A : Type} (U : subtype A) : Prop :=
  forall P : subtype A,
    inclusion U (union P (complement P)) ->
      inclusion U P \/ inclusion U (complement P).

Definition LogicalConnectedComponent {A : Type} (U : subtype A) : Prop :=
  MerelyInhabited U /\ detachable U /\ LogicallyConnected U.

Lemma intersection_to_eq :
  forall {A : Type} (U V : subtype A),
    LogicalConnectedComponent U -> LogicalConnectedComponent V ->
      MerelyInhabited (intersection U V) -> (forall x : A, U x <-> V x).
Proof.
  intros A U V (U1 & U2 & U3) (V1 & V2 & V3) (x & Ux & Vx) y.
  unfold MerelyInhabited, detachable, LogicallyConnected, intersection in *.
  split.
  - intros Uy.
    destruct (U3 V).
    + intros z Uz; red.
      now apply V2.
    + now apply H.
    + now apply H in Ux.
  - intros Vy.
    destruct (V3 U).
    + intros z Vz; red.
      now apply U2.
    + now apply H.
    + now apply H in Vx.
Qed.

Definition neighbour {A : Type} (x y : A) : Prop :=
  ~ ~ (x = y).

Lemma neighour_refl :
  forall {A : Type} (x : A),
    neighbour x x.
Proof.
  easy.
Qed.

Lemma neighour_symm :
  forall {A : Type} (x y : A),
    neighbour x y -> neighbour y x.
Proof.
  firstorder.
Qed.

Lemma neighour_trans :
  forall {A : Type} (x y z : A),
    neighbour x y -> neighbour y z -> neighbour x z.
Proof.
  unfold neighbour.
  intros A x y z nxy nyz xz.
  apply nxy; intros ->.
  apply nyz; intros ->.
  easy.
Qed.

Lemma neighbour_fun :
  forall {A B : Type} (f : A -> B) (x y : A),
    neighbour x y -> neighbour (f x) (f y).
Proof.
  unfold neighbour.
  intros A B f x y nxy fxy.
  now apply nxy; intros ->.
Qed.

Definition neighbourhood {A : Type} (x : A) : Type :=
  {y : A | neighbour x y}.

Definition germ {A B : Type} (f : A -> B) (a : A) :
  neighbourhood a -> neighbourhood (f a).
Proof.
  unfold neighbourhood, neighbour.
  intros [x n].
  exists (f x).
  intros Heq.
  now apply n; intros ->.
Qed.

(*
(Chain rule)
  For f : A → B, g : B → A, and a : A,
    d(g ◦ f )a = dgf (a) ◦ df
*)

Definition deMorgan (A : Type) : Prop :=
  forall x y : A, neighbour x y \/ ~ neighbour x y.