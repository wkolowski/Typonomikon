(** * B3: Konstruktywna logika wyższego rzędu [TODO] *)

From Typonomikon Require Export B2z.

(** * Logika pierwszego rzędu a logika wyższego rzędu (TODO) *)

(** ** Logika pierwszego rzędu *)

(** ** Logika drugiego rzędu *)

(** ** Logika wyższego rzędu *)

(** * Predykatywizm i kodowania impredykatywne (TODO) *)

(* begin hide *)
(* TODO: Tautologie na kodowaniach impredykatywnych jako ćwiczenia z funkcji anonimowych *)
(* end hide *)

Definition iand (P Q : Prop) : Prop :=
  forall C : Prop, (P -> Q -> C) -> C.

Definition ior (P Q : Prop) : Prop :=
  forall C : Prop, (P -> C) -> (Q -> C) -> C.

Definition iTrue : Prop :=
  forall C : Prop, C -> C.

Definition iFalse : Prop :=
  forall C : Prop, C.

Lemma iand_spec :
  forall P Q : Prop,
    iand P Q <-> P /\ Q.
(* begin hide *)
Proof.
  unfold iand. split.
    intro H. apply H. intros p q. split.
      assumption.
      assumption.
    intros [p q] C H. apply H.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma ior_spec :
  forall P Q : Prop,
    ior P Q <-> P \/ Q.
(* begin hide *)
Proof.
  unfold ior. split.
    intro H. apply H.
      intro p. left. assumption.
      intro q. right. assumption.
    intros [p | q] C pc qc.
      apply pc. assumption.
      apply qc. assumption.
Qed.
(* end hide *)

Lemma iTrue_spec :
  iTrue <-> True.
(* begin hide *)
Proof.
  unfold iTrue. split.
    intros _. trivial.
    intros _ C c. assumption.
Qed.
(* end hide *)

Lemma iFalse_False :
  iFalse <-> False.
(* begin hide *)
Proof.
  unfold iFalse. split.
    intro H. apply H.
    contradiction.
Qed.
(* end hide *)

Definition iexists (A : Type) (P : A -> Prop) : Prop :=
  forall C : Prop, (forall x : A, P x -> C) -> C.

Lemma iexists_spec :
  forall (A : Type) (P : A -> Prop),
    iexists A P <-> exists x : A, P x.
(* begin hide *)
Proof.
  unfold iexists. split.
    intro H. apply H. intros x p. exists x. assumption.
    intros [x p] C H. apply (H x). assumption.
Qed.
(* end hide *)

Definition ieq {A : Type} (x y : A) : Prop :=
  forall C : Prop, ((x = y) -> C) -> C.

Definition ieq' {A : Type} (x : A) : A -> Prop :=
  fun y : A =>
    forall P : A -> Prop, P x -> P y.

Lemma ieq_spec :
  forall (A : Type) (x y : A),
    ieq x y <-> x = y.
(* begin hide *)
Proof.
  unfold ieq. split.
    intro H. apply H. trivial.
    intros [] C H. apply H. reflexivity.
Qed.
(* end hide *)

Lemma ieq'_spec :
  forall (A : Type) (x y : A),
    ieq' x y <-> x = y.
(* begin hide *)
Proof.
  unfold ieq'. split.
    intro H. apply H. reflexivity.
    intros [] P px. assumption.
Qed.
(* end hide *)

(** * Spójniki pozytywne i negatywne (TODO) *)

(** TODO:
  - implikacja jest negatywna
  - koniunkcja jest negatywna
  - dysjunkcja jest pozytywna
  - fałsz jest pozytywny
  - prawda jest negatywna
  - słaba negacja jest negatywna
  - silna negacja jest pozytywna
  - równoważność jest negatywna
*)