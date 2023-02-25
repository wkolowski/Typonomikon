Set Primitive Projections.

Inductive ColistF (F A : Type) : Type :=
| ConilF  : ColistF F A
| CoconsF : A -> F -> ColistF F A.

Arguments ConilF  {F A}.
Arguments CoconsF {F A} _ _.

CoInductive Colist (A : Type) := MkColist
{
  out : ColistF (Colist A) A;
}.

Arguments MkColist {A} _.
Arguments out      {A} _.

Add Printing Constructor Colist.

Notation Colist' A := (ColistF (Colist A) A).

Definition Conil {A : Type} : Colist A := MkColist ConilF.

Definition Cocons {A : Type} (h : A) (t : Colist A) : Colist A :=
  MkColist (CoconsF h t).

Inductive ExistsF {A : Type} (P : A -> Prop) : Colist' A -> Prop :=
| ExistsF_zero : forall {h : A} (t : Colist A), P h -> ExistsF P (CoconsF h t)
| ExistsF_succ : forall (h : A) {t : Colist A}, ExistsF P (out t) -> ExistsF P (CoconsF h t).

Arguments ExistsF_zero {A P h} _ _.
Arguments ExistsF_succ {A P} _ {t} _.

Module Def.

Definition Exists {A : Type} (P : A -> Prop) (l : Colist A) : Prop :=
  ExistsF P (out l).

Lemma Exists_impl :
  forall {A : Type} (P Q : A -> Prop) (l : Colist A),
    (forall x : A, P x -> Q x) ->
      Exists P l -> Exists Q l.
Proof.
  unfold Exists; intros A P Q l HPQ Hex.
  induction Hex.
  - now left; apply HPQ.
  - now right.
Qed.

End Def.

Module Def_Arguments.

Definition Exists {A : Type} (P : A -> Prop) (l : Colist A) : Prop :=
  ExistsF P (out l).

Arguments Exists {A} P l /.

Lemma Exists_impl :
  forall {A : Type} (P Q : A -> Prop) (l : Colist A),
    (forall x : A, P x -> Q x) ->
      Exists P l -> Exists Q l.
Proof.
  cbn; intros A P Q l HPQ Hex.
  induction Hex.
  - now left; apply HPQ.
  - now right.
Qed.

End Def_Arguments.

Module Abbreviation.

Notation Exists P l := (ExistsF P (out l)).

Lemma Exists_impl :
  forall {A : Type} (P Q : A -> Prop) (l : Colist A),
    (forall x : A, P x -> Q x) ->
      Exists P l -> Exists Q l.
Proof.
  intros A P Q l HPQ Hex.
  induction Hex.
  - now left; apply HPQ.
  - now right.
Qed.

End Abbreviation.

Module Abbreviation_Eta.

Notation Exists := (fun P l => ExistsF P (out l)).

Lemma Exists_impl :
  forall {A : Type} (P Q : A -> Prop) (l : Colist A),
    (forall x : A, P x -> Q x) ->
      Exists P l -> Exists Q l.
Proof.
  cbn; intros A P Q l HPQ Hex.
  induction Hex.
  - now left; apply HPQ.
  - now right.
Qed.

End Abbreviation_Eta.