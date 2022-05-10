(** Zainspirowane przez podręcznik
    #<a class='link' href='https://www.ps.uni-saarland.de/~smolka/drafts/icl2021.pdf'>
    Modeling and Proving in Computational Type Theory Using the Coq Proof Assistant</a>#
    (rozdział 27). *)

Module AczelTPolymorphic.

Set Universe Polymorphism.

Inductive AczelT@{u} : Type@{u+1} :=
| AczT : forall {X : Type@{u}}, (X -> AczelT) -> AczelT.

Definition AtomicT : AczelT :=
  AczT (fun e : Empty_set => match e with end).

Definition PairT (t1 t2 : AczelT) : AczelT :=
  AczT (fun b : bool => if b then t1 else t2).

Definition InfiniteT : AczelT :=
  AczT (fun _ : nat => AtomicT).

Fail Definition UniversalT : AczelT :=
  @AczT AczelT (fun t : AczelT => t).

End AczelTPolymorphic.

Set Universe Polymorphism.

Inductive AczelT : Type :=
| AczT : forall {X : Set}, (X -> AczelT) -> AczelT.

Definition AtomicT : AczelT :=
  AczT (fun e : Empty_set => match e with end).

Definition PairT (t1 t2 : AczelT) : AczelT :=
  AczT (fun b : bool => if b then t1 else t2).

Definition InfiniteT : AczelT :=
  AczT (fun _ : nat => AtomicT).

Fail Definition UniversalT : AczelT :=
  @AczT AczelT (fun t : AczelT => t).

Inductive Aczel : Prop :=
| Acz : forall {X : Prop}, (X -> Aczel) -> Aczel.

Definition Universal : Aczel :=
  Acz (fun x : Aczel => x).

Definition SubtreeT (s t : AczelT) : Prop :=
match t with
| AczT f => exists x, f x = s
end.

Lemma Irreflexive_SubtreeT :
  forall t : AczelT, ~ SubtreeT t t.
Proof.
  induction t as [X f IH]; cbn.
  intros [x Hfx].
  apply (IH x); red.
  rewrite Hfx.
  exists x. assumption.
Qed.

Fail Definition Subtree (s t : Aczel) : Prop :=
match t with
| Acz f => exists x, f x = s
end.

Fail Inductive Subtree (s : Aczel) : Aczel -> Prop :=
| SubtreeAcz : forall {X : Type} (f : X -> Aczel) (x : X), f x = s -> Subtree s (@Acz X f).

Require Import Setoid.

Lemma no_Subtree_relation_exists :
  forall R : Aczel -> Aczel -> Prop,
    ~ forall (t : Aczel) {X : Prop} (f : X -> Aczel),
        (R t (Acz f) <-> exists x : X, f x = t).
Proof.
  intros R H.
  enough (Hirrefl : forall t : Aczel, ~ R t t); cycle 1.
  - fix IH 1. intros [X f]. rewrite H. intros [x Heq].
    apply (IH (f x)). rewrite Heq at 2. rewrite H. exists x. reflexivity.
  - apply (Hirrefl Universal).
    unfold Universal; rewrite H.
    eexists. reflexivity.
Qed.

(* Coquand's theorem *)
Lemma no_Prop_embedding :
  forall (A : Prop) (f : Prop -> A) (g : A -> Prop),
    ~ (forall P : Prop, g (f P) <-> P).
Proof.
  intros P f g Hiff.
  pose (R t1 t2 := g
    match t2 with
    | Acz h => f (exists x, h x = t1)
    end).
  apply no_Subtree_relation_exists with R.
  intros t X h. unfold R; cbn.
  apply Hiff.
Qed.

Lemma no_Prop_embedding' :
  forall (A : Prop) (f : Prop -> A) (g : A -> Prop),
    ~ (forall P : Prop, g (f P) = P).
Proof.
  intros P f g Hiff.
  pose (R t1 t2 := g
    match t2 with
    | Acz h => f (exists x, h x = t1)
    end).
  apply no_Subtree_relation_exists with R.
  intros t X h. unfold R; cbn.
  rewrite Hiff. reflexivity.
Qed.

Definition idtoeqv {A B : Type} (p : A = B) : A -> B :=
match p with
| eq_refl => id
end.

Lemma idtoeqv_eq_sym :
  forall {A B : Type} (p : A = B) (b : B),
    idtoeqv p (idtoeqv (eq_sym p) b) = b.
Proof.
  intros A B [] b; cbn. reflexivity.
Qed.

Lemma Prop_is_not_a_proposition :
  forall P : Prop, ~ (@eq Type P Prop).
Proof.
  intros P H.
  pose (f := idtoeqv (eq_sym H)).
  pose (g := idtoeqv H).
  apply no_Prop_embedding' with P f g.
  intros Q; unfold f, g; cbn.
  apply idtoeqv_eq_sym.
Qed.

Lemma PI_LEM :
  (forall P : Prop, P \/ ~ P) -> (forall (P : Prop) (p1 p2 : P), p1 = p2).
Proof.
  intros lem P p1 p2.
  destruct (lem (p1 = p2)); [assumption |].
  pose (f := fun Q => if lem Q then p1 else p2).
  pose (g := fun p => p = p1).
  exfalso; apply no_Prop_embedding with P f g; intros Q; unfold f, g.
  destruct (lem Q).
  - split; trivial.
  - split; intros.
    + congruence.
    + contradiction.
Qed.