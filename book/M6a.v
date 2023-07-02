(** * M6a: Zaawansowana logika i aksjomaty [TODO] *)

(** * Związki między aksjomatami *)

From Typonomikon Require Import B6.

Lemma PropExt_simpl :
  PropExt -> forall P : Prop, P -> P = True.
(* begin hide *)
Proof.
  unfold PropExt.
  intros PropExt P p.
  now apply PropExt.
Qed.
(* end hide *)

Lemma PropExt_ProofIrrelevance :
  PropExt -> ProofIrrelevance.
(* begin hide *)
Proof.
  unfold PropExt, ProofIrrelevance.
  intros PropExt P p1 p2.
  assert (P = True) by now apply PropExt_simpl.
  revert p1 p2.
  rewrite H.
  now intros [] [].
Qed.
(* end hide *)

Lemma ProofIrrelevance_UIP :
  ProofIrrelevance -> UIP.
(* begin hide *)
Proof.
  unfold ProofIrrelevance, UIP.
  intros PI A x y p q.
  apply PI.
Qed.
(* end hide *)

Lemma UIP_K : UIP -> K.
(* begin hide *)
Proof.
  unfold UIP, K.
  intros UIP A x p.
  apply UIP.
Qed.
(* end hide *)

Lemma K_UIP : K -> UIP.
(* begin hide *)
Proof.
  unfold K, UIP.
  intros K A x y p q.
  destruct p.
  symmetry. apply K.
Qed.
(* end hide *)

Lemma ProofIrrelevance_K :
  ProofIrrelevance -> K.
(* begin hide *)
Proof.
  now intros; apply UIP_K, ProofIrrelevance_UIP.
Qed.
(* end hide *)

Lemma PropExt_UIP :
  PropExt -> UIP.
(* begin hide *)
Proof.
  now intros; apply ProofIrrelevance_UIP, PropExt_ProofIrrelevance.
Qed.
(* end hide *)

(** * [Set] to [Type]... czasem (TODO) *)

Module SetIsType.

Require Import SetIsType.

Lemma SetIsType : Set = Type.
Proof.
  reflexivity.
Qed.

End SetIsType.

(** * [SProp] nie jest ścisłym zdaniem *)

Require Import StrictProp.

Lemma SProp_is_not_a_strict_proposition :
  forall P : SProp, ~ @eq Type (Box P) SProp.
Proof.
  intros P H.
  pose (prop T := forall t1 t2 : T, t1 = t2).
  assert (prop (Box P)) by (intros [] []; reflexivity).
  assert (prop SProp) by (rewrite <- H; assumption).
  red in H1; specialize (H1 sUnit sEmpty).
  enough sEmpty.
  - destruct H2.
  - rewrite <- H1. constructor.
Qed.

Inductive seq {A : SProp} (x : A) : A -> SProp :=
| srefl : seq x x.

Goal forall P : SProp, ~ @eq Type P SProp.
Proof.
  intros P H.
  pose (prop T := forall t1 t2 : T, eq t1 t2).
  assert (prop (Box P)). red. intros [] []. reflexivity.
  assert (forall p1 p2 : P, p1 = p2). reflexivity.
  assert (prop SProp). rewrite <- H. exact H1.
  red in H2. specialize (H2 sUnit sEmpty).
  enough sEmpty.
  - destruct H3.
  - destruct H2. constructor.
Fail Qed.
Abort.

(** * Drzewa Aczela *)

Module AczelTrees.

(** Zainspirowane przez podręcznik
    #<a class='link' href='https://www.ps.uni-saarland.de/~smolka/drafts/icl2021.pdf'>
    Modeling and Proving in Computational Type Theory Using the Coq Proof Assistant</a>#
    (rozdział 27). *)

Set Universe Polymorphism.

Inductive Aczel : Prop :=
| Acz : forall {X : Prop}, (X -> Aczel) -> Aczel.

Definition Universal : Aczel :=
  Acz (fun x : Aczel => x).

Fail Definition Subtree (s t : Aczel) : Prop :=
match t with
| Acz f => exists x, f x = s
end.

Fail Inductive Subtree (s : Aczel) : Aczel -> Prop :=
| SubtreeAcz : forall {X : Type} (f : X -> Aczel) (x : X), f x = s -> Subtree s (@Acz X f).

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
    eexists.
    reflexivity.
Qed.

(** * [Prop] nie jest zdaniem - twierdzenie Coquand (TODO) *)

Lemma no_Prop_embedding :
  forall (A : Prop) (f : Prop -> A) (g : A -> Prop),
    ~ (forall P : Prop, g (f P) <-> P).
Proof.
  intros A f g Hiff.
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
  forall P : Prop, ~ @eq Type P Prop.
Proof.
  intros P H.
  pose (f := idtoeqv (eq_sym H)).
  pose (g := idtoeqv H).
  apply no_Prop_embedding' with P f g.
  intros Q; unfold f, g; cbn.
  apply idtoeqv_eq_sym.
Qed.

(** * Prawo wyłączonego środka implikuje Proof Irrelevance (TODO) *)

Lemma PI_LEM :
  LEM -> ProofIrrelevance.
Proof.
  unfold LEM, ProofIrrelevance.
  intros lem P p1 p2.
  destruct (lem (p1 = p2)); [assumption |].
  pose (f := fun Q => if lem Q then p1 else p2).
  pose (g := fun p => p = p1).
  exfalso; apply no_Prop_embedding with P f g.
  intros Q; unfold f, g.
  destruct (lem Q).
  - split; trivial.
  - split; intros.
    + congruence.
    + contradiction.
Qed.

(** * Twierdzenie o hierarchii dla uniwersów (TODO) *)

Module HierarchyTheoremUniverses.

Record Embedding@{u} (X Y : Type@{u}) : Type@{u} :=
{
  coe : X -> Y;
  uncoe : Y -> X;
  law : forall x : X, uncoe (coe x) = x;
}.

Arguments coe {X Y} _ _.
Arguments uncoe {X Y} _ _.
Arguments law {X Y} _ _.

Lemma Reflexive_Embedding :
  forall X : Type, Embedding X X.
Proof.
  refine (fun _ => {| coe x := x; uncoe x := x; law _ := eq_refl; |}).
Defined.

Lemma Embedding_inv :
  forall X Y : Type, (Embedding X Y -> False) -> X <> Y.
Proof.
  intros X Y Hne ->.
  apply Hne, Reflexive_Embedding.
Defined.

Lemma Prop_does_not_embed_into_a_proposition :
  forall P : Prop, Embedding Prop P -> False.
Proof.
  intros P [f g Hfg].
  eapply no_Prop_embedding', Hfg.
Qed.

Section HierarchyTheoremUniverses.

Universe u.

Context
  {A : Type@{u}}
  (E : Embedding Type@{u} A).

Inductive AczelT' : Type@{u} :=
| AczT' : forall (a : A) (f : uncoe E a -> AczelT'), AczelT'.

Definition SubtreeT' (t1 t2 : AczelT') : Prop :=
match t2 with
| AczT' _ f => exists x, f x = t1
end.

Lemma Irreflexive_SubtreeT' :
  forall t : AczelT', ~ SubtreeT' t t.
Proof.
  induction t as [a f IH].
  cbn. intros [x Heq].
  apply (IH x).
  rewrite Heq at 2. cbn.
  exists x. reflexivity.
Qed.

Lemma Embedding_AczelT' : Embedding AczelT' (uncoe E (coe E AczelT')).
Proof.
  replace (uncoe E (coe E AczelT')) with AczelT'.
  - apply Reflexive_Embedding.
  - rewrite law. reflexivity.
Defined.

Definition Universal : AczelT' :=
  AczT' (coe E AczelT') (uncoe Embedding_AczelT').

Lemma SubbtreeT'_Universal :
  SubtreeT' Universal Universal.
Proof.
  cbn. exists (coe Embedding_AczelT' Universal).
  rewrite law. reflexivity.
Qed.

Lemma Hierarchy_Embedding : False.
Proof.
  eapply Irreflexive_SubtreeT'.
  apply SubbtreeT'_Universal.
Qed.

End HierarchyTheoremUniverses.

Section HierarchyTheorem'.

Universe u.

Lemma Hierarchy_eq :
  forall A : Type@{u}, Type@{u} = A -> False.
Proof.
  intros A.
  apply Embedding_inv.
  apply Hierarchy_Embedding.
Qed.

End HierarchyTheorem'.

Section HierarchyTheorem''.

Universe u1 u2 u3.

Constraint u1 < u2.
Constraint u2 < u3.

Lemma Hierarchy_neq : Type@{u2} = Type@{u1} -> False.
Proof.
  apply (@Hierarchy_eq@{u2 u3} Type@{u1}).
Qed.

End HierarchyTheorem''.

End HierarchyTheoremUniverses.

End AczelTrees.

(** * Wincyj drzew Aczela (TODO) *)

Module MoreAczelTrees.

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

Module AczelTMonomorphic.

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

End AczelTMonomorphic.

End MoreAczelTrees.

(** * Ko-drzewa Aczela (TODO) *)

Module CoAczelTrees.

CoInductive CoAczelT@{u} : Type@{u+1} :=
{
  branchingT : Type@{u};
  subtreesT : branchingT -> CoAczelT;
}.

Definition AtomicT : CoAczelT :=
{|
  subtreesT := fun e : Empty_set => match e with end
|}.

Definition PairT (t1 t2 : CoAczelT) : CoAczelT :=
{|
  subtreesT := fun b : bool => if b then t1 else t2
|}.

Definition InfiniteT : CoAczelT :=
{|
  subtreesT := fun _ : nat => AtomicT
|}.

Fail Definition UniversalT : CoAczelT :=
{|
  branchingT := CoAczelT;
  subtreesT := fun t : CoAczelT => t
|}.

Definition SubtreeT (t1 t2 : CoAczelT) : Prop :=
  exists x, subtreesT t2 x = t1.

Set Warnings "-cannot-define-projection".
CoInductive CoAczel : Prop :=
{
  branching : Prop;
  subtrees : branching -> CoAczel;
}.
Set Warnings "cannot-define-projection".

Fail Definition Subtree (t1 t2 : CoAczel) : Prop :=
  exists x, subtrees t2 x = t1.

End CoAczelTrees.