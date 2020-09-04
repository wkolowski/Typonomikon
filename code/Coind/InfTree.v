Set Implicit Arguments.

CoInductive InfTree (A : Type) : Type :=
{
    root : A;
    left : InfTree A;
    right : InfTree A;
}.

Arguments root  {A}.
Arguments left  {A} _.
Arguments right {A} _.

Record corecursive
  {A X : Type} (f : X -> InfTree A)
  (rt : X -> A) (l : X -> X) (r : X -> X) : Prop :=
{
    root_f  : forall x : X, root  (f x) = rt x;
    left_f  : forall x : X, left  (f x) = f (l x);
    right_r : forall x : X, right (f x) = f (r x);
}.

CoFixpoint corec
  {A X : Type} (rt : X -> A) (l : X -> X) (r : X -> X)
  (x : X) : InfTree A :=
{|
    root := rt x;
    left := corec rt l r (l x);
    right := corec rt l r (r x);
|}.

Theorem corecursive_corec :
  forall {A X : Type} (rt : X -> A) (l : X -> X) (r : X -> X),
    corecursive (corec rt l r) rt l r.
Proof.
  split; cbn; reflexivity.
Qed.

Definition uniqueness (A : Type) : Prop :=
  forall
    {X : Type} (f g : X -> InfTree A)
    (rt : X -> A) (l : X -> X) (r : X -> X),
      corecursive f rt l r -> corecursive g rt l r ->
        forall x : X, f x = g x.

CoInductive sim {A : Type} (t1 t2 : InfTree A) : Prop :=
{
    roots : root t1 = root t2;
    lefts : sim (left t1) (left t2);
    rights : sim (right t1) (right t2);
}.

Definition sim_to_eq (A : Type) : Prop :=
  forall t1 t2 : InfTree A, sim t1 t2 -> t1 = t2.

Inductive Index : Type :=
    | here : Index
    | goleft : Index -> Index
    | goright : Index -> Index.

Fixpoint subtree
  {A : Type} (t : InfTree A) (i : Index) : InfTree A :=
match i with
    | here => t
    | goleft i' => subtree (left t) i'
    | goright i' => subtree (right t) i'
end.

Fixpoint goleft' (i : Index) : Index :=
match i with
    | here => goleft here
    | goleft i' => goleft (goleft' i')
    | goright i' => goright (goleft' i')
end.

Fixpoint goright' (i : Index) : Index :=
match i with
    | here => goright here
    | goleft i' => goleft (goright' i')
    | goright i' => goright (goright' i')
end.

Lemma left_subtree :
  forall {A : Type} (i : Index) (t : InfTree A),
    left (subtree t i) = subtree t (goleft' i).
Proof.
  induction i; cbn; intros.
    reflexivity.
    rewrite IHi. reflexivity.
    rewrite IHi. reflexivity.
Qed.

Lemma right_subtree :
  forall {A : Type} (i : Index) (t : InfTree A),
    right (subtree t i) = subtree t (goright' i).
Proof.
  induction i; cbn; intros.
    reflexivity.
    rewrite IHi. reflexivity.
    rewrite IHi. reflexivity.
Qed.

Hint Resolve left_subtree right_subtree.

Theorem coinduction :
  forall {A : Type},
    uniqueness A -> sim_to_eq A.
Proof.
  unfold uniqueness, sim_to_eq.
  intros A uniqueness t1 t2 Hsim.
  eapply
  (
    uniqueness
      (Index) (subtree t1) (subtree t2)
      (fun i => root (subtree t2 i)) goleft' goright'
      _ _
      here
  ).
  Unshelve.
  all: repeat split; auto.
  clear uniqueness. intro i.
  revert t1 t2 Hsim.
  induction i; cbn; intros t1 t2 [].
    assumption.
    erewrite IHi.
      reflexivity.
      assumption.
    erewrite IHi.
      reflexivity.
      assumption.
Qed.

Record tsim (A : Type) : Type :=
{
    lt : InfTree A;
    rt : InfTree A;
    tsim' : sim lt rt;
}.

Arguments lt    {A} _.
Arguments rt    {A} _.
Arguments tsim' {A} _.

Definition root' {A : Type} (t : tsim A) : A :=
  root (rt t).

Definition left' {A : Type} (t : tsim A) : tsim A :=
{|
    lt := left (lt t);
    rt := left (rt t);
    tsim' := lefts (tsim' t);
|}.

Definition right' {A : Type} (t : tsim A) : tsim A :=
{|
    lt := right (lt t);
    rt := right (rt t);
    tsim' := rights (tsim' t);
|}.

Theorem coinduction' :
  forall {A : Type},
    uniqueness A -> sim_to_eq A.
Proof.
  unfold uniqueness, sim_to_eq.
  intros A uniqueness t1 t2 Hsim.
  eapply
  (
    uniqueness
      (tsim A) lt rt
      root' left' right'
      _ _
      {| lt := t1; rt := t2; tsim' := Hsim |}
  ).
  Unshelve.
  all: repeat split.
  destruct x, tsim'0. unfold root'; cbn. assumption.
Qed.

(** ** Funkcje na drzewach nieskończonych *)

Require Import D5.

CoFixpoint mirror {A : Type} (t : InfTree A) : InfTree A :=
{|
    root := root t;
    left := mirror (right t);
    right := mirror (left t);
|}.

Lemma mirror_mirror :
  forall {A : Type} (t : InfTree A),
    sim (mirror (mirror t)) t.
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply CH.
    apply CH.
Qed.

CoFixpoint tmap {A B : Type} (f : A -> B) (t : InfTree A) : InfTree B :=
{|
    root := f (root t);
    left := tmap f (left t);
    right := tmap f (right t);
|}.

Lemma tmap_id :
  forall {A : Type} (t : InfTree A),
    sim (tmap (fun x => x) t) t.
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply CH.
    apply CH.
Qed.

Lemma tmap_comp :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (t : InfTree A),
    sim (tmap g (tmap f t)) (tmap (fun x => g (f x)) t).
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply CH.
    apply CH.
Qed.

CoFixpoint replicate {A : Type} (x : A) : InfTree A :=
{|
    root := x;
    left := replicate x;
    right := replicate x;
|}.

Fixpoint index {A : Type} (i : Index) (t : InfTree A) : A :=
match i with
    | here => root t
    | goleft i' => index i' (left t)
    | goright i' => index i' (right t)
end.

Fixpoint revi (i : Index) : Index :=
match i with
    | here => here
    | goleft i' => goright (revi i')
    | goright i' => goleft (revi i')
end.

Lemma index_mirror :
  forall {A : Type} (i : Index) (t : InfTree A),
    index i (mirror t) = index (revi i) t.
Proof.
  induction i as [| i' | i']; cbn; intros.
    reflexivity.
    rewrite IHi'. reflexivity.
    rewrite IHi'. reflexivity.
Qed.

Definition node {A : Type} (v : A) (l r : InfTree A) : InfTree A :=
{|
    root := v;
    left := l;
    right := r;
|}.

Fixpoint replace
  {A : Type} (i : Index) (x : A) (t : InfTree A) : InfTree A :=
match i with
    | here => node x (left t) (right t)
    | goleft i' => node (root t) (replace i' x (left t)) (right t)
    | goright i' => node (root t) (left t) (replace i' x (right t))
end.

Lemma index_replicate :
  forall {A : Type} (i : Index) (x : A),
    index i (replicate x) = x.
Proof.
  induction i as [| i' | i']; cbn; intros.
    reflexivity.
    apply IHi'.
    apply IHi'.
Qed.

Lemma index_replace :
  forall {A : Type} (i : Index) (x : A) (t : InfTree A),
    index i (replace i x t) = x.
Proof.
  induction i as [| i' | i']; cbn; intros.
    reflexivity.
    apply IHi'.
    apply IHi'.
Qed.

CoFixpoint zipW
  {A B C : Type} (f : A -> B -> C)
  (ta : InfTree A) (tb : InfTree B) : InfTree C :=
{|
    root := f (root ta) (root tb);
    left := zipW f (left ta) (left tb);
    right := zipW f (right ta) (right tb);
|}.

Lemma zipW_mirror :
  forall
    {A B C : Type} (f : A -> B -> C)
    (ta : InfTree A) (tb : InfTree B),
      sim (zipW f (mirror ta) (mirror tb)) (mirror (zipW f ta tb)).
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply CH.
    apply CH.
Qed.

Definition unzipW
  {A B C : Type} (f : C -> A * B)
  (t : InfTree C) : InfTree A * InfTree B :=
    (tmap (fun c => fst (f c)) t,
     tmap (fun c => snd (f c)) t).

Fixpoint replace'
  {A : Type} (i : Index) (t1 t2 : InfTree A) : InfTree A :=
match i with
    | here => t2
    | goleft i' => node (root t1) (replace' i' (left t1) t2) (right t1)
    | goright i' => node (root t1) (left t1) (replace' i' (right t1) t2)
end.

Lemma subtree_replace' :
  forall {A : Type} (i : Index) (t1 t2 : InfTree A),
    subtree (replace' i t1 t2) i = t2.
Proof.
  induction i as [| i' | i']; cbn; intros.
    reflexivity.
    apply IHi'.
    apply IHi'.
Qed.

CoFixpoint iterate'
  {A : Type} (f : A -> A) (x : A) (n : nat) : InfTree A :=
{|
    root  := iter f n x;
    left  := iterate' f x (1 + 2 * n);
    right := iterate' f x (2 + 2 * n);
|}.

Fixpoint index_to_nat' (i : Index) (n : nat) : nat :=
match i with
    | here => n
    | goleft i' => index_to_nat' i' (1 + 2 * n)
    | goright i' => index_to_nat' i' (2 + 2 * n)
end.

Lemma index_iterate' :
  forall {A : Type} (f : A -> A) (i : Index) (x : A) (n : nat),
    index i (iterate' f x n) = iter f (index_to_nat' i n) x.
Proof.
  induction i as [| i' | i']; cbn; intros.
    reflexivity.
    rewrite IHi'. reflexivity.
    rewrite IHi'. reflexivity.
Qed.

Definition iterate
  {A : Type} (f : A -> A) (x : A) : InfTree A :=
    iterate' f x 0.

Definition index_to_nat (i : Index) : nat :=
  index_to_nat' i 0.

Lemma index_iterate :
  forall {A : Type} (f : A -> A) (i : Index) (x : A),
    index i (iterate f x) = iter f (index_to_nat i) x.
Proof.
  intros. apply index_iterate'.
Qed.

Inductive InfTreeNeq {A : Type} : InfTree A -> InfTree A -> Type :=
    | ITN_root :
        forall t1 t2 : InfTree A,
          root t1 <> root t2 -> InfTreeNeq t1 t2
    | ITN_left :
        forall t1 t2 : InfTree A,
          InfTreeNeq (left t1) (left t2) -> InfTreeNeq t1 t2
    | ITN_right :
        forall t1 t2 : InfTree A,
          InfTreeNeq (right t1) (right t2) -> InfTreeNeq t1 t2.

Lemma InfTreeNeq_neq :
  forall {A : Type} {t1 t2 : InfTree A},
    InfTreeNeq t1 t2 -> t1 <> t2.
Proof.
  induction 1; intros Heq.
    apply n. f_equal. assumption.
    apply IHX. f_equal. assumption.
    apply IHX. f_equal. assumption.
Qed.