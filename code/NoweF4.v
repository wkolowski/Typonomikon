(** * F4: Kolisty [TODO] *)

(* begin hide *)
(* TODO: insertion sort na kolistach *)
(* end hide *)
Set Primitive Projections.

Set Warnings "+cannot-define-projection".
Set Warnings "+non-primitive-record".

(** * Kolisty nie znaczy okrągły *)

From Typonomikon Require Import D5.

Variant ColistF (F A : Type) : Type :=
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

Notation Colist' A := (ColistF (Colist A) A).

Notation Conil := (MkColist ConilF).
Notation Cocons h t := (MkColist (CoconsF h t)).

Variant BisimF
  {A : Type} (F : Colist A -> Colist A -> Prop)
  : Colist' A -> Colist' A -> Prop :=
| BisimF_ConilF  : BisimF F ConilF ConilF
| BisimF_CoconsF :
    forall {h1 h2 : A} {t1 t2 : Colist A},
      h1 = h2 -> F t1 t2 -> BisimF F (CoconsF h1 t1) (CoconsF h2 t2).

Arguments BisimF_ConilF  {A F}.
Arguments BisimF_CoconsF {A F h1 h2 t1 t2} _ _.

CoInductive Bisim {A : Type} (l1 l2 : Colist A) : Prop :=
{
  Bisim_out : BisimF Bisim (out l1) (out l2);
}.

Arguments Bisim_out {A l1 l2} _.

Notation Bisim' := (BisimF Bisim).

Inductive Finite' {A : Type} : Colist' A -> Prop :=
| Finite'_ConilF  : Finite' ConilF
| Finite'_CoconsF : forall (h : A) {t : Colist A}, Finite' (out t) -> Finite' (CoconsF h t).

Arguments Finite'_ConilF  {A}.
Arguments Finite'_CoconsF {A} _ {t} _.

Definition Finite {A : Type} (l : Colist A) : Prop :=
  Finite' (out l).

Arguments Finite {A} l /.

Variant InfiniteF {A : Type} (F : Colist A -> Prop) : Colist' A -> Prop :=
| Infinite_CoconsF : forall (h : A) {t : Colist A}, F t -> InfiniteF F (CoconsF h t).

Arguments Infinite_CoconsF {A F h t} _.

CoInductive Infinite {A : Type} (l : Colist A) : Prop :=
{
  Infinite_out : InfiniteF Infinite (out l);
}.

Arguments Infinite_out {A l} _.

Notation Infinite' := (InfiniteF Infinite).

Variant ForallF
  {A : Type} (F : Colist A -> Prop) (P : A -> Prop)
  : Colist' A -> Prop :=
| ForallF_ConilF  : ForallF F P ConilF
| ForallF_CoconsF : forall {h : A} {t : Colist A}, P h -> F t -> ForallF F P (CoconsF h t).

Arguments ForallF_ConilF  {A F} _.
Arguments ForallF_CoconsF {A F} _ {h t} _ _.

CoInductive Forall {A : Type} (P : A -> Prop) (l : Colist A) : Prop :=
{
  Forall_out : ForallF (Forall P) P (out l);
}.

Arguments Forall_out {A P l} _.

Notation Forall' P := (ForallF (Forall P) P).

Inductive Exists' {A : Type} (P : A -> Prop) : Colist' A -> Prop :=
| Exists'_zero : forall {h : A} (t : Colist A), P h -> Exists' P (CoconsF h t)
| Exists'_succ : forall (h : A) {t : Colist A}, Exists' P (out t) -> Exists' P (CoconsF h t).

Arguments Exists'_zero {A P h} _ _.
Arguments Exists'_succ {A P} _ {t} _.

Definition Exists {A : Type} (P : A -> Prop) (l : Colist A) : Prop :=
  Exists' P (out l).

Arguments Exists {A} P l /.

Variant ForallSubF
  {A : Type} (F : Colist A -> Prop) (P : Colist A -> Prop)
  (l : Colist A) : Prop :=
| ForallSubF_ConilF  : out l = ConilF -> P l -> ForallSubF F P l
| ForallSubF_CoconsF :
    forall {h : A} {t : Colist A},
      out l = CoconsF h t -> P l -> F t -> ForallSubF F P l.

Arguments ForallSubF_ConilF  {A F P l} _ _.
Arguments ForallSubF_CoconsF {A F P l h t} _ _ _.

CoInductive ForallSub {A : Type} (P : Colist A -> Prop) (l : Colist A) : Prop :=
{
  ForallSub_out : ForallSubF (ForallSub P) P l;
}.

Arguments ForallSub_out {A P l} _.

Notation ForallSub' P := (ForallSubF (ForallSub P) P).

Inductive ExistsSub' {A : Type} (P : Colist A -> Prop) : Colist' A -> Prop :=
| ExistsSub'_here : forall l, P (MkColist l) -> ExistsSub' P l
| ExistsSub'_skip : forall (h : A) {t}, ExistsSub' P (out t) -> ExistsSub' P (CoconsF h t).

Arguments ExistsSub'_here {A P l} _.
Arguments ExistsSub'_skip {A P} _ {t} _.

Definition ExistsSub {A : Type} (P : Colist A -> Prop) (l : Colist A) : Prop :=
  ExistsSub' P (out l).

Definition InfinitelyOften {A : Type} (P : A -> Prop) : Colist A -> Prop :=
  ForallSub (fun l => Exists P l).

Definition EventuallyAlways {A : Type} (P : A -> Prop) : Colist A -> Prop :=
  ExistsSub (Forall P).

CoFixpoint app {A : Type} (l1 l2 : Colist A) : Colist A :=
match out l1 with
| ConilF => l2
| CoconsF h t => Cocons h (app t l2)
end.

Fixpoint prepend {A : Type} (l1 : list A) (l2 : Colist A) : Colist A :=
match l1 with
| [] => l2
| h :: t => Cocons h (prepend t l2)
end.

CoFixpoint map {A B : Type} (f : A -> B) (l : Colist A) : Colist B :=
match out l with
| ConilF => Conil
| CoconsF h t => Cocons (f h) (map f t)
end.

Fixpoint take {A : Type} (l : Colist A) (n : nat) : list A :=
match n, out l with
| 0, _ => []
| _, ConilF => []
| S n', CoconsF h t => h :: take t n'
end.

Fixpoint drop {A : Type} (l : Colist A) (n : nat) : Colist A :=
match n, out l with
| 0, _ => l
| _, ConilF => Conil
| S n', CoconsF h t => drop t n'
end.

Fixpoint nth {A : Type} (l : Colist A) (n : nat) : option A :=
match n, out l with
| _, ConilF => None
| 0, CoconsF h _ => Some h
| S n', CoconsF _ t => nth t n'
end.

Definition segment {A : Type} (l : Colist A) (n1 n2 : nat) : list A :=
  D5.drop n1 (take l n2).

Fixpoint list_to_colist {A : Type} (l : list A) : Colist A :=
match l with
| [] => Conil
| h :: t => Cocons h (list_to_colist t)
end.

(*
Definition ne_list_to_colist {A : Type} (l : ne_list A) : Colist A :=
  list_to_colist (ne_list_to_list l).
*)

CoFixpoint concat {A : Type} (l : Colist (A * list A)) : Colist A :=
match out l with
| ConilF => Conil
| CoconsF h t =>
    Cocons (fst h)
      match snd h with
      | [] => concat t
      | x :: xs => concat (Cocons (x, xs) t)
      end
end.

Lemma Bisim_gfp :
  forall {A : Type} (R : Colist A -> Colist A -> Prop),
    (forall l1 l2, R l1 l2 -> BisimF R (out l1) (out l2)) ->
      (forall l1 l2, R l1 l2 -> Bisim l1 l2).
Proof.
  intros A R HR.
  cofix CH.
  intros l1 l2 H; constructor.
  apply HR in H as []; constructor; [easy |].
  now apply CH.
Qed.

Lemma Bisim_refl :
  forall {A : Type} (l : Colist A),
    Bisim l l.
Proof.
  cofix CH.
  constructor.
  destruct (out l) as [| h t]; constructor; [easy |].
  now apply CH.
Qed.

Lemma Bisim_sym :
  forall {A : Type} {l1 l2 : Colist A},
    Bisim l1 l2 -> Bisim l2 l1.
Proof.
  cofix CH.
  intros A l1 l2 [HB].
  constructor; inversion HB; constructor; [easy |].
  now apply CH.
Qed.

Lemma Bisim_trans :
  forall {A : Type} {l1 l2 l3 : Colist A},
    Bisim l1 l2 -> Bisim l2 l3 -> Bisim l1 l3.
Proof.
  cofix CH.
  intros A l1 l2 l3 [H12] [H23].
  constructor; inversion H12; inversion H23; [now constructor | now congruence.. |].
  constructor; [now congruence |].
  now apply CH with t2; [| congruence].
Qed.

#[export] Instance Equivalence_Bisim (A : Type) : Equivalence (@Bisim A).
Proof.
  split; red.
  - now apply Bisim_refl.
  - now apply @Bisim_sym.
  - now apply @Bisim_trans.
Qed.

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

Lemma Exists_iff :
  forall {A : Type} (P Q : A -> Prop) (l : Colist A),
    (forall x : A, P x <-> Q x) ->
      Exists P l <-> Exists Q l.
Proof.
  now intros A P Q l Hiff; split; apply Exists_impl, Hiff.
Qed.

Lemma Forall_impl :
  forall {A : Type} {P Q : A -> Prop} (l : Colist A),
    (forall x : A, P x -> Q x) ->
      Forall P l -> Forall Q l.
Proof.
  cofix CH.
  intros A P Q l HPQ [HF]; constructor; inversion HF; [now constructor |].
  constructor.
  - now apply HPQ.
  - now eapply CH; eassumption.
Qed.

Lemma Forall_iff :
  forall {A : Type} {P Q : A -> Prop} (l : Colist A),
    (forall x : A, P x <-> Q x) ->
      Forall P l <-> Forall Q l.
Proof.
  now intros A P Q l Hiff; split; apply Forall_impl, Hiff.
Qed.

Lemma ExistsSub_impl :
  forall {A : Type} {P Q : Colist A -> Prop} (l : Colist A),
    (forall x : Colist A, P x -> Q x) ->
      ExistsSub P l -> ExistsSub Q l.
Proof.
  unfold ExistsSub.
  induction 2.
  - now constructor; apply H.
  - now constructor 2.
Qed.

Lemma ExistsSub_iff :
  forall {A : Type} {P Q : Colist A -> Prop} (l : Colist A),
    (forall x : Colist A, P x <-> Q x) ->
      ExistsSub P l <-> ExistsSub Q l.
Proof.
  intros A P Q l Hiff; split; apply ExistsSub_impl, Hiff.
Qed.

Lemma ForallSub_impl :
  forall {A : Type} (P Q : Colist A -> Prop) (l : Colist A),
    (forall x : Colist A, P x -> Q x) ->
      ForallSub P l -> ForallSub Q l.
Proof.
  cofix CH.
  intros A P Q l Hiff [[]]; constructor.
  - now constructor; [| apply Hiff].
  - econstructor 2; [eassumption | now apply Hiff |].
    now eapply CH; eassumption.
Qed.

Lemma ForallSub_iff :
  forall {A : Type} (P Q : Colist A -> Prop) (l : Colist A),
    (forall x : Colist A, P x <-> Q x) ->
      ForallSub P l <-> ForallSub Q l.
Proof.
  now intros A P Q l Hiff; split; apply ForallSub_impl, Hiff.
Qed.

Lemma InfinitelyOften_impl :
  forall {A : Type} (P Q : A -> Prop) (l : Colist A),
    (forall x : A, P x -> Q x) ->
      InfinitelyOften P l -> InfinitelyOften Q l.
Proof.
  intros A P Q l Hiff.
  apply ForallSub_impl; intros x.
  now apply Exists_impl.
Qed.

Lemma InfinitelyOften_iff :
  forall {A : Type} (P Q : A -> Prop) (l : Colist A),
    (forall x : A, P x <-> Q x) ->
      InfinitelyOften P l <-> InfinitelyOften Q l.
Proof.
  intros A P Q l Hiff.
  apply ForallSub_iff; intros x.
  now apply Exists_iff.
Qed.

Lemma EventuallyAlways_impl :
  forall {A : Type} {P Q : A -> Prop} (l : Colist A),
    (forall x : A, P x -> Q x) ->
      EventuallyAlways P l -> EventuallyAlways Q l.
Proof.
  unfold EventuallyAlways.
  intros A P Q l Himpl Hex.
  eapply ExistsSub_impl.
  - now intros x; eapply Forall_impl, Himpl.
  - now apply Hex.
Qed.

Lemma EventuallyAlways_iff :
  forall {A : Type} {P Q : A -> Prop} (l : Colist A),
    (forall x : A, P x <-> Q x) ->
      EventuallyAlways P l <-> EventuallyAlways Q l.
Proof.
  now intros; apply ExistsSub_iff; intros x; apply Forall_iff.
Qed.

Lemma EventuallyAlways_Conil :
  forall {A : Type} (P : A -> Prop) (l : Colist A),
    out l = ConilF -> EventuallyAlways P l.
Proof.
  intros A P l Heq.
  do 2 constructor; cbn.
  rewrite Heq.
  now constructor.
Qed.

Lemma app_Conil :
  forall {A : Type} (l : Colist A),
    Bisim (app Conil l) l.
Proof.
  constructor; cbn.
  now apply Bisim_refl.
Qed.

Lemma app_Cocons :
  forall {A : Type} (h : A) (t l : Colist A),
    Bisim (app (Cocons h t) l) (Cocons h (app t l)).
Proof.
  now constructor; cbn; constructor.
Qed.

Lemma drop_Cocons :
  forall {A : Type} (h : A) (t l : Colist A) (n : nat),
    out l = CoconsF h t ->
      drop l (S n) = drop t n.
Proof.
  now cbn; intros A h t l n ->.
Qed.

Lemma take_Conil :
  forall {A : Type} (l : Colist A) (n : nat),
    out l = ConilF -> take l n = [].
Proof.
  now intros A l [| n']; cbn; [| intros ->].
Qed.

Lemma nth_Conil :
  forall {A : Type} (l : Colist A) (n : nat),
    out l = ConilF -> nth l n = None.
Proof.
  now intros A l [| n']; cbn; intros ->.
Qed.

Lemma prepend_take_drop :
  forall {A : Type} (n : nat) (l : Colist A),
    Bisim (prepend (take l n) (drop l n)) l.
Proof.
  induction n as [| n']; cbn; [easy |]; intros.
  constructor.
  destruct (out l) as [| h t]; cbn; constructor; [easy |].
  now apply IHn'.
Qed.

Lemma prepend_take_nth_drop :
  forall {A : Type} (n : nat) (l : Colist A) (x : A),
    nth l n = Some x ->
      Bisim (prepend (take l n) (Cocons x (drop l (S n)))) l.
Proof.
  induction n as [| n']; cbn; intros; constructor;
    destruct (out l) as [| h t]; cbn; inversion H; subst.
  - now apply (Bisim_refl (Cocons x t)).
  - now constructor; [| apply IHn'].
Qed.

Lemma take_plus :
  forall {A : Type} (n m : nat) (l : Colist A),
    take l (n + m) = take l n ++ take (drop l n) m.
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  destruct (out l) as [| h t]; cbn.
  - now rewrite take_Conil.
  - now rewrite IHn'.
Qed.

Lemma take_map :
  forall {A B : Type} (f : A -> B) (n : nat) (l : Colist A),
    D5.map f (take l n) = take (map f l) n.
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  destruct (out l) as [| h t]; cbn; [easy |].
  now rewrite IHn'.
Qed.

(*
Lemma take_nth :
  forall {A : Type} (n i : nat) (l : Colist A),
    i < n -> List.nth_error (take l n) i = nth l i.
Proof.
  induction n as [| n']; cbn; intros; [now lia |].
  destruct (out l) as [| h t] eqn: Heq; cbn.
  - now destruct i; cbn; rewrite Heq.
  - destruct i as [| i']; cbn; rewrite Heq; [easy |].
    now apply IHn'; lia.
Qed.
*)

Lemma nth_map :
  forall {A B : Type} (f : A -> B) (n : nat) (l : Colist A),
    nth (map f l) n = option_map f (nth l n).
Proof.
  induction n as [| n']; cbn; intros;
    destruct (out l) as [| h t]; cbn; [easy.. |].
  now apply IHn'.
Qed.

Lemma prepend_app :
  forall {A : Type} (l1 l2 : list A) (l3 : Colist A),
    prepend (l1 ++ l2) l3 = prepend l1 (prepend l2 l3).
Proof.
  now induction l1 as [| h1 t1 IH]; cbn; intros; [| rewrite IH].
Qed.

Lemma prepend_Cocons :
  forall {A : Type} (l : list A) (h : A) (t : Colist A),
    prepend l (Cocons h t) = prepend (l ++ [h]) t.
Proof.
  now induction l as [| h t IH]; cbn; intros; [| rewrite IH].
Qed.

Lemma take_prepend_length :
  forall {A : Type} (l1 : list A) (l2 : Colist A),
    take (prepend l1 l2) (length l1) = l1.
Proof.
  now induction l1 as [| h1 t1 IH]; cbn; intros; [| rewrite IH].
Qed.

Lemma take_prepend_plus_length :
  forall {A : Type} (l1 : list A) (l2 : Colist A) (n : nat),
    take (prepend l1 l2) (length l1 + n) = l1 ++ take l2 n.
Proof.
  now induction l1 as [| h1 t1 IH]; cbn; intros; [| rewrite IH].
Qed.

Lemma nth_prepend_length :
  forall {A : Type} (l1 : list A) (h : A) (t : Colist A),
    nth (prepend l1 (Cocons h t)) (length l1) = Some h.
Proof.
  now induction l1 as [| h1 t1 IH]; cbn; intros; [| rewrite IH].
Qed.

Lemma last_take :
  forall {A : Type} (n : nat) (l : Colist A),
    nth l n <> None ->
      last (take l (S n)) = nth l n.
Proof.
  induction n as [| n']; cbn; intros l H;
    destruct (out l) as [| h t]; cbn; [easy.. |].
  destruct (out t) as [| h' t'] eqn: Heq; cbn; intros.
  - now rewrite nth_Conil in H.
  - now rewrite <- IHn'; cbn; rewrite ?Heq; [| easy].
Qed.

Lemma segment_diag :
  forall {A : Type} (n : nat) (l : Colist A),
    segment l n n = [].
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  now destruct (out l) as [| h t]; cbn; [| apply IHn'].
Qed.

(*
Lemma nth_le :
  forall {A : Type} (l : Colist A) (n m : nat),
    n <= m -> nth l m <> None -> nth l n <> None.
Proof.
  intros A l n m [k ->]%Nat.le_sum; revert l k.
  induction n as [| n']; cbn; intros;
    destruct (out l) as [| h t] eqn: Heq; [| easy | easy |].
  - now rewrite nth_Conil in H.
  - now eapply IHn'.
Qed.
*)

Lemma length_take_ge :
  forall {A : Type} (n : nat) (l : Colist A),
    length (take l n) <= n.
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  destruct (out l) as [| h t]; cbn; [now lia |].
  now specialize (IHn' t); lia.
Qed.

Lemma length_take :
  forall {A : Type} (n : nat) (l : Colist A),
    nth l n <> None -> length (take l n) = n.
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  destruct (out l) as [| h t]; cbn; [easy |].
  now rewrite IHn'.
Qed.

Lemma length_take_nth_lt :
  forall {A : Type} (n m : nat) (l : Colist A),
    nth l m <> None -> m < n -> m < length (take l n).
Proof.
  induction n as [| n']; cbn; intros; [easy |].
  destruct (out l) as [| h t] eqn: Heq; cbn.
  - now rewrite nth_Conil in H.
  - destruct m as [| m']; cbn in H; rewrite Heq in H; [now lia |].
    now specialize (IHn' _ _ H); lia.
Qed.

Lemma length_take_le :
  forall {A : Type} (n m : nat) (l : Colist A),
    n <= m -> length (take l n) <= length (take l m).
Proof.
  induction n as [| n']; cbn; intros; [now lia |].
  destruct m as [| m']; cbn; [now lia |].
  destruct (out l) as [| h t]; cbn; [now lia |].
  now specialize (IHn' m' t); lia.
Qed.

Lemma length_take_nth_le :
  forall {A : Type} (l : Colist A) (n m : nat),
    nth l m <> None -> m <= n -> m <= length (take l n).
Proof.
  intros; transitivity (length (take l m)).
  - now rewrite length_take.
  - now apply length_take_le.
Qed.

Lemma take_S_nth :
  forall {A : Type} (n : nat) (l : Colist A) (x : A),
    nth l n = Some x -> take l (S n) = take l n ++ [x].
Proof.
  induction n as [| n']; cbn; intros.
  - now destruct (out l); congruence.
  - destruct (out l) as [| h t]; cbn; [now congruence |].
    now cbn in IHn'; rewrite (IHn' t x H).
Qed.

Lemma take_concat_Cocons :
  forall {A : Type} (x : A) (xs : list A) (t : Colist (A * list A)) (n : nat),
    take (concat (Cocons (x, xs) t)) (1 + length xs + n) = x :: xs ++ take (concat t) n.
Proof.
  intros A x xs; revert x.
  induction xs as [| x' xs']; intros; [easy |].
  now cbn; rewrite <- IHxs'.
Qed.
