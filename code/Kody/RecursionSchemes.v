(** * Ordinary inductive types *)

Module NatF.

Inductive NatF (X : Type) : Type :=
    | Zero : NatF X
    | Succ : X -> NatF X.

Arguments Zero {X}.
Arguments Succ {X} _.

Inductive Nat : Type :=
    | In : NatF Nat -> Nat.

Fixpoint f (n : nat) : Nat :=
match n with
    | 0 => In Zero
    | S n' => In (Succ (f n'))
end.

Fixpoint g (n : Nat) : nat :=
match n with
    | In Zero => 0
    | In (Succ n') => S (g n')
end.

Lemma fg :
  forall n : nat,
    g (f n) = n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    f_equal. assumption.
Qed.

Lemma gf :
  forall n : Nat,
    f (g n) = n.
Proof.
  fix IH 1.
  destruct n as [[| n']]; cbn.
    reflexivity.
    do 2 f_equal. apply IH.
Qed.

End NatF.

(** * Parameterized types *)

Module BTree.

Inductive BTree (A : Type) : Type :=
    | E : BTree A
    | N : A -> BTree A -> BTree A -> BTree A.

Arguments E {A}.
Arguments N {A} _ _ _.

Module BTreeF.

Inductive BTreeF (F : Type -> Type) (A : Type) : Type :=
    | EF : BTreeF F A
    | NF : A -> F A -> F A -> BTreeF F A.

Arguments EF {F A}.
Arguments NF {F A} _ _ _.

Inductive BTree' (A : Type) : Type :=
    | In : BTreeF BTree' A -> BTree' A.

Arguments In {A} _.

Fixpoint f {A : Type} (t : BTree A) : BTree' A :=
match t with
    | E       => In EF
    | N v l r => In (NF v (f l) (f r))
end.

Fixpoint g {A : Type} (t : BTree' A) : BTree A :=
match t with
    | In EF => E
    | In (NF v l r) => N v (g l) (g r)
end.

Lemma fg :
  forall {A : Type} (t : BTree A), g (f t) = t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : BTree' A), f (g t) = t.
Proof.
  fix IH 2.
  destruct t as [[]]; cbn.
    reflexivity. rewrite !IH. reflexivity.
Qed.

End BTreeF.

(** Na ten wariant w Haskellu mówią "Recursion Schemes". *)
Module BTreeR.

Inductive BTreeR (A R : Type) : Type :=
    | ER : BTreeR A R
    | NR : A -> R -> R -> BTreeR A R.

Arguments ER {A R}.
Arguments NR {A R} _ _ _.

Inductive BTree' (A : Type) : Type :=
    | In : BTreeR A (BTree' A) -> BTree' A.

Arguments In {A} _.

Fixpoint f {A : Type} (t : BTree A) : BTree' A :=
match t with
    | E       => In ER
    | N v l r => In (NR v (f l) (f r))
end.

Fixpoint g {A : Type} (t : BTree' A) : BTree A :=
match t with
    | In ER         => E
    | In (NR v l r) => N v (g l) (g r)
end.

Lemma fg :
  forall {A : Type} (t : BTree A), g (f t) = t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : BTree' A), f (g t) = t.
Proof.
  fix IH 2.
  destruct t as [[]]; cbn.
    reflexivity. rewrite !IH. reflexivity.
Qed.

End BTreeR.

End BTree.

(** * Mutual inductive types *)

Module FinitaryTreeF.

Inductive Tree (A : Type) : Type :=
    | Empty : Tree A
    | Node  : A -> Forest A -> Tree A

with Forest (A : Type) : Type :=
    | Nil  : Forest A
    | Cons : Tree A -> Forest A -> Forest A.

Inductive TreeF (T F : Type -> Type) (A : Type) : Type :=
    | EmptyF : TreeF T F A
    | NodeF  : A -> T A -> TreeF T F A

with ForestF (T F : Type -> Type) (A : Type) : Type :=
    | NilF  : ForestF T F A
    | ConsF : T A -> F A -> ForestF T F A.

Unset Positivity Checking.
Fail Inductive Tree' (A : Type) : Type :=
    | InT : TreeF Tree' Forest' A -> Tree' A

with Forest' (A : Type) : Type :=
    | InF : ForestF Tree' Forest' A -> Forest' A.
Set Positivity Checking.

End FinitaryTreeF.

(** * Indexed families *)

Require Import List.
Import ListNotations.

Require Import F3 F4.

Inductive ListF (F : Type -> Type) (A : Type) : Type :=
    | NilF : ListF F A
    | ConsF : A -> F A -> ListF F A.

Arguments NilF  {F A}.
Arguments ConsF {F A} _ _.

Inductive List (A : Type) : Type :=
    | In : ListF List A -> List A.

Arguments In {A} _.

Lemma List_ind' :
  forall
    {A : Type} (P : List A -> Prop)
    (HNil : P (In NilF))
    (HCons : forall (h : A) (t : List A), P t -> P (In (ConsF h t)))
    (l : List A), P l.
Proof.
  fix IH 5.
  destruct l as [[| h t]].
    exact HNil.
    apply HCons, IH; assumption.
Qed.

Fixpoint list_List {A : Type} (l : list A) : List A :=
match l with
    | [] => In NilF
    | h :: t => In (ConsF h (list_List t))
end.

Fixpoint List_list {A : Type} (l : List A) : list A :=
match l with
    | In NilF => []
    | In (ConsF h t) => h :: List_list t
end.

Lemma list_List_list :
  forall {A : Type} (l : list A),
    List_list (list_List l) = l.
Proof.
  induction l as [| h t]; cbn;
  rewrite ?IHt; reflexivity.
Qed.

Lemma List_list_List :
  forall {A : Type} (l : List A),
    list_List (List_list l) = l.
Proof.
  intros.
  induction l using List_ind'; cbn.
    reflexivity.
    rewrite IHl. reflexivity.
Qed.

CoInductive CoList (A : Type) : Type :=
{
    Out : ListF CoList A;
}.

Arguments Out {A} _.

CoFixpoint coList_CoList {A : Type} (l : coList A) : CoList A :=
{|
    Out :=
      match uncons l with
          | None        => NilF
          | Some (h, t) => ConsF h (coList_CoList t)
      end
|}.

CoFixpoint CoList_coList {A : Type} (l : CoList A) : coList A :=
{|
    uncons :=
      match Out l with
          | NilF      => None
          | ConsF h t => Some (h, CoList_coList t)
      end
|}.

Lemma coList_CoList_coList :
  forall {A : Type} (l : coList A),
    lsim (CoList_coList (coList_CoList l)) l.
Proof.
  cofix CH.
  destruct l as [[[h t] |]];
  constructor; cbn.
    right. do 4 eexists. do 3 (split; try reflexivity). apply CH.
    left. split; reflexivity.
Qed.

CoInductive CoList_sim {A : Type} (l1 l2 : CoList A) : Prop :=
{
    CoList_sim' :
      (Out l1 = NilF /\ Out l2 = NilF)
        \/
      exists h1 t1 h2 t2,
        Out l1 = ConsF h1 t1 /\
        Out l2 = ConsF h2 t2 /\
          CoList_sim t1 t2
}.

Lemma CoList_coList_CoList :
  forall {A : Type} (l : CoList A),
    CoList_sim (coList_CoList (CoList_coList l)) l.
Proof.
  cofix CH.
  destruct l as [[| h t]];
  constructor; cbn.
    left. split; reflexivity.
    right. do 4 eexists. do 2 (split; try reflexivity). apply CH.
Qed.

Inductive ForallF
  {A : Type} (R : A -> A -> Prop)
  (F : (A -> A -> Prop) -> CoList A -> CoList A -> Prop)
  : CoList A -> CoList A -> Prop :=
    | Nils  :
        forall l1 l2 : CoList A,
          Out l1 = NilF -> Out l2 = NilF -> ForallF R F l1 l2
    | Conss :
        forall (l1 l2 : CoList A) (h1 h2 : A) (t1 t2 : CoList A),
          Out l1 = ConsF h1 t1 -> Out l2 = ConsF h2 t2 ->
            R h1 h2 -> F R t1 t2 -> ForallF R F l1 l2.

CoInductive CoForall {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
{
    Out' : ForallF eq CoForall l1 l2
}.

Lemma CoList_coList_CoList' :
  forall {A : Type} (l : CoList A),
    CoForall eq (coList_CoList (CoList_coList l)) l.
Proof.
  cofix CH.
  constructor.
  destruct l as [[| h t]].
    constructor; cbn; reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.