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

(** In Haskell they call this variant "Recursion Schemes". *)
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

Fail Inductive Tree' (A : Type) : Type :=
    | InT : TreeF Tree' Forest' A -> Tree' A

with Forest' (A : Type) : Type :=
    | InF : ForestF Tree' Forest' A -> Forest' A.

Inductive TreeR (A : Type) : Type -> Type :=
    | EmptyR : forall F, TreeR A F
    | NodeR  : forall F, A -> F -> TreeR A F

with ForestR (A : Type) : Type -> Type -> Type :=
    | NilR  : forall T F, ForestR A T F
    | ConsR : forall T F, T -> F -> ForestR A T F.

Fail Inductive Tree' (A : Type) : Type :=
    | InT : TreeR A (Forest' A) -> Tree' A

with Forest' (A : Type) : Type :=
    | InF : ForestR A (Tree' A) (Forest' A) -> Forest' A.

End FinitaryTreeF.

(** * Indexed families *)

Require Import List.
Import ListNotations.

Require Import F3 F4.

Module ListCoList.

Inductive ListF (F : Type -> Type) (A : Type) : Type :=
    | NilF : ListF F A
    | ConsF : A -> F A -> ListF F A.

Arguments NilF  {F A}.
Arguments ConsF {F A} _ _.

Module List.

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

Fixpoint f {A : Type} (l : list A) : List A :=
match l with
    | [] => In NilF
    | h :: t => In (ConsF h (f t))
end.

Fixpoint g {A : Type} (l : List A) : list A :=
match l with
    | In NilF => []
    | In (ConsF h t) => h :: g t
end.

Lemma fg :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  induction l as [| h t]; cbn;
  rewrite ?IHt; reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (l : List A),
    f (g l) = l.
Proof.
  intros.
  induction l using List_ind'; cbn.
    reflexivity.
    rewrite IHl. reflexivity.
Qed.

End List.

Module CoList.

CoInductive CoList (A : Type) : Type :=
{
    Out : ListF CoList A;
}.

Arguments Out {A} _.

CoFixpoint f {A : Type} (l : coList A) : CoList A :=
{|
    Out :=
      match uncons l with
          | None        => NilF
          | Some (h, t) => ConsF h (f t)
      end
|}.

CoFixpoint g {A : Type} (l : CoList A) : coList A :=
{|
    uncons :=
      match Out l with
          | NilF      => None
          | ConsF h t => Some (h, g t)
      end
|}.

Lemma fg :
  forall {A : Type} (l : coList A),
    lsim (g (f l)) l.
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

Lemma gf :
  forall {A : Type} (l : CoList A),
    CoList_sim (f (g l)) l.
Proof.
  cofix CH.
  destruct l as [[| h t]];
  constructor; cbn.
    left. split; reflexivity.
    right. do 4 eexists. do 2 (split; try reflexivity). apply CH.
Qed.

Module CoList_ForallF.

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
    Out' : ForallF R CoForall l1 l2
}.

Lemma gf' :
  forall {A : Type} (l : CoList A),
    CoForall eq (f (g l)) l.
Proof.
  cofix CH.
  constructor.
  destruct l as [[| h t]].
    constructor; cbn; reflexivity.
    eright; cbn; try reflexivity. apply CH.
Qed.

End CoList_ForallF.

End CoList.

End ListCoList.

(** * Indexed families, but reduced to parameterized types through equality constraints *)

Module ListCoList2.

Inductive ListR (A R : Type) : Type :=
    | NilR  : ListR A R
    | ConsR : A -> R -> ListR A R.

Arguments NilR  {A R}.
Arguments ConsR {A R} _ _.

Inductive List (A : Type) : Type :=
    | In : ListR A (List A) -> List A.

Arguments In {A} _.

CoInductive CoList (A : Type) : Type :=
{
    Out : ListR A (CoList A);
}.

Arguments Out {A} _.

(** We can halve the amount of work to define many useful type families by just
    reusing templates operating on the "underlying functor", like below. *)

Inductive ForallR
  {A R : Type}
  (Unwrap : R -> ListR A R)
  (RA : A -> A -> Prop)
  (RR : R -> R -> Prop)
  (l1 l2 : R)
  : Prop :=
    | Nils  :
        Unwrap l1 = NilR -> Unwrap l2 = NilR -> ForallR Unwrap RA RR l1 l2
    | Conss :
        forall (h1 h2 : A) (t1 t2 : R),
          Unwrap l1 = ConsR h1 t1 -> Unwrap l2 = ConsR h2 t2 ->
            RA h1 h2 -> RR t1 t2 -> ForallR Unwrap RA RR l1 l2.

Definition uncons {A : Type} (l : List A) : ListR A (List A) :=
match l with
    | In x => x
end.

Inductive Forall {A : Type} (R : A -> A -> Prop) (l1 l2 : List A) : Prop :=
    | InForall : ForallR uncons R (Forall R) l1 l2 -> Forall R l1 l2.

CoInductive CoForall {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
{
    Out' : ForallR Out R (CoForall R) l1 l2
}.

Inductive ExistsR
  {A L : Type}
  (Uncons : L -> ListR A L)
  (RA : A -> A -> Prop)
  (RL : L -> L -> Prop)
  (l1 l2 : L)
  : Prop :=
    | Here  :
        forall (h1 h2 : A) (t1 t2 : L),
          Uncons l1 = ConsR h1 t1 -> Uncons l2 = ConsR h2 t2 ->
            RA h1 h2 -> ExistsR Uncons RA RL l1 l2
    | There :
        forall (h1 h2 : A) (t1 t2 : L),
          Uncons l1 = ConsR h1 t1 -> Uncons l2 = ConsR h2 t2 ->
            RL t1 t2 -> ExistsR Uncons RA RL l1 l2.

Inductive Exists {A : Type} (R : A -> A -> Prop) (l1 l2 : List A) : Prop :=
    | InExists : ExistsR uncons R (Exists R) l1 l2 -> Exists R l1 l2.

Inductive CoExists {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
    | InCoExists : ExistsR Out R (CoExists R) l1 l2 -> CoExists R l1 l2.

(** Maybe we can define generic functions? *)

Fixpoint cata {A R : Type} (f : ListR A R -> R) (l : List A) : R :=
match l with
    | In NilR        => f NilR
    | In (ConsR h t) => f (ConsR h (cata f t))
end.

CoFixpoint ana {A R : Type} (f : R -> ListR A R) (r : R) : CoList A :=
{|
    Out :=
      match f r with
          | NilR      => NilR
          | ConsR h t => ConsR h (ana f t)
      end
|}.


End ListCoList2.