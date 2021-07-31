Require Import List.
Import ListNotations.

Require Import F3 F4.

(** * Least and greatest fixpoint of a functor *)

Unset Positivity Checking.

(** If we turn off positivity checking, we can define types that represent the
    least and the greatest fixed point of a functor [F : Type -> Type]. *)

Inductive Mu (F : Type -> Type) : Type :=
    | In : F (Mu F) -> Mu F.

Arguments In {F} _.

(** Let's take a look at [Mu]. The single constructor [In] establishes an
    isomorphism between [F (Mu f)] and [Mu F], which means that [Mu F] is
    a fixed point of [F]. [Mu] is an inductive type, which guarantees that
    it is the least fixpoint of [F]. *)

CoInductive Nu (F : Type -> Type) : Type :=
{
    Out : F (Nu F);
}.

Arguments Out {F} _.

(** For [Nu] things are exactly dual. The field [Out] establishes an isomorphism
    between [Nu F] and [F (Nu F)], which makes [Nu F] into a fixpoint of [F].
    Because [Nu] is coinductive, this fixpoint is the greatest one. *)

Set Positivity Checking.

(** How de we use [Mu] and [Nu] to define inductive and coinductive types?
    That's easy: we just need to define a functor of type [Type -> Type] and
    apply [Mu] or [Nu] to it. The most interesting functors can be defined
    as inductive families. *)

Inductive ListR (A X : Type) : Type :=
    | NilF  : ListR A X
    | ConsF : A -> X -> ListR A X.

Arguments NilF  {A X}.
Arguments ConsF {A X} _ _.

(** [ListR] represents the polynomial functor [fun X => 1 + A * X]. It is the
    underlying functor of the [list] and [CoList] types, which means that
    [list = Mu (ListR A)] and [CoList = Nu (ListR A)]. Let's see how this
    works in more detail. *)

Module List.

Definition List (A : Type) : Type := Mu (ListR A).

(** Defining [List A] using [ListR] is easy enough... *)

Unset Guard Checking.
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
Set Guard Checking.

(** ... but to derive the induction principle for [List A], we need to turn off
    the termination checker. This is because [Mu] is a non-strictly-positive
    type, so the termination can't see that our definition is indeed terminating. *)

Fixpoint f {A : Type} (l : list A) : List A :=
match l with
    | [] => In NilF
    | h :: t => In (ConsF h (f t))
end.

(** We can easily convert a [list A] (the good old one, defined without any
    fixpoints) into a [List A] (the new one, defined using [Mu]. *)

Unset Guard Checking.
Fixpoint g {A : Type} (l : List A) {struct l} : list A :=
match l with
    | In NilF        => []
    | In (ConsF h t) => h :: g t
end.
Set Guard Checking.

(** But to convert [List A] into [list A], we either need to use our induction
    principle (which made us turn off the termination checker) or turn the
    termination checker once again and manually implement it as an ordinary
    recursive function. *)

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

(** Proving that [list A] and [List A] are isomorphic is easy. But the whole
    development is unsatisfactory, because we need to cheat to get through
    positivity and termination checks. *)

End List.

(** * Least and greatest fixpoints revisited *)

Module List'.

Inductive List (A : Type) : Type :=
    | In : ListR A (List A) -> List A.

Arguments In {A} _.

(** It's much better to "tie the knot" (as these kinds of techniques are often
    called informally) manually, by instantiating the [F] from the definition
    of [Mu] with [ListR A] and [Mu F] with [List A]. This way we don't need to
    turn off the positivity checker. *)

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

(** Now we can also derive the induction principle without having to turn off
    the termination checker. *)

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

(** Similarly, we are free to define recursive function in the usual way without
    having to worry about termination checking. *)

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

End List'.

(** * Underlying functors of commonly used types *)

(** * Ordinary inductive types *)

(** With what we learned up to now, it shouldn't be hard to define the underlying
    functor of the natural numbers. *)

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

(** We have seen lists, but let's also take a quick glance at binary trees. *)

Module BTree.

Inductive BTree (A : Type) : Type :=
    | E : BTree A
    | N : A -> BTree A -> BTree A -> BTree A.

Arguments E {A}.
Arguments N {A} _ _ _.

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

(** Haskellers call the above approach to underlying functors "Recursion Schemes".
    It's nice, but as we shall see soon, there are some situations when it breaks
    down due to universe inconsistencies. Below we present a slightly modified
    approach. *)

Module BTreeF.

Inductive BTreeF (F : Type -> Type) (A : Type) : Type :=
    | EF : BTreeF F A
    | NF : A -> F A -> F A -> BTreeF F A.

Arguments EF {F A}.
Arguments NF {F A} _ _ _.

(** Note that this time our parameters are not two types [A] and [R], but a
    functor [F : Type -> Type] and a type [A]. This way, we represent subtrees
    with [F A] instead of [R]. Besides this little difference, everything else
    stays virtually the same. *)

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

End BTree.

(** * Mutual inductive types *)

(** (TODO: odkłamać) It's high time to see the promised breakdown of the Haskell-like approach.
    The best setting for this are mutual inductive types. *)

Module FinitaryTreeF.

Inductive Tree (A : Type) : Type :=
    | Empty : Tree A
    | Node  : A -> Forest A -> Tree A

with Forest (A : Type) : Type :=
    | Nil  : Forest A
    | Cons : Tree A -> Forest A -> Forest A.

Arguments Empty {A}.
Arguments Node  {A} _ _.

Arguments Nil   {A}.
Arguments Cons  {A} _ _.

(** We want a type of trees that can be empty or be a node holding an element
    that can have a finite number of subtrees that are collected into a list. *)

Inductive TreeR (A F : Type) : Type :=
    | EmptyR : TreeR A F
    | NodeR  : A -> F -> TreeR A F.

Inductive ForestR (A F T : Type) : Type :=
    | NilR  : ForestR A F T
    | ConsR : T -> F -> ForestR A F T.

Arguments EmptyR {A F}.
Arguments NodeR  {A F} _ _.

Arguments NilR   {A F T}.
Arguments ConsR  {A F T} _ _.

Module TreeR.

Inductive Tree' (A : Type) : Type :=
    | InT : TreeR A (Forest' A) -> Tree' A

with Forest' (A : Type) : Type :=
    | InF : ForestR A (Forest' A) (Tree' A) -> Forest' A.

Arguments InT {A} _.

Arguments InF {A} _.

Fixpoint f {A : Type} (t : Tree A) : Tree' A :=
match t with
    | Empty     => InT EmptyR
    | Node x ts => InT (NodeR x (fs ts))
end

with fs {A : Type} (ts : Forest A) : Forest' A :=
match ts with
    | Nil        => InF NilR
    | Cons t ts' => InF (ConsR (f t) (fs ts'))
end.

Fixpoint g {A : Type} (t : Tree' A) : Tree A :=
match t with
    | InT EmptyR       => Empty
    | InT (NodeR x ts) => Node x (gs ts)
end

with gs {A : Type} (ts : Forest' A) : Forest A :=
match ts with
    | InF NilR  => Nil
    | InF (ConsR t ts') => Cons (g t) (gs ts')
end.

Lemma fg :
  forall {A : Type} (t : Tree A),
    g (f t) = t

with fsgs :
  forall {A : Type} (ts : Forest A),
    gs (fs ts) = ts.
Proof.
  destruct t as [| x ts]; cbn.
    reflexivity.
    rewrite fsgs. reflexivity.

  destruct ts as [| t ts']; cbn.
    reflexivity.
    rewrite fg, fsgs. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : Tree' A),
    f (g t) = t

with gsfs :
  forall {A : Type} (ts : Forest' A),
    fs (gs ts) = ts.
Proof.
  destruct t as [[| x ts]]; cbn.
    reflexivity.
    rewrite gsfs. reflexivity.

  destruct ts as [[| t ts']]; cbn.
    reflexivity.
    rewrite gf, gsfs. reflexivity.
Qed.

End TreeR.

Module TreeF.

Inductive TreeF (F : Type -> Type) (A : Type) : Type :=
    | EmptyF : TreeF F A
    | NodeF  : A -> F A -> TreeF F A.

Inductive ForestF (T F : Type -> Type) (A : Type) : Type :=
    | NilF  : ForestF T F A
    | ConsF : T A -> F A -> ForestF T F A.

Arguments EmptyF {F A}.
Arguments NodeF  {F A} _ _.

Arguments NilF   {T F A}.
Arguments ConsF  {T F A} _ _.

Inductive Tree' (A : Type) : Type :=
    | InT : TreeF Forest' A -> Tree' A

with Forest' (A : Type) : Type :=
    | InF : ForestF Tree' Forest' A -> Forest' A.

Arguments InT {A} _.

Arguments InF {A} _.

Fixpoint f {A : Type} (t : Tree A) : Tree' A :=
match t with
    | Empty     => InT EmptyF
    | Node x ts => InT (NodeF x (fs ts))
end

with fs {A : Type} (ts : Forest A) : Forest' A :=
match ts with
    | Nil        => InF NilF
    | Cons t ts' => InF (ConsF (f t) (fs ts'))
end.

Fixpoint g {A : Type} (t : Tree' A) : Tree A :=
match t with
    | InT EmptyF       => Empty
    | InT (NodeF x ts) => Node x (gs ts)
end

with gs {A : Type} (ts : Forest' A) : Forest A :=
match ts with
    | InF NilF  => Nil 
    | InF (ConsF t ts') => Cons (g t) (gs ts')
end.

Lemma fg :
  forall {A : Type} (t : Tree A),
    g (f t) = t

with fsgs :
  forall {A : Type} (ts : Forest A),
    gs (fs ts) = ts.
Proof.
  destruct t as [| x ts]; cbn.
    reflexivity.
    rewrite fsgs. reflexivity.

  destruct ts as [| t ts']; cbn.
    reflexivity.
    rewrite fg, fsgs. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : Tree' A),
    f (g t) = t

with gsfs :
  forall {A : Type} (ts : Forest' A),
    fs (gs ts) = ts.
Proof.
  destruct t as [[| x ts]]; cbn.
    reflexivity.
    rewrite gsfs. reflexivity.

  destruct ts as [[| t ts']]; cbn.
    reflexivity.
    rewrite gf, gsfs. reflexivity.
Qed.

End TreeF.

End FinitaryTreeF.

(** * Indexed families *)

Require Import List.
Import ListNotations.

Require Import F3 F4.

Module ListCoList.

Module CoList.

Import F4.

Module CoList_ForallF.

Inductive ForallF
  {A : Type} (R : A -> A -> Prop)
  (F : (A -> A -> Prop) -> CoList A -> CoList A -> Prop)
  : CoList A -> CoList A -> Prop :=
    | Nils  :
        forall l1 l2 : CoList A,
          uncons l1 = NilF -> uncons l2 = NilF -> ForallF R F l1 l2
    | Conss :
        forall (l1 l2 : CoList A) (h1 h2 : A) (t1 t2 : CoList A),
          uncons l1 = ConsF h1 t1 -> uncons l2 = ConsF h2 t2 ->
            R h1 h2 -> F R t1 t2 -> ForallF R F l1 l2.

CoInductive CoForall {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
{
    uncons' : ForallF R CoForall l1 l2
}.

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
    uncons : ListR A (CoList A);
}.

Arguments uncons {A} _.

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

Definition uncons' {A : Type} (l : List A) : ListR A (List A) :=
match l with
    | In x => x
end.

Inductive Forall {A : Type} (R : A -> A -> Prop) (l1 l2 : List A) : Prop :=
    | InForall : ForallR uncons' R (Forall R) l1 l2 -> Forall R l1 l2.

CoInductive CoForall {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
{
    uncons'' : ForallR uncons R (CoForall R) l1 l2
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
    | InExists : ExistsR uncons' R (Exists R) l1 l2 -> Exists R l1 l2.

Inductive CoExists {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
    | InCoExists : ExistsR uncons R (CoExists R) l1 l2 -> CoExists R l1 l2.

(** Maybe we can define generic functions? *)

Fixpoint cata {A R : Type} (f : ListR A R -> R) (l : List A) : R :=
match l with
    | In NilR        => f NilR
    | In (ConsR h t) => f (ConsR h (cata f t))
end.

CoFixpoint ana {A R : Type} (f : R -> ListR A R) (r : R) : CoList A :=
{|
    uncons :=
      match f r with
          | NilR      => NilR
          | ConsR h t => ConsR h (ana f t)
      end
|}.

End ListCoList2.

(** * Codes for inductive-recursive types *)

Inductive IR (D : Type) : Type :=
    | iota  : D -> IR D
    | sigma : forall A : Type, (A -> IR D) -> IR D
    | delta : forall A : Type, ((A -> D) -> IR D) -> IR D.