(** Inspired by:
    - Cyclic Lists, Purely: https://gallais.github.io/blog/cyclic-list-purely.html
    - Representing Cyclic Structures as Nested Data Types:
      https://www.cs.gunma-u.ac.jp/~hamana/Papers/tfp06.pdf *)

Require Import Recdef.
Require Import List.
Import ListNotations.

(** * CoLists *)

(** We need CoLists (Coinductive Lists) to express some things for which the
    original blogpost uses ordinary Haskell lists. *)

Inductive CoListF (A R : Type) : Type :=
    | CoNilF
    | CoConsF (h : A) (t : R).

Arguments CoNilF  {A R}.
Arguments CoConsF {A R} _ _.

CoInductive CoList (A : Type) : Type :=
{
    uncons : CoListF A (CoList A);
}.

Arguments uncons {A} _.

Definition CoNil {A : Type} : CoList A :=
{|
    uncons := CoNilF;
|}.

Definition CoCons {A : Type} (h : A) (t : CoList A) : CoList A :=
{|
    uncons := CoConsF h t;
|}.

Inductive FiniteCoList {A : Type} (l : CoList A) : Type :=
    | FiniteCoNil :
        uncons l = CoNilF -> FiniteCoList l
    | FiniteCoCons :
        forall (h : A) (t: CoList A),
          uncons l = CoConsF h t ->
            FiniteCoList t -> FiniteCoList l.

Inductive simF {A : Type} (l1 l2 : CoList A) (R : CoList A -> CoList A -> Type) : Type :=
    | CoNilsF (H1 : uncons l1 = CoNilF) (H2 : uncons l2 = CoNilF)
    | CoConssF :
        forall (h1 h2 : A) (t1 t2 : CoList A),
          uncons l1 = CoConsF h1 t1 -> uncons l2 = CoConsF h2 t2 ->
            h1 = h2 -> R t1 t2 -> simF l1 l2 R.

CoInductive sim {A : Type} (l1 l2 : CoList A) : Type :=
{
    sim' : simF l1 l2 sim;
}.

Lemma sim_refl :
  forall {A : Type} (l : CoList A),
    sim l l.
Proof.
  cofix CH.
  destruct l as [[| h t]].
    do 2 constructor; cbn; reflexivity.
    constructor. econstructor 2; try reflexivity. apply CH.
Qed.

(** The first part is inspired by "Cyclic Lists, Purely"
    (https://gallais.github.io/blog/cyclic-list-purely.html) *)

(** * Fegaras and Sheard's solution *)

Module HOAS_Like.

Unset Positivity Checking.
Inductive CList (A : Type) : Type :=
    | Nil
    | Cons (h : A) (t : CList A)
    | Rec  (h : A) (r : CList A -> CList A).
Set Positivity Checking.

Arguments Nil  {A}.
Arguments Cons {A} _ _.
Arguments Rec  {A} _.

Function unwind {A : Type} (l : CList A) : CoList A :=
match l with
    | Nil => CoNil
    | Cons h t => CoCons h (unwind t)
    | Rec h r => CoCons h (unwind (r l))
end.

Inductive FiniteCList {A : Type} : CList A -> Type :=
    | FNil  : FiniteCList Nil
    | FCons :
        forall (h : A) (t : CList A),
          FiniteCList t -> FiniteCList (Cons h t).

Lemma Finite_check :
  forall {A : Type} (l : CList A),
    FiniteCList l -> FiniteCoList (unwind l).
Proof.
  induction 1; cbn.
    constructor. cbn. reflexivity.
    econstructor 2.
      reflexivity.
      assumption.
Qed.

(** ** The limitations of this representation *)

(** *** There is no guarantee on the way pointers are used (if at all). *)

(** Explanation: [FiniteCList] is a syntactic definition of finiteness.
    [FiniteCoList] is, on the other hand, a semantic definition of
    finiteness.

    It turns out that there are some semantically finite CLists which
    are not finite according to the syntactic definition. This is caused
    by the misuse of the [Rec] constructor to construct phony cycles. *)

Definition finite : CList nat :=
  Cons 1 (Rec 2 (fun _ => Nil)).

Lemma finite_not_FiniteCList :
  FiniteCList finite -> False.
Proof.
  inversion 1. subst.
  inversion H1.
Qed.

Lemma FiniteCoList_unwind_finite :
  FiniteCoList (unwind finite).
Proof.
  cbn.
  econstructor 2; try reflexivity.
  econstructor 2; try reflexivity.
  constructor; reflexivity.
Defined.

(** Nice observation: problems are caused by not using the name bound
    by [Rec] (or possibly also by using it more that once). So maybe
    this could be fixed by a type of linear functions? *)

(** *** Normal forms are not guaranteed *)

Definition ex1 : CList nat :=
  Cons 4 (Rec 2 (fun l => l)).

Definition ex2 : CList nat :=
  Rec 4 (fun _ => Rec 2 (fun l => l)).

(** Here we have two syntactically distinct [CList]s whose normal forms are the
    same. *)

Lemma syntactically_different :
  ex1 <> ex2.
Proof.
  inversion 1.
Qed.

Lemma semantically_equal :
  sim (unwind ex1) (unwind ex2).
Proof.
  cofix CH.
  constructor. econstructor 2.
    unfold ex1. rewrite unwind_equation. reflexivity.
    unfold ex2. rewrite unwind_equation. reflexivity.
    reflexivity.
    apply sim_refl.
Qed.

Fixpoint take (n : nat) {A : Type} (l : CList A) : list A :=
match n with
    | 0    => []
    | S n' =>
        match l with
            | Nil => []
            | Cons h t => h :: take n' t
            | Rec h r => h :: take n' (r l)
        end
end.

Fixpoint app {A : Type} (l1 l2 : CList A) : CList A :=
match l1 with
    | Nil => l2
    | Cons h t => Cons h (app t l2)
    | Rec h r => Rec h (fun l => (app (r l) l2))
end.

(** *** Useful functions cannot be written without unfolding the cycle *)

(** It's probably impossible to define [map]. *)
Unset Guard Checking.
Fixpoint mapS (l : CList nat) : CList nat :=
match l with
    | Nil      => Nil
    | Cons h t => Cons (S h) (mapS t)
    | Rec  h r => Rec (S h) (fun l => r (mapS l))
(*  | Rec  h r => Cons (S h) (mapS (r l)) *) (* Does not terminate *)
end.
Set Guard Checking.

(** If we try, mapping successor over a recursive list results in computing
    powers of two... *)
Compute take 10 (mapS ex1).
(* ===> [6; 4; 6; 10; 18; 34; 66; 130; 258; 514] : list nat *)

End HOAS_Like.

(** * Calling the type system to the rescue *)

Module Phantom.

Inductive Closed : SProp := closed.

Unset Positivity Checking.
Inductive CList' (A : Type) : SProp -> Type :=
    | Nil  : CList' A Closed
    | Cons : forall {B : SProp} (h : A) (t : CList' A B), CList' A B
    | Rec  : forall (h : A) (r : forall {B : SProp}, CList' A B -> CList' A B),
               CList' A Closed.
Set Positivity Checking.

Arguments Nil  {A}.
Arguments Cons {A B} _ _.
Arguments Rec  {A} _ _.

Definition CList (A : Type) : Type := CList' A Closed.

(** Our previous problems with illegal uses of the pointer are gone. *)

Fail Definition finite : CList nat :=
  Cons 1 (Rec 2 (fun _ _ => Nil)).
(* The command has indeed failed with message:
   In environment [P : SProp], [c : CList' nat P]
   The term [Nil] has type
   [CList' nat Closed]
   while it is expected to have type
   [CList' nat P]
   (cannot unify [Closed] and [P]).
*)

(** As we see, we can't use [Nil] while omitting the argument, as this results
    in a type error. *)

Definition ex1 : CList nat :=
  Cons 4 (Rec 2 (fun _ l => l)).

(** The correct definition is still correct. *)

Fail Definition ex2 : CList nat :=
  Rec 4 (fun _ _ => Rec 2 (fun _ l => l)).
(* In environment
   [P : SProp], [c : CList' nat P]
   The term
   [Rec 2 (fun (B : SProp) (l : CList' nat B) => l)]
   has type
   [CList' nat Closed]
   while it is expected to have type
   [CList' nat P]
*)

(** We also can't use one pointer while ignoring another one. Thus, we see that
    using a phantom type argument has effects similar to using a type of linear
    functions. *)

Require Import Coq.Program.Equality.

Unset Guard Checking.
Fixpoint stopRec
  {A : Type} {R : SProp -> Type}
  (nil  : R Closed)
  (cons : forall (B : SProp), A -> R B -> R B)
  (rec  : A -> (forall B : SProp, R B -> R B) -> R Closed)
  (l    : CList' A Closed)
  {B : SProp}
  (ih : R B) {struct l} : R B.
Proof.
  destruct l as [| B' h t | h r].
    exact ih.
    exact (cons _ h (stopRec A R nil cons rec t B ih)).
    exact ih. Show Proof.
Defined.
Set Guard Checking.

Unset Guard Checking.
Fixpoint cfold
  {A : Type} {R : SProp -> Type}
  (nil  : R Closed)
  (cons : forall (B : SProp), A -> R B -> R B)
  (rec  : A -> (forall B : SProp, R B -> R B) -> R Closed)
  (l    : CList' A Closed) {struct l}
        : R Closed.
Proof.
  destruct l as [| B h t | h r].
    exact nil.
    exact (cons _ h (cfold A R nil cons rec t)).
    exact (rec h (@stopRec A R nil cons rec (r _ (Rec h r)))). Show Proof.
Defined.
Set Guard Checking.

Definition cmap {A B : Type} (f : A -> B) (l : CList A) : CList B.
Proof.
  eapply cfold.
    exact Nil.
    intros B' h t. exact (Cons (f h) t).
    intros h r. exact (Rec (f h) r).
    exact l.
Defined.

Compute cmap S ex1.

(** We can define a non-dependent eliminator (i.e. the recursion principle). *)

Definition cfoldRec
  {A R : Type} (nil : R) (cons : A -> R -> R) (rec : A -> (R -> R) -> R)
  (l : CList A) : R :=
    @cfold A (fun _ => R) nil (fun _ => cons) (fun a r => rec a (r Closed)) l.

Require Import String.

(** We can define a [show] function which displays a (representation of a)
    cycli list as a finite string. *)
Definition show {A : Type} (sh : A -> string) (l : CList A) : string :=
  cfoldRec
    "[]"%string
    (fun h t => append (sh h) (append " :: " t))
    (fun h r => append "rec X. " (append (sh h) (append " :: " (r "X"))))%string
    l.

Definition wut : CList string :=
  (Cons "a" (Cons "b" (Rec "c" (fun _ l => Cons "d" l))))%string.

Compute show (fun x => x) wut.

(** Contrary to what's possible in Haskell (as described in the original
    blogpost), in Coq we can't recover a fold-like function for [CList], as
    that would basically require unwinding the [CList] into a [CoList] and then
    folding the CoList, but that's impossible because [CoList]s are coinductive.

    But a mere conversion to a CoList is of course still possible. *)

CoFixpoint unwind {A : Type} {B : SProp} (l : CList' A B) : CoList A :=
{|
    uncons :=
      match l with
          | Nil      => CoNilF
          | Cons h t => CoConsF h (unwind t)
          | Rec h r  => CoConsF h (unwind (r _ l))
      end;
|}.

Fixpoint cotake {A : Type} (n : nat) (l : CoList A) : list A :=
match n with
    | 0    => []
    | S n' =>
        match uncons l with
            | CoNilF => []
            | CoConsF h t => h :: cotake n' t
        end
end.

Compute cotake 10 (unwind wut).

End Phantom.

(** The second part is inspired by "Representing Cyclic Structures as Nested Data Types"
    (https://www.cs.gunma-u.ac.jp/~hamana/Papers/tfp06.pdf) *)

Module HOAS_Unique.

(** The HOAS-like representation wasn't unique and that was bad. We can make a
    better representation with unique normal forms by getting rid of [Cons] and
    leaving just [Rec]. *)

Unset Positivity Checking.
Inductive CList (A : Type) : Type :=
    | Nil
    | RCons (h : A) (r : CList A -> CList A).
Set Positivity Checking.

Arguments Nil   {A}.
Arguments RCons {A} _ _.

Function unwind {A : Type} (l : CList A) : CoList A :=
match l with
    | Nil       => CoNil
    | RCons h r => CoCons h (unwind (r l))
end.

(** But it's hard to prove that normal forms are unique in this representation. *)

Lemma unique :
  forall {A : Type} (l1 l2 : CList A),
    sim (unwind l1) (unwind l2) -> l1 = l2.
Proof.
  intros A l1.
  functional induction unwind l1.
    destruct l2.
      reflexivity.
      inversion 1. inversion sim'0.
        inversion H2.
        inversion H.
    intro l2. functional induction unwind l2.
      inversion 1. inversion sim'0.
        inversion H1.
        inversion H0.
      inversion 1. inversion sim'0.
        inversion H1.
        cbn in *. inversion H; inversion H0; subst. f_equal.
Abort.

End HOAS_Unique.

(** We can do better: we can defunctionalize the higher-order repsentation to
    arrive at a first-order representation that is basically just de Bruijn
    levels. *)

Module Nested.

Inductive CList (A V : Type) : Type :=
    | Var : V -> CList A V
    | Nil : CList A V
    | RCons : A -> CList A (option V) -> CList A V.

Arguments Var   {A V} _.
Arguments Nil   {A V}.
Arguments RCons {A V} _ _.

(** Technically, this is realized using a nested inductive type. The type
    family [CList] has two type parameters, [A] and [V]. [A] is the type of
    elements held in the list, while [V] represents pointers that can be used
    to close a cycle. Our intention is that when [V] is nonempty, [CList A V]
    represents cyclic lists "with free variables", whereas for empty [V],
    [CList A V] represents "closed" cyclic lists. *)

Fixpoint map {A B V : Type} (f : A -> B) (l : CList A V) : CList B V :=
match l with
    | Var v     => Var v
    | Nil       => Nil
    | RCons h t => RCons (f h) (map f t)
end.

(** [map] is easy. *)

Fixpoint shift {A V : Type} (l : CList A V) : CList A (option V) :=
match l with
    | Var v     => Var (Some v)
    | Nil       => Nil
    | RCons h t => RCons h (shift t)
end.

(** [shift] is a very important auxiliary function which shifts all pointers
    one place to the right, i.e. a pointer that referred to the list's zeroth
    element now refers to the first one and so on. *)

Lemma map_shift :
  forall {A B V : Type} (f : A -> B) (l : CList A V),
    map f (shift l) = shift (map f l).
Proof.
  induction l as [| | h t]; cbn.
    1-2: reflexivity.
    f_equal. exact IHl.
Qed.

Lemma map_map :
  forall {A B C V : Type} (f : A -> B) (g : B -> C) (l : CList A V),
    map g (map f l) = map (fun x => g (f x)) l.
Proof.
  induction l as [| | h t]; cbn; intros.
    1-2: reflexivity.
    rewrite IHl. reflexivity.
Qed.

Lemma map_id :
  forall {A V : Type} (l : CList A V),
    map (fun x => x) l = l.
Proof.
  induction l as [| | h t]; cbn; intros.
    1-2: reflexivity.
    rewrite IHl. reflexivity.
Qed.

Fixpoint app {A V : Type} (l1 l2 : CList A V) : CList A V :=
match l1 with
    | Var v     => Var v
    | Nil       => l2
    | RCons h t => RCons h (app t (shift l2))
end.

(** [app] is also easy, but we need to [shift] the pointers when appending [l2]
    to the tail of [l1]. When we hit a variable we drop [l2], because it means
    that we have arrived in a location where a pointer to an earlier location
    in the list is used, i.e. the first list is cyclic and thus "infinite". *)

Lemma map_app :
  forall {A B V : Type} (f : A -> B) (l1 l2 : CList A V),
    map f (app l1 l2) = app (map f l1) (map f l2).
Proof.
  induction l1 as [| | h t]; cbn; intros.
    1-2: reflexivity.
    rewrite IHl1, map_shift. reflexivity.
Qed.

Lemma app_shift :
  forall {A V : Type} (l1 l2 : CList A V),
    app (shift l1) (shift l2) = shift (app l1 l2).
Proof.
  induction l1 as [| | h t]; cbn; intros.
    1-2: reflexivity.
    rewrite IHl1. reflexivity.
Qed.

Lemma app_assoc :
  forall {A V : Type} (l1 l2 l3 : CList A V),
    app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  induction l1 as [| | h t]; cbn; intros.
    1-2: reflexivity.
    rewrite IHl1, app_shift. reflexivity.
Qed.

Fixpoint snoc {A V : Type} (x : A) (l : CList A V) : CList A V :=
match l with
    | Var v     => Var v
    | Nil       => RCons x Nil
    | RCons h t => RCons h (snoc x t)
end.

Lemma snoc_shift :
  forall {A V : Type} (x : A) (l : CList A V),
    snoc x (shift l) = shift (snoc x l).
Proof.
  induction l as [| | h t]; cbn.
    1-2: reflexivity.
    rewrite IHl. reflexivity.
Qed.

Lemma snoc_app :
  forall {A V : Type} (x : A) (l1 l2 : CList A V),
    snoc x (app l1 l2) = app l1 (snoc x l2).
Proof.
  induction l1 as [| | h t]; cbn; intros.
    1-2: reflexivity.
    rewrite IHl1, snoc_shift. reflexivity.
Qed.

Fixpoint replicate {A V : Type} (n : nat) (x : A) : CList A V :=
match n with
    | 0    => Nil
    | S n' => RCons x (replicate n' x)
end.

Definition repeat {A V : Type} (x : A) : CList A V :=
  RCons x (Var None).

Inductive Finite {A V : Type} : CList A V -> Type :=
    | FNil   : Finite Nil
    | FRCons : forall (h : A) (t : CList A (option V)),
                 Finite t -> Finite (RCons h t).

Lemma shift_replicate :
  forall (n : nat) {A V : Type} (x : A),
    @shift A V (replicate n x) = replicate n x.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

Lemma Finite_replicate :
  forall (n : nat) {A V : Type} (x : A),
    @Finite A V (@replicate A V n x).
Proof.
  induction n as [| n']; cbn; intros.
    constructor.
    constructor. apply IHn'.
Qed.

Lemma not_Finite_repeat :
  forall {A V : Type} (x : A),
    @Finite A V (repeat x) -> False.
Proof.
  inversion 1. subst. inversion X0.
Qed.

Definition CList' (A : Type) : Type := CList A False.

Definition cons {A V : Type} (h : A) (t : CList' A) : CList' A :=
  RCons h (shift t).

Fixpoint recycle {A V : Type} (x : A) (l : CList A (option V)) : CList A V :=
match l with
    | Var None     => RCons x (Var None)
    | Var (Some v) => Var v
    | Nil          => Nil
    | RCons h t    => RCons h (recycle x t)
end.

Definition cuncons {A : Type} (l : CList' A) : option (A * CList' A) :=
match l with
    | Var v     => match v with end
    | Nil       => None
    | RCons h t => Some (h, recycle h t)
end.

CoFixpoint unwind {A : Type} (l : CList' A) : CoList A :=
{|
    uncons :=
      match cuncons l with
          | None => CoNilF
          | Some (h, t) => CoConsF h (unwind t)
      end
|}.

Fixpoint ctake (n : nat) {A : Type} (l : CoList A) : list A :=
match n with
    | 0    => []
    | S n' =>
        match uncons l with
            | CoNilF      => []
            | CoConsF h t => h :: ctake n' t
        end
end.

Definition example : CList' nat :=
  RCons 1 (RCons 2 (Var None)).

Definition take (n : nat) {A : Type} (l : CList' A) : list A :=
  ctake n (unwind l).

Compute take 10 example.

Fixpoint drop (n : nat) {A : Type} (l : CList' A) : CList' A :=
match n with
    | 0    => l
    | S n' =>
        match cuncons l with
            | None => Nil
            | Some (_, t) => drop n' t
        end
end.

Compute drop 11 example.

Fixpoint take' (n : nat) {A : Type} (l : CList' A) : list A :=
match n with
    | 0    => []
    | S n' =>
        match cuncons l with
            | None => []
            | Some (h, t) => h :: take' n' t
        end
end.

Compute take' 10 example.

Fail Fixpoint bind {A B V : Type} (l : CList A V) (f : A -> CList B V) : CList B V :=
match l with
    | Var v     => Var v
    | Nil       => Nil
    | RCons h t => app (f h) (bind t (fun l => shift (f l)))
end.

Fixpoint rev {A V : Type} (l : CList A V) : CList A V :=
match l with
    | Var v     => Var v
    | Nil       => Nil
    | RCons h t => recycle h (rev t)
end.

Definition from1to5 : CList' nat :=
  RCons 1 (RCons 2 (RCons 3 (RCons 4 (RCons 5 (Var None))))).

Compute rev from1to5.

Fixpoint nth (n : nat) {A : Type} (l : CList' A) : option A :=
match n, cuncons l with
    | _   , None        => None
    | 0   , Some (h, t) => Some h
    | S n', Some (h, t) => nth n' t
end.

Compute List.map (fun n => nth n from1to5) [0; 1; 2; 3; 4; 5; 6; 7].

Fixpoint cycle (n : nat) {A : Type} (l : CList' A) : CList' A :=
match n, cuncons l with
    | 0   , _           => l
    | _   , None        => l
    | S n', Some (h, t) => cycle n' t
end.

Compute List.map (fun n => cycle n from1to5) [0; 1; 2; 3; 4; 5; 6; 7].

Fixpoint any {A V : Type} (p : A -> bool) (l : CList A V) : bool :=
match l with
    | Var v     => false
    | Nil       => false
    | RCons h t => p h || any p t
end.

Fixpoint wut {A V : Type} (l : CList A (option V)) : CList A V :=
match l with
    | Var None     => Nil
    | Var (Some v) => Var v
    | Nil          => Nil
    | RCons h t    => RCons h (wut t)
end.

Fixpoint filter {A V : Type} (p : A -> bool) (l : CList A V) : CList A V :=
match l with
    | Var v     => Var v
    | Nil       => Nil
    | RCons h t => if p h then RCons h (filter p t) else wut (filter p t)
end.

Compute from1to5.
Compute filter Nat.even from1to5.
Compute filter Nat.even (RCons 1 (RCons 2 (Var None))).

Fixpoint shift' {A V : Type} (l : CList A V) : CList A (option (option V)) :=
match l with
    | Var v     => Var (Some (Some v))
    | Nil          => Nil
    | RCons h t    => RCons h (shift' t)
end.

Fail Fixpoint intersperse {A V : Type} (x : A) (l : CList A V) : CList A V :=
match l with
    | Var v       => Var v
    | Nil         => Nil
    | RCons h t   => RCons h (shift' (RCons x (intersperse x t)))
end.

Fail Compute take 20 (intersperse 0 from1to5).

(** * Relations *)

Inductive Elem {A V : Type} (x : A) : CList A V -> Type :=
    | Zero :
        forall l : CList A (option V), Elem x (RCons x l)
    | Succ :
        forall (h : A) (t : CList A (option V)),
          Elem x t -> Elem x (RCons h t).

Inductive Dup {A V : Type} : CList A V -> Type :=
    | DupVar :
        forall v : V, Dup (Var v)
    | DupHere :
        forall (h : A) (t : CList A (option V)),
          Elem h t -> Dup (RCons h t)
    | DupThere :
        forall (h : A) (t : CList A (option V)),
          Dup t -> Dup (RCons h t).

Lemma NoDup_Finite :
  forall {A V : Type} (l : CList A V),
    (Dup l -> False) -> Finite l.
Proof.
  induction l as [| | h t]; cbn; intros.
    contradiction H. constructor.
    constructor.
    constructor. apply IHl. intro. apply H. constructor 3. assumption.
Qed.

Lemma NoFinite_Dup :
  forall {A V : Type} (l : CList A V),
    (Finite l -> False) -> Dup l.
Proof.
  induction l as [| | h t]; intros.
    constructor.
    contradict H. constructor.
    constructor 3. apply IHl. intro. apply H. constructor. assumption.
Qed.

Inductive Ex {A V : Type} (P : A -> Type) : CList A V -> Type :=
    | ExHere :
        forall (x : A) (l : CList A (option V)),
          P x -> Ex P (RCons x l)
    | ExThere :
        forall (h : A) (t : CList A (option V)),
          Ex P t -> Ex P (RCons h t).

Fixpoint takeWhile {A V : Type} (p : A -> bool) (l : CList A V) : CList A V :=
match l with
    | Var v     => Var v
    | Nil       => Nil
    | RCons h t => if p h then RCons h (takeWhile p t) else Nil
end.

Require Import Nat.

Compute takeWhile (fun n => n <? 6) from1to5.

Fail Fixpoint dropWhile {A V : Type} (p : A -> bool) (l : CList A V) : CList A V :=
match l with
    | Var v     => Var v
    | Nil       => Nil
    | RCons h t => if p h then dropWhile p t else Nil
end.

End Nested.

Module CyclicBinaryTree.

Inductive CBin (A V : Type) : Type :=
    | Var : V -> CBin A V
    | E   : CBin A V
    | N   : A -> CBin A (option V) -> CBin A (option V) -> CBin A V.

Arguments Var {A V} _.
Arguments E   {A V}.
Arguments N   {A V} _ _ _.

Definition CBin' (A : Type) : Type :=
  CBin A False.

Definition example : CBin' nat :=
  N 1
    (N 2
      (N 3 (Var None) E)
      E)
    (N 4
      (N 5 E E)
      (N 6 E E)).

Fixpoint recycle {A V : Type} (x : A) (t : CBin A (option V)) : CBin A V :=
match t with
    | Var None     => N x (Var None) (Var None)
    | Var (Some v) => Var v
    | E            => E
    | N y l r      => N y (recycle x l) (recycle x r)
end.

Definition unN {A : Type} (t : CBin' A) : option (A * CBin' A * CBin' A) :=
match t with
    | Var v   => match v with end
    | E       => None
    | N x l r => Some (x, recycle x l, recycle x r)
end.

Fixpoint map {A B V : Type} (f : A -> B) (t : CBin A V) : CBin B V :=
match t with
    | Var v   => Var v
    | E       => E
    | N x l r => N (f x) (map f l) (map f r)
end.

Fixpoint mirror {A V : Type} (t : CBin A V) : CBin A V :=
match t with
    | Var v   => Var v
    | E       => E
    | N x l r => N x (mirror r) (mirror l)
end.

Definition complete {A : Type} (x : A) : CBin' A :=
  N x (Var None) (Var None).

Fixpoint index {A : Type} (l : list bool) (t : CBin' A) : option A :=
match l, unN t with
    | _, None     => None
    | []         , Some (x, _ , _ ) => Some x
    | false :: l', Some (_, t', _ ) => index l' t'
    | true  :: l', Some (_, _ , t') => index l' t'
end.

Compute example.
Compute index [false; false; false; false] example.

(* Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> BTree A. *)

Fixpoint shift {A V : Type} (t : CBin A V) : CBin A (option V) :=
match t with
    | Var v   => Var (Some v)
    | E       => E
    | N x l r => N x (shift l) (shift r)
end.

Fixpoint take (n : nat) {A : Type} (t : CBin' A) : CBin' A :=
match n, unN t with
    | _   , None           => E
    | 0   , _              => E
    | S n', Some (x, l, r) => N x (shift (take n' l)) (shift (take n' r))
end.

Compute take 5 example.

Fixpoint any {A V : Type} (p : A -> bool) (t : CBin A V) : bool :=
match t with
    | Var v   => false
    | E       => false
    | N x l r => p x || any p l || any p r
end.

Fixpoint all {A V : Type} (p : A -> bool) (t : CBin A V) : bool :=
match t with
    | Var v   => false
    | E       => false
    | N x l r => p x && all p l && all p r
end.

(* Parameter count : forall A : Type, (A -> bool) -> BTree A -> nat. *)

Fixpoint takeWhile {A V : Type} (p : A -> bool) (t : CBin A V) : CBin A V :=
match t with
    | Var v   => Var v
    | E       => E
    | N x l r => if p x then N x (takeWhile p l) (takeWhile p r) else E
end.

Require Import Nat.

Compute takeWhile (fun x => x <? 3) example.

(* Need to compute lcm somewhere.
Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (ta : CBin A V) (tb : CBin B V) : CBin C V :=
match ta, tb with
    | Var va, Var vn => V
 *)

End CyclicBinaryTree.

Module GeneralCyclicStructures.

Require Import MuNu.

(** The above approach can be generalized even more, to a Fixpoint-with-Cycles
    inductive type like. But for this to work in Coq, we need to turn off the
    positivity checker and then the termination checker each time we want to
    implement a recursive function, so we're not going to pursue the generalized
    approach here.

    Anyway, see https://www.cs.gunma-u.ac.jp/~hamana/Papers/tfp06.pdf section 4
    for more details. *)

End GeneralCyclicStructures.