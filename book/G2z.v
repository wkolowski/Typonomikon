(** * G2z: Struktury cykliczne [TODO] *)

Require Import List.
Import ListNotations.

From Typonomikon Require Import F4.

(** * Listy cykliczne (TODO) *)

Module CyclicList.

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
    | None => NilF
    | Some (h, t) => ConsF h (unwind t)
    end
|}.

Fixpoint ctake (n : nat) {A : Type} (l : CoList A) : list A :=
match n with
| 0    => []
| S n' =>
  match uncons l with
  | NilF      => []
  | ConsF h t => h :: ctake n' t
  end
end.

Definition example : CList' nat :=
  RCons 1 (RCons 2 (Var None)).

Definition take (n : nat) {A : Type} (l : CList' A) : list A :=
  ctake n (unwind l).

Definition example' : CList' nat :=
  RCons 1 (RCons 2 Nil).

Compute take 10 example'.

Definition example'' : CList' nat :=
  RCons 1 (RCons 2 (RCons 3 (RCons 4 (Var (Some (Some None)))))).

Compute take 10 example''.

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

Compute takeWhile (fun n => Nat.leb n 6) from1to5.

Fail Fixpoint dropWhile {A V : Type} (p : A -> bool) (l : CList A V) : CList A V :=
match l with
| Var v     => Var v
| Nil       => Nil
| RCons h t => if p h then dropWhile p t else Nil
end.

End CyclicList.

(** * Listy cykliczne bez udziwnień (TODO) *)

Module SimpleCyclicList.

From Typonomikon Require Import D5a D5b.

Inductive Cyclic (A : Type) : Type :=
| C : forall (start : list A) (cycle : list A), Cyclic A.

Arguments C {A} _ _.

Definition cmap {A B : Type} (f : A -> B) (l : Cyclic A) : Cyclic B :=
match l with
| C start cycle => C (map f start) (map f cycle)
end.

Lemma cmap_cmap :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (l : Cyclic A),
    cmap g (cmap f l) = cmap (fun x => g (f x)) l.
Proof.
  destruct l; cbn.
  f_equal; apply map_map.
Qed.

Lemma cmap_id :
  forall {A : Type} (l : Cyclic A), 
    cmap (fun x => x) l = l.
Proof.
  destruct l; cbn.
  f_equal; apply map_id.
Qed.

Definition capp {A : Type} (l1 l2 : Cyclic A) : Cyclic A :=
match l1, l2 with
| C s1 [], C s2 c2 => C (s1 ++ s2) c2
| C s1 c1, C s2 c2 => l1
end.

Lemma map_app :
  forall {A B : Type} (f : A -> B) (l1 l2 : Cyclic A),
    cmap f (capp l1 l2) = capp (cmap f l1) (cmap f l2).
Proof.
  destruct l1 as [s1 []], l2 as [s2 c2]; cbn.
    f_equal. apply map_app.
    reflexivity.
Qed.

Lemma capp_assoc :
  forall {A : Type} (l1 l2 l3 : Cyclic A),
    capp (capp l1 l2) l3 = capp l1 (capp l2 l3).
Proof.
  destruct l1 as [s1 []], l2 as [s2 []], l3 as [s3 c3]; cbn.
    2-4: reflexivity.
    f_equal. rewrite app_assoc. reflexivity.
Qed.

Definition csnoc {A : Type} (x : A) (l : Cyclic A) : Cyclic A :=
match l with
| C s [] => C (snoc x s) []
| C s c => C s c
end.

Lemma csnoc_capp :
  forall {A : Type} (x : A) (l1 l2 : Cyclic A),
    csnoc x (capp l1 l2) = capp l1 (csnoc x l2).
Proof.
  destruct l1 as [s1 []], l2 as [s2 []]; cbn.
    2-4: try reflexivity.
    f_equal. apply snoc_app.
Qed.

Definition creplicate {A : Type} (n : nat) (x : A) : Cyclic A :=
  C (replicate n x) [].

Definition crepeat {A : Type} (x : A) : Cyclic A :=
  C [] [x].

Inductive Finite {A : Type} : Cyclic A -> Type :=
| Finite' : forall l : list A, Finite (C l []).

Lemma Finite_creplicate :
  forall (n : nat) {A : Type} (x : A),
    Finite (creplicate n x).
Proof.
  constructor.
Qed.

Lemma not_Finite_crepeat :
  forall {A : Type} (x : A),
    Finite (crepeat x) -> False.
Proof.
  inversion 1.
Qed.

Definition ccons {A : Type} (h : A) (t : Cyclic A) : Cyclic A :=
match t with
| C s c => C (h :: s) c
end.

Definition cuncons {A : Type} (l : Cyclic A) : option (A * Cyclic A) :=
match l with
| C [] []       => None
| C [] (h :: t) => Some (h, C [] (snoc h t))
| C (h :: t) c  => Some (h, C t c)
end.

Definition example : Cyclic nat :=
  C [] [1; 2; 3; 4; 5].

Fixpoint ctake (n : nat) {A : Type} (l : Cyclic A) : list A :=
match n, l with
| 0   , _             => []
| S n', C [] []       => []
| S n', C (h :: t) c  => h :: ctake n' (C t c)
| S n', C [] (h :: t) => h :: ctake n' (C [] (snoc h t))
end.

Compute ctake 10 example.

Fixpoint cdrop (n : nat) {A : Type} (l : Cyclic A) : Cyclic A :=
match n, l with
| 0   , _             => l
| S n', C [] []       => C [] []
| S n', C (h :: t) c  => cdrop n' (C t c)
| S n', C [] (h :: t) => cdrop n' (C [] (snoc h t))
end.

Compute cdrop 23 example.

Fixpoint cbind_aux {A B : Type} (l : list A) (f : A -> Cyclic B) : Cyclic B :=
match l with
| []     => C [] []
| h :: t => capp (f h) (cbind_aux t f)
end.

Definition cbind {A B : Type} (l : Cyclic A) (f : A -> Cyclic B) : Cyclic B :=
match l with
| C s c => capp (cbind_aux s f) (cbind_aux c f)
end.

Definition crev {A : Type} (l : Cyclic A) : Cyclic A :=
match l with
| C s [] => C (rev s) []
| C _ c => C [] (rev c)
end.

Compute ctake 10 (crev (C [1; 2] [3; 4; 5])).
Compute crev example.

Fixpoint nth (n : nat) {A : Type} (l : Cyclic A) : option A :=
match n, l with
| _   , C [] []       => None
| 0   , C (h :: _) _  => Some h
| 0   , C [] (h :: _) => Some h
| S n', C (_ :: t) c  => nth n' (C t c)
| S n', C [] (h :: t) => nth n' (C [] (snoc h t))
end.

Compute map (fun n => nth n example) [0; 1; 2; 3; 4; 5; 6; 7].

Definition cany {A : Type} (p : A -> bool) (l : Cyclic A) : bool :=
match l with
| C s c => any p s || any p c
end.

Definition cfilter {A : Type} (p : A -> bool) (l : Cyclic A) : Cyclic A :=
match l with
| C s c => C (filter p s) (filter p c)
end.

Compute example.
Compute cfilter Nat.even example.
Compute ctake 10 (cfilter Nat.even example).

Definition cintersperse {A : Type} (x : A) (l : Cyclic A) : Cyclic A :=
match l with
| C s [] => C (intersperse x s) []
| C s c  => C (intersperse x s) (x :: intersperse x c)
end.

Compute example.
Compute cintersperse 0 example.
Compute ctake 20 (cintersperse 0 example).

Definition ctakeWhile {A : Type} (p : A -> bool) (l : Cyclic A) : Cyclic A :=
match l with
| C s c =>
  if length s =? length (takeWhile p s)
  then C (takeWhile p s) (takeWhile p c)
  else C (takeWhile p s) []
end.

Compute ctakeWhile (fun n => n <? 3) example.

Definition cdropWhile {A : Type} (p : A -> bool) (l : Cyclic A) : Cyclic A :=
match l with
| C s c =>
  match dropWhile p s with
  | [] => C [] (dropWhile p c)
  | s' => C s' c
  end
end.

Compute cdropWhile (fun n => n <? 3) example.

End SimpleCyclicList.

(** * Cykliczne drzewa binarne (TODO) *)

(** Sadly, this wonderful technique doesn't work with binary trees. This is
    because cyclic lists have only one cycle, which is easy to represent with
    a single ordinary [list], but trees can have as many cycles as they have
    leaves. *)

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

Compute takeWhile (fun x => Nat.leb x 3) example.

(* Need to compute lcm somewhere.
Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (ta : CBin A V) (tb : CBin B V) : CBin C V :=
match ta, tb with
| Var va, Var vn => V
 *)

End CyclicBinaryTree.

Module GeneralCyclicStructures.

(** The above approach can be generalized even more, to a Fixpoint-with-Cycles
    inductive type like. But for this to work in Coq, we need to turn off the
    positivity checker and then the termination checker each time we want to
    implement a recursive function, so we're not going to pursue the generalized
    approach here.

    Anyway, for more details see
    #<a class='link' href='https://www.cs.gunma-u.ac.jp/~hamana/Papers/tfp06.pdf'>
    Representing Cyclic Structures as Nested Data Types</a>#, section 4. *)

End GeneralCyclicStructures.