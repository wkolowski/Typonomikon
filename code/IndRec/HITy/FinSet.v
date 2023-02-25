(**
  Some tools from Homotopy Type Theory. They are already defined in the standard
  library under different names, but we use the HoTT names for simplicity.
*)

(** Transport is basically rewriting. *)
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) : P x -> P y :=
match p with
| eq_refl _ => fun u : P x => u
end.

(** Functions preserve equality. *)
Definition ap
  {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
match p with
| eq_refl => eq_refl
end.

(** Dependent functions preserve equality *)
Definition apd
  {A : Type} {P : A -> Type} (f : forall x : A, P x) {x y : A} (p : x = y)
  : transport P p (f x) = (f y) :=
match p with
| eq_refl => eq_refl
end.

(** We define finite sets as a Private Inductive Type hidden inside a module. *)
Module FinSet.

(** Finite sets are made using constructors which look like [nil] and [cons] for lists. *)
Private Inductive FinSet (A : Type) : Type :=
| empty : FinSet A
| scons : A -> FinSet A -> FinSet A.

Arguments empty {A}.
Arguments scons {A} _ _.

(**
  Now comes the hack: we assume that we can change the ordering of elements in
  the set with [swap] and remove duplicates using [idem].

  Note that this allows us to prove [False] inside the module, because constructors
  of inductive types are injective by default. But of course we won't do it.
*)
Axiom swap :
  forall {A : Type} (x y : A) (s : FinSet A),
    scons x (scons y s) = scons y (scons x s).

Axiom idem :
  forall {A : Type} (x : A) (s : FinSet A),
    scons x (scons x s) = scons x s.

(** Now we define the recursion principle. *)
Section rec.

(**
  Given a type [P] that has the structure of a finite set, i.e.:
  - there's an empty set
  - we can add an element to the set
  - we can swap elements in the set
  - we can remove duplicates
*)
Context
  (A : Type)
  (P : Type)
  (empty' : P)
  (scons' : A -> P -> P)
  (swap'  : forall (x y : A) (s : P), scons' x (scons' y s) = scons' y (scons' x s))
  (idem'  : forall (x : A) (s : P), scons' x (scons' x s) = scons' x s).

(**
  We can define an element of [P] from any finite set [s] by replacing the
  constructors of [s] with the provided operations. Note that the arguments
  [swap'] and [idem'] guarantee that the provided operations behave nicely.
*)
Fixpoint FinSet_rec
  (swap'  : forall (x y : A) (s : P), scons' x (scons' y s) = scons' y (scons' x s))
  (idem'  : forall (x : A) (s : P), scons' x (scons' x s) = scons' x s)
  (s : FinSet A) : P :=
match s with
| empty => empty'
| scons x s' => scons' x (FinSet_rec swap' idem' s')
end.

(**
  The path [swap] of [FinSet] gets mapped to the path [swap'] provided by [P]
  and analogously for [idem].
*)
Axiom FinSet_rec_swap :
  forall (x y : A) (s : FinSet A),
    ap (FinSet_rec swap' idem') (swap x y s) = swap' x y (FinSet_rec swap' idem' s).

Axiom FinSet_rec_idem :
  forall (x : A) (s : FinSet A),
    ap (FinSet_rec swap' idem') (idem x s) = idem' x (FinSet_rec swap' idem' s).

End rec.

(** Now we define the induction principle. *)
Section ind.

(**
  This time we are given a type [P] that supports making the empty set and adding
  elements to the set, but we don't need any guarantees that these operations
  behave nicely, because the induction principle will be only used to construct
  proofs - we kind of implicitly assume proof irrelevance here.
*)

Context
  (A : Type)
  (P : FinSet A -> Prop)
  (empty' : P empty)
  (scons' : forall (x : A) {s : FinSet A}, P s -> P (scons x s)).

(**
  If we can prove [P] for the empty case and for the "add element" case,
  we can prove it for all finite sets.
*)
Fixpoint FinSet_ind (s : FinSet A) : P s :=
match s with
| empty => empty'
| scons x s' => scons' x s' (FinSet_ind s')
end.

End ind.

(** Now we define the dependent recursor. This is a joint generalization of the
    recursor and the induction principle. *)
Section rect.

Context
  (A : Type)
  (P : FinSet A -> Type)
  (empty' : P empty)
  (scons' : forall (x : A) {s : FinSet A}, P s -> P (scons x s))
  (Swap'  :=
    forall (x y : A) (s : FinSet A) (s' : P s),
      transport _ (swap x y s) (scons' x (scons' y s')) = scons' y (scons' x s'))
  (swap'  : Swap')
  (Idem'  :=
    forall (x : A) (s : FinSet A) (s' : P s),
      transport _ (idem x s) (scons' x (scons' x s')) = scons' x s')
  (idem'  : Idem').

Fixpoint FinSet_rect
  (swap' : Swap') (idem' : Idem') (s : FinSet A) : P s :=
match s with
| empty => empty'
| scons x s' => scons' x s' (FinSet_rect swap' idem' s')
end.

Axiom FinSet_rect_swap :
  forall (x y : A) (s : FinSet A),
    apd (FinSet_rect swap' idem') (swap x y s) = swap' x y s (FinSet_rect swap' idem' s).

Axiom FinSet_rect_idem :
  forall (x : A) (s : FinSet A),
    apd (FinSet_rect swap' idem') (idem x s) = idem' x s (FinSet_rect swap' idem' s).

End rect.

End FinSet.

(**
  After closing the module, we can no longer define functions out of [FinSet]
  by pattern matching, because the type is private. Now the only way to define
  functions (and prove theorems) is to use the recursion/induction principles
  that we defined inside the module.

  Also note that even though we could have proved [False] inside the module,
  we didn't do it and now after closing the module we are back in a safe world
  with no contradictions.
*)
Import FinSet.

(**
  Now we define the union of two finite sets. This corresponds to [app] on
  lists. Note that because we can't use pattern matching, we must do this
  in proof mode using [refine].
*)
Definition union {A : Type} (s1 s2 : FinSet A) : FinSet A.
Proof.
  (*
    The first argument of [FinSet_rec] is [A], the type of elements of the set.
    The second argument of is the codomain, in this case [FinSet A].
    The third argument is the result for the [empty] case.
    The fourth argument is the result for the [scons] case. Note that the result
      of the recursive call is [rc].
    The fifth and sixth arguments are the proofs that the thrid and fourth
      arguments behave nicely. Note that we'll prove them with tactics.
    The last argument is the thing we're matching on.
  *)
  refine
  (
    @FinSet_rec A (FinSet A)   (* match s with                            *)
    s2                         (* | empty       => s2                     *)
    (fun x rc => scons x rc)   (* | scons x s1' => scons x (union s1' s2) *)
    _ _ s1                     (* end                                     *)
  ); clear s1 s2.
  (* Now we need to prove that we didn't do anything silly. *)
  - now apply swap.
  - now apply idem.
Defined.

(**
  One problem with our approach is that the proofs (the [swap]/[idem] cases)
  are part of function definitions, so when we try to [cbn] or [unfold], they
  get out and things get ugly. Therefore, we prove (by reflexivity) separate
  lemmas which we'll use for rewriting.
*)

Lemma union_empty_l :
  forall {A : Type} (s : FinSet A),
    union empty s = s.
Proof. easy. Defined.

Lemma union_scons_l :
  forall {A : Type} (x : A) (s1 s2 : FinSet A),
    union (scons x s1) s2 = scons x (union s1 s2).
Proof. easy. Defined.

(**
  Proofs in our approach are very pleasant - we only need to handle the cases
  which correspond to [empty] and [scons], so it's as simple as proving lemmas
  about lists.
*)

Lemma union_empty_r :
  forall {A : Type} (s : FinSet A),
    union s empty = s.
Proof.
  intros A.
  (*
    We can use the [induction] tactic, but we must give [@FinSet_ind A] in
    the [using] clause for it to get accepted by Coq.
  *)
  induction s as [| x s IH] using (@FinSet_ind A).
  - now rewrite union_empty_l.
  - now rewrite union_scons_l, IH.
Qed.

Lemma union_scons_r :
  forall {A : Type} (x : A) (s1 s2 : FinSet A),
    union s1 (scons x s2) = scons x (union s1 s2).
Proof.
  intros A; induction s1 as [| y s1' IH] using (@FinSet_ind A); intros.
  - now rewrite !union_empty_l.
  - now rewrite !union_scons_l, IH, swap.
Qed.

Lemma union_comm :
  forall {A : Type} (s1 s2 : FinSet A),
    union s1 s2 = union s2 s1.
Proof.
  intros A; induction s1 as [| x s1' IH] using (@FinSet_ind A); intros.
  - now rewrite union_empty_l, union_empty_r.
  - now rewrite union_scons_l, union_scons_r, IH.
Qed.

Lemma union_idem :
  forall {A : Type} (s : FinSet A),
    union s s = s.
Proof.
  intros A; induction s as [| x s' IH] using (@FinSet_ind A); intros.
  - now rewrite union_empty_l.
  - now rewrite union_scons_l, union_scons_r, IH, idem.
Qed.

Lemma union_assoc :
  forall {A : Type} (s1 s2 s3 : FinSet A),
    union (union s1 s2) s3 = union s1 (union s2 s3).
Proof.
  intros A; induction s1 as [| x s1' IH] using (@FinSet_ind A); intros.
  - now rewrite !union_empty_l.
  - now rewrite !union_scons_l, IH.
Qed.

(**
  What happens when we try to define an evil function, like the one that
  tries to extract the "head" element from a set?
*)
Definition head {A : Type} (s : FinSet A) : option A.
Proof.
  (*
    match s with
    | empty => None
    | scons x _ => Some x
    end
  *)
  refine
  (
    @FinSet_rec A (option A)
    None
    (fun x _ => Some x)
    _ _ s
  ); clear s; cycle 1.
  (* The [idem] case goes through quite easily. *)
  - easy.
  (*
    But in the [swap] case we need to prove [Some x = Some y] for arbitrary
    [x] and [y], which won't be possible.
  *)
  - intros x y s.
Abort.

Definition map {A B : Type} (f : A -> B) (s : FinSet A) : FinSet B.
Proof.
  refine
  (
    @FinSet_rec A (FinSet B)
    empty
    (fun x rc => scons (f x) rc)
    _ _ s
  ); clear s.
  - now intros x y s; apply swap.
  - now intros; apply idem.
Defined.

Definition filter {A : Type} (p : A -> bool) (s : FinSet A) : FinSet A.
Proof.
  refine
  (
    @FinSet_rec A (FinSet A)
    empty
    (fun x rc => if p x then scons x rc else rc)
    _ _ s
  ); clear s.
  - now intros x y s'; destruct (p x), (p y); [apply swap | | |].
  - now intros x s; destruct (p x); [apply idem |].
Defined.

Definition join {A : Type} (ss : FinSet (FinSet A)) : FinSet A.
Proof.
  refine
  (
    @FinSet_rec (FinSet A) (FinSet A)
    empty
    (fun x rc => union x rc)
    _ _ ss
  ); clear ss.
  - now intros x y z; rewrite <- union_assoc, (union_comm x y), union_assoc.
  - now intros x y; rewrite <- union_assoc, union_idem.
Defined.

Definition any {A : Type} (p : A -> bool) (s : FinSet A) : bool.
Proof.
  refine
  (
    @FinSet_rec A bool
    false
    (fun x rc => orb (p x) rc)
    _ _ s
  ); clear s.
  - now intros x y s; destruct (p x), (p y).
  - now intros x s; destruct (p x); cbn.
Defined.

Definition all {A : Type} (p : A -> bool) (s : FinSet A) : bool.
Proof.
  refine
  (
    @FinSet_rec A bool
    true
    (fun x rc => andb (p x) rc)
    _ _ s
  ); clear s.
  - now intros x y s; destruct (p x), (p y).
  - now intros x s; destruct (p x); cbn.
Defined.

(*
Definition elem_of {A : Type} `{EqDecision A} (s : FinSet A) (x : A) : bool.
Proof.
  refine
  (
    @FinSet_rec A bool
    false
    (fun y rc => if decide (x = y) then true else rc)
    _ _ s
  ); clear s.
  - by intros y1 y2 b; destruct (decide (x = y1)), (decide (x = y2)).
  - by intros y b; destruct (decide (x = y)).
Defined.
*)