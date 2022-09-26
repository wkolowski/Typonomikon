Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) : P x -> P y :=
match p with
| eq_refl _ => fun u : P x => u
end.

Definition transportconst
  {A B : Type} {x y : A} (p : x = y) (b : B)
  : @transport A (fun _ => B) x y p b = b :=
match p with
| eq_refl => eq_refl
end.

Definition apd
  {A : Type} {P : A -> Type} (f : forall x : A, P x) {x y : A} (p : x = y)
  : transport P p (f x) = (f y) :=
match p with
| eq_refl => eq_refl (f x)
end.

Module FinSet.

Private Inductive FinSet (A : Type) : Type :=
| empty : FinSet A
| scons : A -> FinSet A -> FinSet A.

Arguments empty {A}.
Arguments scons {A} _ _.

Axiom swap :
  forall {A : Type} (x y : A) (s : FinSet A),
    scons x (scons y s) = scons y (scons x s).

Axiom idem :
  forall {A : Type} (x : A) (s : FinSet A),
    scons x (scons x s) = scons x s.

Section rect.

Context
  (A : Type)
  (P : FinSet A -> Type)
  (empty' : P empty)
  (scons' : forall (x : A) {s : FinSet A}, P s -> P (scons x s))
  (swap'  : forall (x y : A) {s : FinSet A} (s' : P s),
              transport _ (swap x y s) (scons' x (scons' y s')) = scons' y (scons' x s'))
  (idem'  : forall (x : A) {s : FinSet A} (s' : P s),
              transport _ (idem x s) (scons' x (scons' x s')) = scons' x s').

Fixpoint FinSet_rect
  (swap'  : forall (x y : A) {s : FinSet A} (s' : P s),
              transport _ (swap x y s) (scons' x _ (scons' y _ s')) = scons' y _ (scons' x _ s'))
  (idem'     : forall (x : A) {s : FinSet A} (s' : P s),
                 transport _ (idem x s) (scons' x _ (scons' x _ s')) = scons' x _ s')
  (s : FinSet A) : P s :=
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

Section ind.

Context
  (A : Type)
  (P : FinSet A -> Prop)
  (empty' : P empty)
  (scons' : forall (x : A) {s : FinSet A}, P s -> P (scons x s)).

Fixpoint FinSet_ind (s : FinSet A) : P s :=
match s with
| empty => empty'
| scons x s' => scons' x s' (FinSet_ind s')
end.

(* Axiom FinSet_rect_swap :
  forall (x y : A) (s : FinSet A),
    apd FinSet_ind (swap x y s) = swap' x y s (FinSet_ind s).

Axiom FinSet_rect_idem :
  forall (x : A) (s : FinSet A),
    apd (FinSet_rect swap' idem') (idem x s) = idem' x s (FinSet_rect swap' idem' s). *)

End ind.

End FinSet.

Import FinSet.

Definition union {A : Type} (s1 s2 : FinSet A) : FinSet A.
Proof.
  refine
  (
    @FinSet_rect A (fun _ => FinSet A)
    s2
    (fun x _ rc => scons x rc)
    _ _ s1
  ); clear s1 s2.
(*   - intros.
    destruct (swap x y s); cbn.
    now apply swap.
  - intros.
    destruct (idem x s).
    now apply idem.
*)
  - abstract (intros; destruct (swap x y s); apply swap).
  - abstract (intros; destruct (idem x s); apply idem).
Defined.

Lemma union_empty_l :
  forall {A : Type} (s : FinSet A),
    union empty s = s.
Proof. easy. Defined.

Lemma union_scons_l :
  forall {A : Type} (x : A) (s1 s2 : FinSet A),
    union (scons x s1) s2 = scons x (union s1 s2).
Proof. easy. Defined.

Lemma union_empty_r :
  forall {A : Type} (s : FinSet A),
    union s empty = s.
Proof.
  intros A s.
  refine
  (
    @FinSet_ind A (fun s => union s empty = s)
    _
    _
    s
  ); clear s.
  - now rewrite union_empty_l.
  - now intros x s IH; rewrite union_scons_l, IH.
Qed.

Lemma union_scons_r :
  forall {A : Type} (x : A) (s1 s2 : FinSet A),
    union s1 (scons x s2) = scons x (union s1 s2).
Proof.
  intros A x s1.
  refine
  (
    @FinSet_ind A (fun s => forall s2, union s (scons x s2) = scons x (union s s2))
    _
    _
    s1
  ); clear s1.
  - easy.
  - now intros y s1' IH s2; rewrite !union_scons_l, IH, swap.
Qed.

Lemma union_comm :
  forall {A : Type} (s1 s2 : FinSet A),
    union s1 s2 = union s2 s1.
Proof.
  intros A s1 s2.
  refine
  (
    @FinSet_ind A (fun s => union s s2 = union s2 s)
    _
    _
    s1
  ).
  - now cbn; rewrite union_empty_r.
  - now intros x s IH; rewrite union_scons_l, union_scons_r, IH.
Qed.

Definition head {A : Type} (s : FinSet A) : option A.
Proof.
  refine
  (
    @FinSet_rect A (fun _ => option A)
    None
    (fun x _ _ => Some x)
    _ _ s
  ); clear s; cycle 1.
  - intros x s _.
    now destruct (idem x s); cbn.
  - intros x y s _.
    destruct (swap x y s); cbn.
Abort.