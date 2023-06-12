(** * G3: Wyższe Typy Induktywne [TODO] *)

(** Tutaj jakieś nie-homotopiczne przykłady, np. pary nieuporządkowane, zbiory,
    albo coś w ten deseń. *)

(** * Wstęp (TODO) *)

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

(** * Pary nieuporządkowane (TODO) *)

Module UPair.

Private Inductive UPair (A : Type) : Type :=
| upair : A -> A -> UPair A.

Arguments upair {A} _ _.

Axiom comm :
  forall {A : Type} (x y : A), upair x y = upair y x.

Section rec.

Context
  (A : Type)
  (P : Type)
  (upair' : A -> A -> P)
  (comm'  : forall (x y : A), upair' x y = upair' y x).

Definition UPair_rec
  (comm'  : forall (x y : A), upair' x y = upair' y x)
  (u : UPair A) : P :=
match u with
| upair x y => upair' x y
end.

Axiom UPair_rec_comm :
  forall (x y : A),
    ap (UPair_rec comm') (comm x y) = comm' x y.

End rec.

Section ind.

Context
  (A : Type)
  (P : UPair A -> Prop)
  (upair' : forall (x y : A), P (upair x y)).

Definition UPair_ind (u : UPair A) : P u :=
match u with
| upair x y => upair' x y
end.

End ind.

Section rect.

Context
  (A : Type)
  (P : UPair A -> Type)
  (upair' : forall (x y : A), P (upair x y))
  (Comm'  :=
    forall (x y : A),
      transport _ (comm x y) (upair' x y) = upair' y x)
  (comm'  : Comm').

Definition UPair_rect (comm' : Comm') (u : UPair A) : P u :=
match u with
| upair x y => upair' x y
end.

Axiom UPair_rect_comm :
  forall (x y : A),
    apd (UPair_rect comm') (comm x y) = comm' x y.

End rect.

End UPair.

Import UPair.

Definition swap {A : Type} (u : UPair A) : UPair A.
Proof.
  refine (UPair_rec A (UPair A)
    (fun x y => upair y x)
    _
    u).
  now intros; apply comm.
Defined.

Lemma no_fst :
  (forall {A : Type}, exists (fst : UPair A -> A), forall x y : A, fst (upair x y) = x) -> False.
Proof.
  intros H.
  cut (true = false); [now congruence |].
  destruct (H bool) as [fst fst_spec].
  rewrite <- (fst_spec true false).
  rewrite comm.
  rewrite fst_spec.
  easy.
Qed.