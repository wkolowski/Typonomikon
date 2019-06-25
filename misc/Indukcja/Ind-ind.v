(**

  If there was induction-induction in Coq, we could use it to define a type
  of sorted lists like this: *)

  Fail

  Inductive slist {A : Type} (R : A -> A -> Prop) : Type :=
      | snil : slist R
      | scons : forall (h : A) (t : slist A), ok h t -> slist A

  with ok {A : Type} {R : A -> A -> Prop} : A -> slist R -> Prop :=
      | ok_snil : forall x : A, ok x snil
      | ok_scons :
          forall (h : A) (t : slist A) (p : ok h t) (x : A),
            R x h -> ok x (scons h t p).

(*

  Not like we need to - we can of course do the same thing by first defining
  list and only then sortedness. But the goal of this file is to investigate
  induction-induction.

  Since we can't have this definition, let's give it to ourselves by means
  of some axioms.

*)

Variables
  (slist : forall {A : Type}, (A -> A -> Prop) -> Type)
  (ok : forall {A : Type} {R : A -> A -> Prop}, A -> slist R -> Prop)
  (snil : forall {A : Type} {R : A -> A -> Prop}, slist R)
  (scons :
    forall {A : Type} {R : A -> A -> Prop} (h : A) (t : slist R),
      ok h t -> slist R)
  (ok_snil :
    forall {A : Type} {R : A -> A -> Prop} (x : A), ok x (@snil _ R))
  (ok_scons :
    forall
      {A : Type} {R : A -> A -> Prop}
      (h : A) (t : slist R) (p : ok h t)
      (x : A), R x h -> ok x (scons h t p))
  (ind : forall
    (A : Type) (R : A -> A -> Prop)
    (P : slist R -> Type)
    (Q : forall (h : A) (t : slist R), ok h t -> Type)
    (Psnil : P snil)
    (Pscons :
      forall (h : A) (t : slist R) (p : ok h t),
        P t -> Q h t p -> P (scons h t p))
    (Qsnil : forall x : A, Q x snil (ok_snil x))
    (Qscons :
      forall
        (h : A) (t : slist R) (p : ok h t)
        (x : A) (H : R x h),
          P t -> Q h t p -> Q x (scons h t p) (ok_scons h t p x H)),
    {f : (forall l : slist R, P l) &
    {g : (forall (h : A) (t : slist R) (p : ok h t), Q h t p) &
      f snil = Psnil /\
      (forall (h : A) (t : slist R) (p : ok h t),
        f (scons h t p) = Pscons h t p (f t) (g h t p)) /\
      (forall x : A,
        g x snil (ok_snil x) = Qsnil x) /\
      (forall
        (h : A) (t : slist R) (p : ok h t)
        (x : A) (H : R x h),
          g x (scons h t p) (ok_scons h t p x H) =
          Qscons h t p x H (f t) (g h t p))
    }}).

(** A non-dependent recursor that ignores the ordering ok. *)
Definition rec'
  {A : Type} {R : A -> A -> Prop}
  (P : Type) (snil' : P) (scons' : A -> P -> P) :

  {f : slist R -> P &
    f snil = snil' /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = scons' h (f t)
  }.
Proof.
  (* Apply the induction principle with appropriate arguments.
     Not that hard to figure out. *)
  destruct
  (
    ind
    A R
    (fun _ => P) (fun _ _ _ => True)
    snil' (fun h _ _ t _ => scons' h t)
    (fun _ => I) (fun _ _ _ _ _ _ _ => I)
  )
  as (f & g & H1 & H2 & H3 & H4).
  exists f. split.
    exact H1.
    exact H2.
Defined.

Require Import List.
Import ListNotations.

(** Converted a sorted list to an ordinary list. *)
Definition toList
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> list A &
    f snil = [] /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = h :: f t
  }.
Proof.
  exact (rec' (list A) [] cons).
Defined.