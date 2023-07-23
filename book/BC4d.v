(** * BC4d: Nierówność i różność [TODO] *)

Require Import Setoid.

(** * Nierówność (TODO) *)

(** * Różność *)

(** ** (Słaba) różność funkcji *)

(** Funkcje są różne (w silnym sensie), gdy różnią się dla jakiegoś
    argumentu. *)

Definition fun_apart {A B : Type} (R : B -> B -> Type) (f g : A -> B) : Type :=
  {x : A & R (f x) (g x)}.

Lemma fun_apart_spec :
  forall {A B : Type} (R : B -> B -> Type) (f g : A -> B),
    (forall x : B, R x x -> False) ->
      fun_apart R f g -> f <> g.
(* begin hide *)
Proof.
  intros A B R f g HR [x r] ->.
  now apply HR in r.
Qed.
(* end hide *)

Lemma fun_apart_spec' :
  forall {A B : Type} (R : B -> B -> Type) (f g : A -> B),
    (forall x : B, R x x -> False) ->
      fun_apart R f g -> ~ (forall x : A, f x = g x).
(* begin hide *)
Proof.
  intros A B R f g HR [x r] Hext.
  rewrite Hext in r.
  now apply HR in r.
Qed.
(* end hide *)

(** ** Silna różność funkcji (TODO) *)

Inductive strong_fun_apart
  {A B : Type} (RA : A -> A -> Type) (RB : B -> B -> Type) (f g : A -> B) : Type :=
| sfa (x1 x2 : A) (ra : RA x1 x2) (rb : RB (f x1) (g x2)).

Lemma strong_fun_apart_spec :
  forall {A B : Type} (RB : B -> B -> Type) (f g : A -> B),
    strong_fun_apart eq RB f g -> fun_apart RB f g.
(* begin hide *)
Proof.
  intros A B RB f g [x ? <- rb].
  now exists x.
Qed.
(* end hide *)

(** ** Różność funkcji zależnych (TODO) *)

Inductive dep_fun_apart
  {A : Type} {B : A -> Type}
  (R : forall x : A, B x -> B x -> Type)
  (f g : forall x : A, B x) : Type :=
| dep_fun_apart' : forall {x : A}, R x (f x) (g x) -> dep_fun_apart R f g.

Lemma dep_fun_apart_spec :
  forall
    {A : Type} {B : A -> Type}
    (R : forall x : A, B x -> B x -> Type)
    (f g : forall x : A, B x)
    (HR : forall {x : A} (y : B x), R x y y -> False),
      dep_fun_apart R f g -> f <> g.
(* begin hide *)
Proof.
  intros A B R f g HR [x r] ->.
  apply (HR _ (g x)). apply r.
Qed.
(* end hide *)

Lemma dep_fun_apart_spec' :
  forall
    {A : Type} {B : A -> Type}
    (R : forall x : A, B x -> B x -> Type)
    (f g : forall x : A, B x)
    (HR : forall {x : A} (y : B x), R x y y -> False),
      dep_fun_apart R f g -> ~ (forall x : A, f x = g x).
(* begin hide *)
Proof.
  intros A B R f g HR [x r] Hext.
  apply (HR _ (g x)).
  rewrite <- Hext at 1.
  assumption.
Qed.
(* end hide *)