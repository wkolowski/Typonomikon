Module NegativeCoInductive.

Set Primitive Projections.

(** Uwaga: można już w definicji zadeklarować nazwę konstruktora. *)
CoInductive Stream (A : Type) : Type := Cons
{
  hd : A;
  tl : Stream A;
}.

Arguments hd {A} _.
Arguments tl {A} _.

Print Stream.
(* ===>
   CoInductive Stream (A : Type) : Type := Cons { hd : A;  tl : Stream A }

   Stream has primitive projections without eta conversion.
   Arguments Stream _%type_scope
   Arguments Cons _%type_scope _ _
*)

(** Kluczowa linijka: Stream has primitive projections without eta conversion.
    Oznacza ona, że [Stream] ma włączone Primitive Projections, czyli że jest
    natywnym rekordem, czyli że faktycznie jest negatywnym typem koinduktywnym,
    a nie tylko fancy notacją na pozytywny typ koinduktywny z jednym konstruktorem. *)

Lemma Stream_eq_intro :
  forall {A : Type} (s1 s2 : Stream A),
    hd s1 = hd s2 -> tl s1 = tl s2 -> s1 = s2.
Proof.
  Fail destruct s1.
  (* ===> Dependent case analysis is not allowed for inductive definition Stream. *)
Abort.

Lemma Stream_uniqueness :
  forall {A : Type} (s : Stream A), s = Cons A (hd s) (tl s).
Proof.
  Fail destruct s.
  (* ===> Dependent case analysis is not allowed for inductive definition Stream. *)
Abort.

End NegativeCoInductive.

Module PositiveCoInductive.

Unset Primitive Projections.

(** Uwaga: można już w definicji zadeklarować nazwę konstruktora. *)
CoInductive Stream (A : Type) : Type := Cons
{
  hd : A;
  tl : Stream A;
}.

Arguments hd {A} _.
Arguments tl {A} _.

Print Stream.
(* ===>
   CoInductive Stream (A : Type) : Type := Cons { hd : A;  tl : Stream A }

   Arguments Stream _%type_scope
   Arguments Cons _%type_scope _ _
*)

(** Tym razem kluczowy jest brak żadnej wzmianki o Primitive Projections, co
    oznacza, że [Stream] jest pozytywnym typem koinduktywnym z jednym konstruktorem
    [Cons], który bierze [hd : A] i [tl : Stream A] jako argumenty. *)

Lemma Stream_eq_intro :
  forall {A : Type} (s1 s2 : Stream A),
    hd s1 = hd s2 -> tl s1 = tl s2 -> s1 = s2.
Proof.
  destruct s1, s2; cbn; intros -> ->. reflexivity.
Qed.

Lemma Stream_uniqueness :
  forall {A : Type} (s : Stream A), s = Cons A (hd s) (tl s).
Proof.
  destruct s; cbn. reflexivity.
Qed.

(** Oba poprzednio niemożliwe twierdzenia da się teraz udowodnić bez problemu. *)

End PositiveCoInductive.