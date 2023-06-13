(** * G8a: Programowanie generyczne [TODO] *)

(* begin hide *)
(* TODO: https://effectfully.blogspot.com/2016/04/descriptions.html *)
(* end hide *)

(** Tutaj o programowaniu generycznym za pomocą uniwersów kodów. Na końcu
    generycznie zajmiemy się typami (ko)induktywnymi, badając W- i M-typy,
    a potem oparte na nich uniwersa kodów.

    Być może to właśnie tutaj jest odpowiednie miejsce aby wprowadzić
    indukcję-rekursję. *)

(** * Spłaszczanie wielokrotnie zagnieżdżonych list *)

Require Import List.
Import ListNotations.

Module Flatten.

Inductive Star : Type :=
| Var : Type -> Star
| List : Star -> Star.

Fixpoint interp (s : Star) : Type :=
match s with
| Var A => A
| List s' => list (interp s')
end.

Fixpoint flattenType (s : Star) : Type :=
match s with
| Var A => A
| List s' => flattenType s'
end.

Fixpoint flatten {s : Star} : interp s -> list (flattenType s) :=
match s with
| Var A => fun x : interp (Var A) => [x]
| List s' =>
  fix f (x : list (interp s')) : list (flattenType s') :=
  match x with
  | [] => []
  | h :: t => @flatten s' h ++ f t
  end
end.

Compute @flatten (List (List (Var nat))) [[1; 2; 3]; [4; 5; 6]].
Compute
  @flatten
    (List (List (List (Var nat))))
    [[[1]; [2; 2]; [3]]; [[4; 5; 6]]].

Class HasStar (A : Type) : Type :=
{
  star : Star;
  no_kidding : interp star = A;
}.

#[refine]
#[export]
Instance HasStar_any (A : Type) : HasStar A | 1 :=
{
  star := Var A;
}.
Proof.
  cbn. reflexivity.
Defined.

#[refine]
#[export]
Instance HasStar_list (A : Type) (hs : HasStar A) : HasStar (list A) | 0 :=
{
  star := List star;
}.
Proof.
  cbn. rewrite no_kidding. reflexivity.
Defined.

Definition flatten'
  {A : Type} {_ : HasStar A} (x : A) : list (flattenType star).
Proof.
  apply flatten. rewrite no_kidding. exact x.
Defined.

Compute flatten' [[1; 2; 3]; [4; 5; 6]].
Compute flatten' [[[1]; [2; 2]; [3]]; [[4; 5; 6]]].

End Flatten.

(** * [zipWith] z dowolną ilością argumentów *)

From Typonomikon Require D5.

Module ZipWithN.

Import D5.

Inductive Code : Type :=
| Singl : Type -> Code
| Cons : Type -> Code -> Code.

Fixpoint cmap (F : Type -> Type) (c : Code) : Code :=
match c with
| Singl A => Singl (F A)
| Cons A c' => Cons (F A) (cmap F c')
end.

Fixpoint funType (c : Code) (R : Type) : Type :=
match c with
| Singl A => A -> R
| Cons A c' => A -> funType c' R
end.

Definition listType (c : Code) (R : Type) : Type :=
  funType (cmap list c) R.

Fixpoint prod (c : Code) : Type :=
match c with
| Singl A => A
| Cons A c' => A * prod c'
end.

Definition prodList (c : Code) : Type :=
  prod (cmap list c).

Definition listProd (c : Code) : Type :=
  list (prod c).

Definition uncurriedFunType (c : Code) (R : Type) : Type :=
  prod c -> R.

Definition uncurriedListType (c : Code) (R : Type) : Type :=
  prodList c -> R.

Fixpoint zip2 {A B : Type} (l : list A) (r : list B) : list (A * B) :=
match l, r with
| [], _ => []
| _, [] => []
| hl :: tl, hr :: tr => (hl, hr) :: zip2 tl tr
end.

Fixpoint zip {c : Code} : prodList c -> listProd c :=
match c with
| Singl A => id
| Cons A c' =>
  fun '(l, p) => zip2 l (zip p)
end.

Compute
  @zip
    (Cons bool (Singl nat))
    ([true; false], [4; 5]).

Fixpoint uncurryFun
  {c : Code} {R : Type} {struct c} : funType c R -> uncurriedFunType c R.
Proof.
  destruct c; cbn in *; intro f; red; cbn.
    exact f.
    intros [t p]. exact (uncurryFun _ _ (f t) p).
Defined.

Fixpoint curryList
  {c : Code} {R : Type} {struct c} : uncurriedListType c R -> listType c R.
Proof.
  destruct c as [A | A c']; unfold uncurriedListType; cbn in *.
    intros f l. exact (f l).
    intros f l. apply curryList. red. intro. apply f. split; assumption.
Defined.

Definition zipWith
  {c : Code} {R : Type} (f : funType c R) : listType c (list R) :=
    curryList (fun p : prodList c => map (uncurryFun f) (zip p)).

Compute
  @zipWith
    (Cons nat (Cons nat (Singl nat))) _
    (fun a b c => a + b + c)
    [1; 2; 3] [4; 5; 6] [7; 8; 9].

End ZipWithN.

(** * Porządna negacja (albo i nie) [TODO] *)

(** Pomysł: silną negację można zdefiniować przez rekursję po uniwersum
    kodów, w którym są kody na wszystkie potrzebne typy. *)

From Typonomikon Require D1 D2.

Module Negation.

(*
Inductive U : Type :=
| F : U
| T : U
| And : U -> U -> U
| Or : U -> U -> U
| Impl : U -> U -> U.
*)

From Typonomikon Require Import D1 D1z D2.
(* TODO: Import PoorUniverse. *)

End Negation.