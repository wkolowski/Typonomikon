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

Require Import List.
Import ListNotations.

Fixpoint flatten {s : Star} : interp s -> list (flattenType s) :=
match s with
    | Var A => fun x : interp (Var A) => [x]
    | List s' => fix f (x : list (interp s')) : list (flattenType s') :=
        match x with
            | [] => []
            | h :: t => @flatten s' h ++ f t
        end
end.

Compute @flatten (List (List (Var nat))) [[1; 2; 3]; [4; 5; 6]].
Compute @flatten (List (List (List (Var nat)))) [[[1]; [2; 2]; [3]]; [[4; 5; 6]]].

Class HasStar (A : Type) : Type :=
{
    star : Star;
    no_kidding : interp star = A;
}.

#[refine]
Instance HasStar_any (A : Type) : HasStar A | 1 :=
{
    star := Var A;
}.
Proof.
  cbn. reflexivity.
Defined.

#[refine]
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
  apply flatten. rewrite no_kidding. exact x. Show Proof.
Defined.

Compute flatten' [[1; 2; 3]; [4; 5; 6]].
Compute flatten' [[[1]; [2; 2]; [3]]; [[4; 5; 6]]].