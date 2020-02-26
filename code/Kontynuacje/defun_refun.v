(** Bardzo insajtowy filmik (i transkrypcjo-artykuł) o defunkcjonalizacji
    (i refunkcjonalizacji też):

    http://www.pathsensitive.com/2019/07/the-best-refactoring-youve-never-heard.html

    Ok, o co chodzi? *)

Require Import D5.

Print filter.
(* ===> filter =
        fun (A : Type) (p : A -> bool) =>
        fix filter (l : list A) {struct l} : list A :=
          match l with
          | [] => []
          | h :: t => if p h then h :: filter t else filter t
          end
             : forall A : Type, (A -> bool) -> list A -> list A *)

(** Przyjrzyjmy się funkcji [filter] (w nieco zmodyfikowanej wersji -
    potrafisz powiedzieć, czym różni się ona od tej z rozdziału o
    listach?). Jest to prosta funkcja, która wyrzuca z listy elementy,
    które nie spełniają predykatu [p].

    I cóż, że ze Szwecji? Ano, jest pewna kolosalna różnica między
    funkcją [filter], którą znamy z Coqa, oraz filtrami, które
    znamy z różnych programów czy stron internetowych: argumentem
    [filter] jest predykat boolowski, ale filtrowania w rzeczywistym
    świecie mają zazwyczaj charakter zaznaczenia jakiegoś checkboxa
    w stylu "tylko ze zdjęciem" czy wybrania zakresu cen/ocen. Żadne
    rzeczywistoświatowe filtrowanie raczej nie pozwali nam podać
    predykatu boolowskiego. *)

Inductive MyFilter : Type :=
    | IsEven : MyFilter
    | LessThan : nat -> MyFilter
    | LifeUniverseAndAllThat : MyFilter
    | And : MyFilter -> MyFilter -> MyFilter
    | Or : MyFilter -> MyFilter -> MyFilter
    | Not : MyFilter -> MyFilter.

Fixpoint apply (p : MyFilter) (n : nat) : bool :=
match p with
    | IsEven => even n
    | LessThan m => n <? m
    | LifeUniverseAndAllThat => n =? 42
    | And p1 p2 => apply p1 n && apply p2 n
    | Or p1 p2 => apply p1 n || apply p2 n
    | Not p' => negb (apply p' n)
end.