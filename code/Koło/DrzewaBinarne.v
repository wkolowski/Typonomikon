(** Na dzisiejszym kole było całkiem wesoło - okazuje się, ża każdy zrozumiał to samo polecenie inaczej, a pote,
    wszyscy robili te same błędy, ale w różnej kolejności. *)

(** **** Ćwiczenie *)

(** Zdefiniuj typ drzew binarnych (tzn. drzewo może mieć 0, 1 lub 2 poddrzewa), które potencjalnie mogą być puste. *)

Module Z1.

(** Komentarz: większości osób udało się bez większych problemów. *)

(** * Oczekiwana odpowiedź *)

Inductive BTree (A : Type) : Type :=
    | E : BTree A
    | N : A -> BTree A -> BTree A -> BTree A.

(** * Wariacje w rozumieniu *)

(** Brak elementów w węzłach. Doprecyzowanie polecenia: typ drzew binarnych trzymających
    elementy typu [A] w węzłach. Być może trzeba też wytłumaczyć, co to węzły, liście etc. *)
Module Wariacja1.
Inductive BTree : Type :=
    | E : BTree
    | N : BTree -> BTree -> BTree.
End Wariacja1.

(** * Niepoprawne opdowiedzi *)

(** Brakuje jednego poddrzewa, co zamienia "drzewo" w listę. *)
Module Fail1.
Inductive BTree (A : Type) : Type :=
    | E : BTree A
    | N : A -> BTree A -> BTree A.
End Fail1.

End Z1.

(** **** Ćwiczenie *)

(** Zdefiniuj typ drzew binarnych (tzn. 0, 1 lub 2 poddrzewa), które muszą być niepuste. *)

Module Z2.

(** Komentarz: ilość niepoprawnych opdowiedzi (których nawet się nie spodziewałem) zdecydowanie wyjebało ponad
    skalę. *)

(** * Oczekiwana odpowiedź *)

Inductive Tree (A : Type) : Type :=
    | L : A -> Tree A
    | N : Tree A -> Tree A -> Tree A.

(** * Wariacje w rozumieniu *)

(** Większość osób zinterpretowała to jako "typ niepustych drzew binarnych, które trzymają elementy w węzłach".
    W sumie to się im nie dziwię. Tę wariację przyjąłem jako właściwą interpretację. *)
Module Wariacja1.
Inductive Tree (A : Type) : Type :=
    | T : A -> option (Tree A) -> option (Tree A) -> Tree A.
End Wariacja1.

(** To samo co wyżej, tylko że inaczej wyrażone. *)
Module Wariacja2.
Inductive Tree (A : Type) : Type :=
    | E : A -> Tree A
    | L : A -> Tree A -> Tree A
    | R : A -> Tree A -> Tree A
    | N : A -> Tree A -> Tree A -> Tree A.
End Wariacja2.

(** * Niepoprawne opdowiedzi: *)

(** Nie można zrobić drzewa z jednym poddrzewem. *)
Module Fail1.
Inductive Tree (A : Type) : Type :=
    | E : A -> Tree A
    | N : A -> Tree A -> Tree A -> Tree A.
End Fail1.

(** Nie można odróżnić czy pojedyncze poddrzewo jest lewe czy prawe. *)
Module Fail2.
Inductive Tree (A : Type) : Type :=
    | E : A -> Tree A
    | S : A -> Tree A -> Tree A
    | N : A -> Tree A -> Tree A -> Tree A.
End Fail2.

(** Nie można zrobić drzewa z dwoma elementami (różne wariacje). *)
Module Fail3.
Inductive Tree (A : Type) : Type :=
    | L : A -> Tree A
    | N : A -> Tree A -> Tree A -> Tree A.
End Fail3.

End Z2.

(** **** Ćwiczenie *)

(** Zdefiniuj typ drzew binarnych, które mogą mieć dowolną (ale skończoną) ilość poddrzew. *)

Module Z3.

(** Komentarz: tutaj też było dziwnie. *)

(** * Oczekiwana odpowiedź *)

Inductive Tree' (A : Type) : Type :=
    | T : A -> list (Tree' A) -> Tree' A.

Inductive Tree (A : Type) : Type :=
    | Empty    : Tree A
    | NonEmpty : Tree' A -> Tree A.

(** * Wariacje w rozumieniu *)

(** Drzewo niepuste. *)
Module Wariacja1.
Inductive Tree (A : Type) : Type :=
    | T : A -> list (Tree A) -> Tree A.
End Wariacja1.

(** * Niepoprawne opdowiedzi *)

(** Nieskończenie wiele reprezentacji liścia, np. N x [], N x [E]. N x [E, E] etc. *)
Module Fail1.
Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N : A -> list (Tree A) -> Tree A.
End Fail1.

(** Dwie reprezentacje liścia (E x, N x []), drzewo niepuste. *)
Module Fail2.
Inductive Tree (A : Type) : Type :=
    | E : A -> Tree A
    | N : A -> list (Tree A) -> Tree A.
End Fail2.

(** Nieskończenie wiele reprezentacji drzewa pustego. *)
Module Fail3.
Inductive Tree (A : Type) : Type :=
    | E : A -> Tree A
    | N : list (Tree A) -> Tree A.
End Fail3.

End Z3.