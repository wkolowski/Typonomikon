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

(** Zdefiniuj typ drzew o dowolnym skończonym rozgałęzieniu (tym razem mogą być puste). *)

Module Z3.

(** Komentarz: sporo osób (czyli chyba wszystkie) myślało wewnątrz pudełka i próbowali to zrobić za pomocą
    pojedynczej definicji induktywnej, czyli źle. *)

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

(** **** Ćwiczenie *)

(** Zdefiniuj drzewo, które jest puste lub ma element i nieskończenie wiele poddrzew. *)

(** Komentarz: niektórzy mają problem z rozróżnieniem nieskończoności od liczby skończonej, ale
    nieograniczonej. *)

Module Z4.

(* * Oczekiwana odpowiedź *)

Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N : A -> (nat -> Tree A) -> Tree A.

(** * Niepoprawne odpowiedzi *)

(** Brakuje przypadku bazowego. *)
Module Fail1.
Inductive Tree (A : Type) : Type :=
    | T : A -> (nat -> Tree A) -> Tree A.
End Fail1.

End Z4.

(** **** Ćwiczenie *)

(** Zdefiniuj drzewo (potencjalnie puste), które trzyma wartości w węzłach i może mieć dowolną ilość poddrzew
    (także nieskończoną, nieprzeliczalną etc.). *)

Module Z5.

(** Komentarz: pojawiły się problemy z rozróżnieniem [forall B : Type, B -> ...] od [Type -> ...] (czyli problemy
    w rozumieniu kwantyfikatorów przemieszanych z funkcjami oraz problemy z rozumieniem określeń "dowolny" oraz
    "dowolny, ale ustalony (przez użytkownika)". *)

(** * Oczekiwana odpowiedź *)

Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N : A -> forall B : Type, (B -> Tree A) -> Tree A.

(** * Niepoprawne odpowiedz *)

(** Nawias postawiony przed kwantyfikatorem, a nie za, co zupełnie zmienia znaczenie wszystkiego. *)
Module Fail1.
Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N : A -> (forall B : Type, B -> Tree A) -> Tree A.
End Fail1.

(** Drzewo, które oprócz elementów typu [A] przechowuje w węzłach typy. *)
Module Fail2.
Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N : A -> Type -> Tree A.
End Fail2.

(** Drzewo o sztywnym rozgałęzieniu, które jest uniwersum-duże. *)
Module Fail3.
Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N : A -> (Type -> Tree A) -> Tree A.
End Fail3.

(** Drzewo o dowolnym sztywnym rozgałęzieniu wybranym przez użytkownika. *)
Module Fail4.
Inductive Tree (A B : Type) : Type :=
    | E : Tree A B
    | N : A -> (B -> Tree A B) -> Tree A B.
End Fail4.

End Z5.