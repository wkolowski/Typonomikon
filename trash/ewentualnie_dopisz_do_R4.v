
(* begin hide *)
(* TODO: [induction], [inversion], [destruct] *)
(* end hide *)

(** TODO:
    - przerobić "drobne taktyki" na "taktyki do zarządzania kontekstem"
    - przenieść opis taktyki [pattern] (i odpowiadające zadanie) do części
      o taktykach dla redukcji *)

(** * Taktyki do redukcji i obliczeń *)

(** Posłużyć się następującym systemem nazewniczo-klasyfikacyjnym.
    Dla każdej literki są trzy relacje: redukcja, ekspansja i konwersja.
    Bazą jest ekspansją, która ma jakąś swoją definicję, pisana jest
    a -> b. Relacja ekspansji a <- b zdefiniowana jest jako b -> a, zaś
    relacja konwersji to domknięcie równoważnościowe relacji redukcji.

    Mamy następujące relacje redukcji:
    - alfa (zmiana nazwy jednej zmiennej związanej)
    - beta (podstawienie argumentu za parametr formalny w jednym miejscu)
    - delta (odwinięcie jednej definicji) — uwaga: to w sumie nie jest
      relacja, tylko rodzina relacji parametryzowana/indeksowana nazwami,
      które chcemy odwinąć
    - eta (?)
    - iota (wykonanie jednego dopasowania do wzorca)
    - zeta (redukcja pojedynczego [let]a)

    Odpowiadające taktyki:
    - alfa — brak (ewentualnie [change])
    - beta — [pattern] do beta ekspansji
    - delta — [unfold] (delta redukcja), [fold] (delta ekspansja)
    - eta — [extensionality]
    - iota — raczej brak (ewentualnie [change])
    - zeta — raczej brak (ewentualnie [change]) *)

(** Omówić następujące taktyki (w kolejności):
    - [pattern] (beta ekspansja)
    - [unfold], [fold] (delta redukcja/ekspansja)
    - [change] (konwertowalność)
    - [cbn]
    - [compute], [vm_compute], [native_compute]
    - [cbv], [lazy]
    - [red]
    - [simpl]
    - [hnf] *)

(** Omówić postacie normalne (o ile gdzieś można znaleźć jakiś ich opis. *)