(** * Bajeczka *)

(** Co to są termy? Po polsku: wyrażenia. Są to napisy zbudowane według
    pewnych reguł (które będziemy chcieli poznać), które mogą oznaczać
    przeróżne rzeczy: zdania logiczne i ich dowody, programy i ich
    specyfikacje, obiekty matematyczne takie jak liczby czy funkcje,
    struktury danych takie jak napisy czy listy.

    Najważniejszym, co wiemy o każdym termie, jest jego typ. Co to jest typ?
    To taki klasyfikator, który mówi, czego możemy się po termie spodziewać -
    można liczyć za pomocą liczb, ale nie za pomocą wartości logicznych.
    Można dowodzić zdań, ale nie napisów. Można skleić ze sobą dwa napisy,
    ale nie napis i funkcję etc.

    Każdy term ma tylko jeden typ, więc każdy typ możemy sobie wyobrazić jako
    wielki worek z termami. Dla przykładu, typ [nat], czyli typ liczb
    naturalnych, to worek, w którym są takie wyrażenia, jak:
    - 42
    - 2 + 2
    - 10 * 10
    - jeżeli słowo "dupa" zawiera "i", to 123, a w przeciwnym wypadku 765
    - długość listy [a, b, c, d, e] *)

(** Najważniejsze termy są nazywane elementami. Dla [nat] są to 0, 1, 2,
    3, 4, 5 i tak dalej. Elementy wyróżnia to, że są w postaci normalnej/
    postaci kanonicznej. Znaczy to intuicyjnie, że są one ostatecznymi wynikami
    obliczeń, np.:
    - obliczenie 42 daje 42
    - obliczenie 2 + 2 daje 4
    - obliczenie 10 * 10 daje 100
    - obliczenie ... daje 765
    - obliczenie długości listy daje 5 *)

(** Czym dokładnie są obliczenia, dowiemy się później. Na razie wystarczy
    nam wiedzieć, że każdy term zamknięty, czyli taki, o którym wiadomo
    wystarczająco dużo, oblicza się do postaci normalnej, np. 5 + 1 oblicza
    się do 6. Jeżeli jednak czegoś nie wiadomo, to term się nie oblicza, np.
    n + 1 nie wiadomo ile wynosi, jeżeli nie wiadomo, co oznacza n.

    Podsumowując, każdy element jest termem, a każdy term oblicza się do
    postaci normalnej, czyli do elementu. *)