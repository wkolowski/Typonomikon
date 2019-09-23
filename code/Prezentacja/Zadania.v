(** * Zadania *)


(** **** Zadanie 6 *)

(*

    Zdefiniuj na listach porządek według długości i pokaż, że jest on
    dobrze ufundowany.

    Zdefiniuj przez rekursję dobrze ufundowaną funkcję rotn, która
    bierze liczbę n oraz listę i zwraca listę, w której bloki o
    długości dokładnie [n + 1] zostały odwrócone, np.
    rotn 0 [1; 2; 3; 4; 5; 6; 7] = [1; 2; 3; 4; 5; 6; 7]
    rotn 1 [1; 2; 3; 4; 5; 6; 7] = [2; 1; 4; 3; 6; 5; 7]
    rotn 2 [1; 2; 3; 4; 5; 6; 7] = [3; 2; 1; 6; 5; 4; 7]

    Wskazówka: zdefiniuj funkcją pomocniczą split, która dzieli listę
    na blok odpowiedniej długości i resztę listy.

    Następnie przyjmij, że funkcja [rotn] spełnia swoje równanie
    rekurencyjne (bonus, bardzo trudne: udowodnij, że faktycznie
    tak jest).

    Zdefiniuj relację opisującą wykres funkcji rotn. Pokaż, że
    definicja wykresu jest poprawna i pełna oraz wyprowadź z niej
    regułę indukcji funkcyjnej. Użyj jej, żeby udowodnić, że funkcja
    rotn jest inwolucją dla dowolnego n, tzn. rotn n (rotn n l) = l.

*)