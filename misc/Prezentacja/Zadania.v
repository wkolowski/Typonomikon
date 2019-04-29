(** * Zadania *)

(** **** Zadanie 1 *)

(*
    Zdefiniuj typ potencjalnie nieskończonych drzew binarnych trzymających
    wartości typu A w węzłach, jego relację bipodobieństwa, predykaty
    "skończony" i "nieskończony" oraz funkcję mirror, która zwraca
    lustrzane odbicie drzewa. Udowodnij, że bipodobieństwo jest relacją
    równoważności i że funkcja mirror jest inwolucją (tzn. mirror (mirror t)
    jest bipodobne do t), która zachowuje właściwości bycia drzewem
    skończonym/nieskończonym. Pokaż, że drzewo nie może być jednocześnie
    skończone i nieskończone.
*)

(** **** Zadanie 2 *)

(*

    Znajdź taką rodzinę typów koinduktywnych C, że dla dowolnego
    typu A, C A jest w bijekcji z typem funkcji nat -> A. Przez
    bijekcję będziemy tu rozumieć funkcję, która ma odwrotność, z którą
    w obie strony składa się do identyczności.

    Uwaga: nie da się tego udowodnić bez użycia dodatkowych aksjomatów,
    które na szczęście są bardzo oczywiste i same się narzucają.

*)

(** **** Zadanie 3 *)

(*

    Sprawdź, czy dobrze ufundowana jest następująca relacja porządku
    (mam nadzieję, że obrazek jest zrozumiały):
    0 < 1 < ... < ω < ω + 1 < ... < 2 * ω

     Oczywiście najpierw musisz wymyślić, w jaki sposób zdefiniować taką
     relację.

*)

(** **** Zadanie 4 *)

(*

    Niech (B, R) będzie typem wyposażonym w relację dobrze ufundowaną R.
    Zdefiniuj po współrzędnych relację porządku na funkcjach A -> B
    i rozstrzygnij, czy relacja ta jest dobrze ufundowana.

    Uwaga: zadanie jest trochę podchwytliwe.

*)

(** **** Zadanie 5 *)

(*

    Zdefiniuj pojęcie "nieskończonego łańcucha malejącego" (oczywiście
    za pomocą koindukcji) i udowodnij, że jeżeli relacja jest dobrze
    ufundowana, to nie ma nieskończonych łańcuchów malejących.

*)

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

    Następnie przyjmij, że funkcja rotn spełnia swoje równanie
    rekurencyjne (bonus, bardzo trudne: udowodnij, że faktycznie
    tak jest).

    Zdefiniuj relację opisującą wykres funkcji rotn. Pokaż, że
    definicja wykresu jest poprawna i pełna oraz wyprowadź z niej
    regułę indukcji funkcyjnej. Użyj jej, żeby udowodnić, że funkcja
    rotn jest inwolucją dla dowolnego n, tzn. rotn n (rotn n l) = l.

*)

(** **** Zadanie 7 *)

(*

    Zdefiniuj funkcję rotn (i wszystkie funkcje pomocnicze) jeszcze raz,
    tym razem za pomocą komendy Function. Porównaj swoje definicje wykresu
    oraz reguły indukcji z tymi automatycznie wygenerowanymi. Użyj taktyki
    functional induction, żeby jeszcze raz udowodnić, że rotn jest
    inwolucją (i wszystkie lematy też). Policz, ile pisania udało ci się
    dzięki temu zaoszczędzić.

    Czy w twoim rozwiązaniu są lematy, w których użycie indukcji funkcyjnej
    znacznie utrudnia przeprowadzenie dowodu? W moim jest jeden taki.

*)

(** **** Zadanie 8 *)

(*

    Zainstaluj plugin Equations:
    https://github.com/mattam82/Coq-Equations

    Przeczytaj tutorial:
    https://raw.githubusercontent.com/mattam82/Coq-Equations/master/doc/equations_intro.v

    Następnie znajdź jakiś swój dowód przez indukcję, który był skomplikowany
    i napisz prostszy dowód z potem za pomocą komendy [Equations] i taktyki
    [funelim].

    Dobrze byłoby, gdyby nie była to kolejna przeróbka poprzedniego zadania.

*)

(** **** Zadanie bonusowe *)

(*

    Nie ma to wprawdzie żadnego związku z tematem wykładu, ale miło by było
    pamiętać, że Coq to nie jest jakiś tam biedajęzyk programowania, tylko
    pełnoprawny system podstaw matematyki (no, prawie...). W związku z tym
    bonusowe zadanie:

    Pokaż, że nat <> Type.

*)