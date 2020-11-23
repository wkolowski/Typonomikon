# Przydatne Coqowe komendy

| Komenda              | Opis            |
| -------------------- | --------------- |
| `Check t.`           | Wyświetl typ termu `t`. |
| `Print t.`           | Wyświetl definicję termu `t`. |
| `Search t1 ... tn.`  | Znajdź wszystkie definicje/twierdzenia, w których typie występują `t1`, ..., `tn`. |
| `Search "str".`      | Znajdź wszystkie definicje/twierdzenia, w których nazwie występuje ciąg znaków "str". |
| `Locate "notacja".`  | Znajdź nazwę definicji, dla której notacją jest `notacja`. |
| `Section nazwa.`     | Otwórz sekcję o podanej nazwie. Przydatne, gdy w wielu definicjach i twierdzeniach musimy powtarzać ciągle te same arguemnty. |
| `Module nazwa.`      | Otwórz moduł o podanej nazwie. Trochę podobne do `Section`. |
| `End nazwa.`         | Zamknij sekcję/moduł o podanej nazwie. |
| `Require nazwa.`     | Załaduj moduł o nazwie `nazwa`. |
| `Import nazwa.`      | Zaimportuj moduł o nazwie `nazwa`. Teraz do rzeczy z modułu można się odnosić bez pisania nazwy modułu na początku (`x` zamiast `nazwa.x`). |
| `Require Import nazwa.` | Połączenie `Require` i `Import`. |
| `Axiom t : A.`       | Przyjmij aksjomat o nazwie `t`, który jest elementem typu `A`. |
| `Axioms (t1 : A1) ... (tn : An).` | Przyjmij dużo aksjomatów na raz. |
| `Variable t : A`.    | Działa podobnie jak `Axiom`, ale jeżeli użyto wewnątrz sekcji, to po zamknięciu sekcji `t : A` zmieni się w argument wszystkich twierdzeń i definicji w tej sekcji. |
| `Variables (t1 : A1) ... (tn : An).` | Dużo `Variable` na raz. |
| `Hypothesis t : A.`  | W sumie to samo co `Variable` |
| `Hypotheses (t1 : A1) ... (tn : An).` | Dużo `Hypothesis` na raz. |

Więcej szczegółów w odpowiednim rozdziale [manuala](https://coq.inria.fr/refman/coq-cmdindex.html).