# CoqBook

To repozytorium zawiera źródła mojej [książki](https://zeimer.github.io/CoqBookPL/)

Co tu się dzieje:

- assets/ zawiera style css, pliki js, nagłówek i stopkę dodawane do każdej strony oraz materiały do zrobienia okładek. Większość z tego jest ukradziona ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- book/ zawiera źródła książki w postaci zakomentowanych plików .v (hipsterzy nazywają to "literate programming").
- build.sh to skrypt budujący ze źródeł wersje HTML i PDF książki.
- code/ to folder roboczy, w którym gromadzę różne fragmenty kodu na przyszły użytek.
- docs/ to folder, z którego książka jest hostowana na GitHub Pages.
- README.md to plik, który właśnie czytasz.
- tex/ to folder, w którym możesz znaleźć wersję PDF książki (oraz okładkę), ale miej się na baczności, gdyż póki co jest ona upośledzona.
- txt/ zawiera moje notatki i TODO.

Książkę można skompilować za pomocą polecenia
```bash
./build.sh
```

## Ogłoszenia parafialne

Po najnowszym refaktoringu w książce widać wszystkie planowane (na chwilę obecną) rozdziały. Niektóre z nich oznaczone są jako puste - nic tam nie ma. Inne mogą być oznaczone jako TODO - jest tam coś, ale być może nie wkomponowuje się to dobrze w liniową kolejność rozdziałów (obecnie dotyczy to szczególnie rozdziału C o podstawach teorii typów).

W dalszej perspektywie powstaną rozdziały stosowane dotyczące różnych, mniej lub bardziej konkretnych rzeczy: konkretnych typów induktywnych (list niepustych, wektorów, drzew, typów używanych w silnych specyfikacjach), struktur danych (stosy, ciągi, drzewa wyszukiwań, kolejki), porządków, struktur algebraicznych, funktorów, monad i innych dziwnych rzeczy, które nie interesują normalnych ludzi. W txt/TODO jest dokładny plan, świeżo wypolerowany.
