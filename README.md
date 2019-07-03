# CoqBook

To repozytorium zawiera źródła mojej [książki](https://zeimer.github.io/CoqBookPL/)

Co tu się dzieje:

- assets/ zawiera style css, pliki js, nagłówek i stopkę dodawane do każdej strony oraz okładkę. Większość z tego jest ukradziona ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- book/ zawiera źródła książki w postaci zakomentowanych plików .v (hipsterzy nazywają to "literate programming").
- build.sh to skrypt budujący ze źródeł wersje HTML i PDF książki.
- code/ to folder roboczy, w którym gromadzę różne fragmenty kodu na przyszły użytek.
- docs/ to folder, z którego książka jest hostowana na GitHub Pages.
- README.md to plik, który właśnie czytasz.
- tex/ to folder, w którym możesz znaleźć wersję PDF książki, ale miej się na baczności, gdyż póki co jest ona upośledzona.
- txt/ zawiera moje notatki i TODO.

Książkę można skompilować za pomocą polecenia
```bash
./build.sh
```

## Ogłoszenia parafialne

Chwilowo książka składa się z następujących 2 typów rozdziałów:
- rozdziały oznaczone literą R opisują Coqa, stojące za nim idee, jego podstawy teoretyczne oraz różne quirki związane z jego użytkowaniem. W kluczowych momentach prezentują niewielkie ilości zadań sprawdzających zrozumienie materiału.
- rozdziały oznaczone literą X opisują (choć to chyba za mocne słowo) różne rzeczy z dziedziny informatyki i matematyki. Zawierają głównie duże ilość zadań, które możesz wykonać.

W dalszej perspektywie powstaną rozdziały stosowane dotyczące różnych, mniej lub bardziej konkretnych rzeczy: konkretnych typów induktywnych (list niepustych, wektorów, drzew, typów używanych w silnych specyfikacjach), struktur danych (stosy, ciągi, drzewa wyszukiwań, kolejki), porządków, struktur algebraicznych, funktorów, monad i innych dziwnych rzeczy, które nie interesują normalnych ludzi. W txt/TODO jest dokładny plan, świeżo wypolerowany.
