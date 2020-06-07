# CoqBook

To repozytorium zawiera moją [książkę](https://wkolowski.github.io/CoqBookPL/) o programowaniu funkcyjnym, logice konstruktywnej, formalizacji matematyki i innych takich (razem ze źródłami). Dostępna jest też [wersja PDF](https://github.com/wkolowski/CoqBookPL/raw/master/tex/Ksi%C4%85%C5%BCka.pdf), ale nie polecam, bo jest mało dopracowana i niektóre rzeczy źle się wyświetlają.

Co tu się dzieje:
- assets/ zawiera style css, pliki js, nagłówek i stopkę dodawane do każdej strony oraz materiały do zrobienia okładek. Większość z tego jest ukradziona ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- book/ zawiera źródła książki w postaci zakomentowanych plików .v (hipsterzy nazywają to "literate programming", a jako że w Coqu mamy nie tylko programowanie, ale i dowodzenie, to nawet "literate proofgramming").
- build.sh to skrypt budujący ze źródeł wersje HTML i PDF książki.
- code/ to folder roboczy, w którym gromadzę różne fragmenty kodu na przyszły użytek.
- docs/ to folder, z którego książka jest hostowana na GitHub Pages.
- README.md to plik, który właśnie czytasz.
- tex/ to folder, w którym możesz znaleźć wersję PDF książki (oraz okładkę), ale miej się na baczności, gdyż póki co jest ona upośledzona.
- txt/ zawiera różne notatki, w tym spis rzeczy TODO i plan co robić dalej.

Książkę można zbudować za pomocą polecenia
```bash
./build.sh
```