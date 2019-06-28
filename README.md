# CoqBook

To repozytorium zawiera źródła mojej [książki](https://zeimer.github.io/).

W sumie nie wiem, dlaczego wstawiłem je osobno, zamiast wrzucić do jednego repo razem z książką...

Co tu się dzieje:
- book/ zawiera pliki .v, które stanowią źródła książki.
- css/ i js/ to style i kod js, które dają książce w miarę znośny wygląd. Ukradzione ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- extra/ zawiera nagłówek i stopkę, które dodają analitiksy i inne takie, a także okładkę, również ukradzioną z Software Foundations.
- todo/ to folder roboczy, w którym gromadzą się różne rzeczy: notatki, fragmenty kodu na przyszłość, śmieci, etc. Update 2019-6-28: świeżo po refaktoringu, więc jest tu jako taki porządeczek.
- build.sh i rebuild.sh to skrypty służące odpowiednio do budowania i budowania od nowa książki. make_makefile.sh generuje nowy makefile od zera.

Książkę można skompilować za pomocą polecenia
```bash
./rebuild.sh
```
Polecenie to usuwa wszystkie śmieci typu .vo, .v.d, .glob, folder htmls/, tworzy nowego makefile'a, kompiluje od zera wszystkie pliki .v znajdujące się w book/ i todo/, generuje pliki .html z komentarzy, dodaje nagłówek, stopkę i okładkę z extra/ i podmienia style oraz js na właściwe.

## Ogłoszenia parafialne

Chwilowo książka składa się z następujących 3 typów rozdziałów:
- rozdziały oznaczone literą R opisują Coqa, stojące za nim idee, jego podstawy teoretyczne oraz różne quirki związane z jego użytkowaniem. W kluczowych momentach prezentują niewielkie ilości zadań sprawdzających zrozumienie materiału.
- rozdziały oznaczone literą X opisują (choć to chyba za mocne słowo) różne rzeczy z dziedziny informatyki i matematyki. Zawierają głównie duże ilość zadań, które możesz wykonać.
- jest też jeden rozdział po angielsku (Seminar: Induction). Są to moje notatki z seminarium. Kiedyś może przetłumaczę na polski (ale prędzej przetłumaczę wszystko inne na angielski).

W dalszej perspektywie powstaną rozdziały stosowane dotyczące różnych, mniej lub bardziej konkretnych rzeczy: konkretnych typów induktywnych (list niepustych, wektorów, drzew, typów używanych w silnych specyfikacjach), struktur danych (stosy, ciągi, drzewa wyszukiwań, kolejki), porządków, struktur algebraicznych, funktorów, monad i innych dziwnych rzeczy, które nie interesują normalnych ludzi.
