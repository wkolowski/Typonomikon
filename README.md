# CoqBook

To repozytorium zawiera źródła mojej [książki](https://zeimer.github.io/).

W sumie nie wiem, dlaczego wstawiłem je osobno, zamiast wrzucić do jednego repo razem z książką...

Co tu się dzieje:
- book/ zawiera pliki .v, które stanowią źródła książki.
- css/ i js/ to style i kod js, które dają książce w miarę znośny wygląd. Ukradzione ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- extra/ zawiera nagłówek i stopkę, które dodają analitiksy i inne takie, a także okładkę, również ukradzioną z Software Foundations.
- misc/ zawiera pliki .v o niskim priorytecie z jakimiś kodami, z których może kiedyś coś będzie.
- sig/ zawiera pliki .v z sygnaturami operacji na niektórych typach, które chcę opisać (trzeba przyznać, że ostatnimi czasy projekt skręcił w kierunku ulepszania biblioteki standardowej)
- teksty/ to nieco bardziej składne notatki
- todo/ zawiera pliki .v o wysokim priorytecie. Będą z nich powstawać przyszłe rozdziały i ogólnie przyszły kontent.
- wd/ to folder do biężącej pracy nad rzeczami, które mają być niewidzialne
- build.sh i rebuild.sh to skrypty służące odpowiednio do budowania i budowania od nowa książki. make_makefile.sh generuje nowy makefile od zera.

Książkę można skompilować za pomocą polecenia
```bash
./rebuild.sh
```
Polecenie to usuwa wszystkie śmieci typu .vo, .v.d, .glob, folder htmls/, tworzy nowego makefile'a, kompiluje od zera wszystkie pliki .v znajdujące się w book/ i wd/, generuje pliki .html z komentarzy, dodaje nagłówek, stopkę i okładkę z extra/ i podmienia style oraz js na właściwe.

## Ogłoszenia parafialne

Chwilowo książka składa się z następujących 3 typów rozdziałów:
- rozdziały oznaczone literą R opisują Coqa, stojące za nim idee, jego podstawy teoretyczne oraz różne quirki związane z jego użytkowaniem. W kluczowych momentach prezentują niewielkie ilości zadań sprawdzających zrozumienie materiału.
- rozdziały oznaczone literą X opisują (choć to chyba za mocne słowo) różne rzeczy z dziedziny informatyki i matematyki. Zawierają głównie duże ilość zadań, które możesz wykonać.
- jest też jeden rozdział po angielsku (Seminar: Induction). Są to moje notatki z seminarium. Kiedyś może przetłumaczę na polski (ale prędzej przetłumaczę wszystko inne na angielski).

W dalszej perspektywie powstaną rozdziały stosowane dotyczące różnych, mniej lub bardziej konkretnych rzeczy: konkretnych typów induktywnych (list niepustych, wektorów, drzew, typów używanych w silnych specyfikacjach), struktur danych (stosy, ciągi, drzewa wyszukiwań, kolejki), porządków, struktur algebraicznych, funktorów, monad i innych dziwnych rzeczy, które nie interesują normalnych ludzi.

## TODO

Najbliższe TODO:
- listy

Bliskie TODO:
- R4: spis taktyk (już się robi)
- R5: reflekcja

Średnie TODO:
- dokończyć rozdział o funkcjach (więcej ukrytej teorii kategorii)
- dokończyć rozdział o relacjach
- opisać foldy dla list
Dalekie TODO:
- Wygląd:
  - zwijane, rozwijane dowody
- Logika:
  - różne alternatywne definicje równości (np. JMeq, eq_dep)
  - aksjomaty
- Rekursja:
  - rekursja strukturalna
  - rekursja ogonowa
  - rekursja polimorficzna
  - rekursja "monotoniczna" (fix w fiksie)
  - rekursja "po paliwie"
  - rekursja dobrze ufundowana
  - Bove-Capretta
  - rekursja przez iterację
- Indukcja:
  - foldy
  - reguły dla indukcji dobrze ufundowanej
- Typy:
  - opisać lepiej produkt zależny
  - dodać podrozdział o zależnych typach induktywnych
  - dodać podrozdział o typach induktywnych z nieskończoną ilością argumentów rekurencyjnych (A -> T)
  - o silnych specyfikacjach
- R ileś tam: Matematyka
  - setoidy
  - częściowe porządki/teoria krat
  - monoidy/teoria grup
- R ileś tam + 1: przegląd Haskellowego podwórka. Jeżeli nie możesz się doczekać, patrz [tu](https://github.com/Zeimer/HSLib)
- R6: Teoria Kategorii — ho ho, pieśń przyszłości! Achtung: przemycać tego jak najwięcej.
- Zadania TODO:
  - Zrób zadania z definiowania induktywnych typów i predykatów
- Inne:
  - definiowanie przez dowód
- Sugestie:
  - być może przesunąć Empty_set i unit za Enumeracje, a prod i sum za Właściwości konstruktorów. Wcisnąć tu ukrytą teorię kategorii.
