# CoqBook

To repozytorium zawiera źródła mojej [książki](https://zeimer.github.io/)

W sumie nie wiem, dlaczego wstawiłem je osobno, zamiast wrzucić do jednego repo razem z książką...

Co tu się dzieje:
- book/ zawiera pliki .v, które stanowią źródła książki. Źródła jednego rozdziału (Seminar: Induction) nie są dostępne.
- build.sh i rebuild.sh to skrypty służące odpowiednio do budowania i budowania od nowa książki.
- css/ i js/ to style i kod js, które dają książce w miarę znośny wygląd. Ukradzione ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- extra/ zawiera nagłówek i stopkę, które dodają analitiksy i inne takie, a także okładkę, również ukradzioną z Software Foundations.
- make_makefile.sh generuje nowy makefile od zera.
- trash/ zawiera fragmenty rozdziałów, które zostały wycięte albo skopiowane na zapas z jakichś dziwnych powodów (np. refaktoringu).
- todo/ zawiera pliki .v o wysokim priorytecie, z których będą powstawać przyszłe rozdziały.
- misc/ zawier pliki .v o niskim priorytecie z jakimiś kodami, z których może kiedyś coś będzie. 10.11.17 udało mi się tu posprzątać, więc powinien być w miarę porządek.
- README.md to ten plik

Książkę można skompilować za pomocą polecenia
```bash
./rebuild.sh
```
Polecenie to usuwa wszystkie śmieci typu .vo, .v.d, .glob, folder htmls/, tworzy nowego makefile'a, kompiluje od zera wszystkie pliki .v znajdujące się w book/, generuje pliki .html z komentarzy, dodaje nagłówek, stopkę i okładkę z extra/ i podmienia style oraz js na właściwe.

## Ogłoszenia parafialne

Chwilowo książka składa się z następujących 3 typów rozdziałów:
- rozdziały oznaczone literą R opisują Coqa, stojące za nim idee, jego podstawy teoretyczne oraz różne quirki związane z jego użytkowaniem. W kluczowych momentach prezentują niewielkie ilości zadań sprawdzających zrozumienie materiału.
- rozdziały oznaczone literą X opisują (choć to chyba za mocne słowo) różne rzeczy z dziedziny informatyki i matematyki. Zawierają głównie duże ilość zadań, które możesz wykonać.
- jest też jeden rozdział po angielsku (Seminar: Induction). Są to moje notatki z seminarium. Kiedyś może przetłumaczę na polski (ale prędzej przetłumaczę wszystko inne na angielski).

W dalszej perspektywie powstaną rozdziały stosowane dotyczące różnych, mniej lub bardziej konkretnych rzeczy: konkretnych typów induktywnych (list niepustych, wektorów, drzew, typów używanych w silnych specyfikacjach), struktur danych (stosy, ciągi, drzewa wyszukiwań, kolejki), porządków, struktur algebraicznych, funktorów, monad i innych dziwnych rzeczy, które nie interesują normalnych ludzi.

## TODO

Bliskie TODO:
- taktyki (już się robią)
- reflekcja (niestety po angielsku)

Średnie TODO:
- dokończyć rozdział o funkcjach (więcej ukrytej teorii kategorii)
- dokończyć rozdział o relacjach

Dalekie TODO:
- Wygląd:
  - zwijane, rozwijane dowody
- Logika:
  - porządna reflekcja
  - różne alternatywne definicje równości (np. JMeq, eq_dep)
  - aksjomaty
- Rekursja:
  - rekursja strukturalna
  - rekursja "monotoniczna" (fix w fiksie)
  - rekursja ogonowa
  - rekursja "po paliwie"
  - rekursja przez iterację
  - Bove-Capretta
  - rekursja dobrze ufundowana
- Indukcja:
  - foldy
  - reguły dla indukcji dobrze ufundowanej
- Typy:
  - opisać lepiej produkt zależny
  - dodać podrozdział o zależnych typach induktywnych
  - dodać podrozdział o typach induktywnych z nieskończoną ilością argumentów rekurencyjnych (A -> T)
  - o silnych specyfikacjach
- R4: Matematyka
  - setoidy
  - częściowe porządki/teoria krat
  - monoidy/teoria grup
- R5: Funktory i monady
  - Funktory: przykłady na option i list, zadania na tree, state, reader, writer
  - Funktory aplikatywne
  - Monady
  - Alternative
  - MonadPlus
- R6: Teoria Kategorii — ho ho, pieśń przyszłości! Achtung: przemycać tego jak najwięcej.
- Zadania TODO:
  - Zrób zadania z definiowania induktywnych typów i predykatów
- Kontent:
  - Arytmetyka binarna (liczby naturalne, dodatnie i całkowite)
  - Typ option
  - Przerobić ćwiczenia z logiki na rozdział
  - Logika ternarna
  - Listy niepuste (nel)
  - Wektory (vec)
  - Drzewa binarne
- Inne:
  - definiowanie przez dowód
  - być może koindukcja (a może lepiej nie...)
  - wzbogacanie struktur danych
- Sugestie:
  - być może przesunąć Empty_set i unit za Enumeracje, a prod i sum za Właściwości konstruktorów. Wcisnąć tu ukrytą teorię kategorii.
