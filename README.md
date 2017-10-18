# CoqBook

To repozytorium zawiera źródła mojej [książki](https://zeimer.github.io/)

W sumie nie wiem, dlaczego wstawiłem je osobno, zamiast wrzucić do jednego repo razem z książką...

Co tu się dzieje:
- book/ zawiera pliki .v, które stanowią źródła książki
- build.sh i rebuild.sh to skrypty służące odpowiednio do budowania i budowania od nowa książki
- css/ i js/ to style i kod js, który daje książce w miarę znośny wygląd. Ukradzione ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- extra/ zawiera nagłówek i stopkę, które dodają analitiksy i inne takie
- makefile to makefile, a make_makefile.sh generuje nowy makefile od zera
- misc/ to rzeczy, z których będą powstawać przyszłe rozdziały. Póki co jest tu burdl.
- README.md to ten plik

Książkę można skompilować za pomocą polecenia
```bash
./rebuild.sh
```
Polecenie to usuwa wszystkie śmieci typu .vo, .v.d, .glob, holder htmls/, tworzy nowego makefile'a, kompiluje od zera wszystkie pliki .v znajdujące się w book/, generuje pliki .html z komentarzy, dodaje nagłówek i stopkę z extra/ i podmienia style oraz js na właściwe.

## Ogłoszenia parafialne

W tak zwanym międzyczasie trochę zmieniła się moja koncepcja na temat tego, jak ta książka powinna wyglądać. W mojej nowej wizji występują dwa typy rozdziałów:
- rozdziały teoretyczne opisują Coqa, stojące za nim idee, jego podstawy teoretyczne oraz różne quirki związane z jego użytkowaniem. W kluczowych momentach prezentują niewielkie ilości zadań sprawdzających zrozumienie materiału. Będę je numerował (póki co) literą R.
- rozdziały stosowane będą opisywać różne rzeczy z dziedziny informatyki i matematyki, a twoim zadaniem będzie ich implementacja i formalna weryfikacja w Coqu. Będę je numerował literą X.

W dalszej perspektywie powstaną rozdziały stosowane dotyczące różnych, mniej lub bardziej konkretnych rzeczy: konkretnych typów induktywnych (list niepustych, wektorów, drzew, typów używanych w silnych specyfikacjach), struktur danych (stosy, ciągi, drzewa wyszukiwań, kolejki), relacji, porządków etc.

Mam nadzieję, że mój zapał nie będzie słomiany.

## TODO

Bardziej bliskie TODO:
- zapewnić kompatybilność z Coqiem 8.6
- dokończyć podrozdział o regułach komputacji
- dokończyć rozdział o funkcjach (więcej ukrytej teorii kategorii)
- dokończyć rozdział o relacjach

Bardziej dalekie TODO:
- Wygląd:
  - okładka
  - zwijane, rozwijane dowody
- Logika:
  - reflekcja
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
  - Komenda Function
- Indukcja:
  - jak dokładnie działa indukcja
  - proste reguły eliminacji
  - coś o generalizowaniu hipotezy indukcyjnej
  - foldy
  - skomplikowane reguły eliminacji
  - reguły dla Prop
  - reguły dla indukcji wzajemnej
  - reguły dla indukcji dobrze ufundowanej
- Typy:
  - opisać lepiej produkt zależny
  - dodać podrozdział o zależnych typach induktywnych
  - dodać podrozdział o typach induktywnych z nieskończoną ilością argumentów rekurencyjnych (A -> T)
  - o silnych specyfikacjach
- R3: Automatyzacja i taktyki
  - proofsearch (zadania chyba już są w misc/)
  - auto, eauto, intuition, omega etc.
  - przykłady: automatyzacja dowodów o funkcjach boolowskich i relacjach, ale wymyślić też coś innego
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
  - Typ [option]
  - Przerobić ćwiczenia z logiki na rozdział
  - Logika ternarna
  - Listy niepuste (nel)
  - Wektory (vec)
  - Drzewa binarne
  - lensy ? (ho ho, to się nie stanie — bo nie umiem)
- Inne:
  - definiowanie przez dowód
  - być może koindukcja
  - wzbogacanie struktur danych
- Sugestie:
  - być może przesunąć Empty_set i unit za Enumeracje, a prod i sum za Właściwości konstruktorów. Wcisnąć tu ukrytą teorię kategorii.
