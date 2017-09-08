# CoqBook

To repozytorium zawiera źródła mojej [książki](https://zeimer.github.io/)

Co tu się dzieje:
- css/ i js/ to style i kod js, który daje książce w miarę znośny wygląd. Ukradzione ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- book/ zawiera pliki .v, które stanowią źródła książki
- misc/ to rzeczy, z których będą powstawać przyszłe rozdziały
- HEAD_PREPEND robi porządek z nagłówkiem każdego rozdziału i dodaje analitiksy

Książkę można skompilować za pomocą polecenia
```bash
./compile.sh
```

Polecenie to kompiluje od zera wszystkie pliki .v znajdujące się w book/, generuje pliki .html z komentarzy i podmienia style oraz js na właściwe.

## Ogłoszenia parafialne

W tak zwanym międzyczasie trochę zmieniła się moja koncepcja na temat tego, jak ta książka powinna wyglądać. W mojej nowej wizji występują dwa typy rozdziałów:
- rozdziały teoretyczne opisują Coqa, stojące za nim idee, jego podstawy
  teoretyczne oraz różne quirki związane z jego użytkowaniem. W kluczowych
  momentach prezentują niewielkie ilości zadań sprawdzających zrozumienie
  materiału. Będę je numerował (póki co) literą R.
- rozdziały stosowane będą opisywać różne rzeczy z dziedziny informatyki
  i matematyki, a twoim zadaniem będzie ich implementacja i formalna
  weryfikacja w Coqu. Będę je numerował literą X.

W dalszej perspektywie powstaną rozdziały stosowane dotyczące różnych, mniej
    lub bardziej konkretnych rzeczy: konkretnych typów induktywnych (list
    niepustych, wektorów, drzew, typów używanych w silnych specyfikacjach),
    struktur danych (stosy, ciągi, drzewa wyszukiwań, kolejki), relacji,
    porządków etc.

    Mam nadzieję, że mój zapał nie będzie słomiany.

    Zaczynam coś czuć, że nowy podział rozdziałów na _R_ i _X_ może się nie udać. *)

(** Bardziej bliskie TODO: dokończyć podrozdział o regułach komputacji *)

(** Bardziej odległe TODO:
    - Wygląd:
      - okładka
      - zwijane, rozwijane dowody

    - Logika:
      - reflekcja
      - różne alternatywne definicje równości (np. [JMeq], [eq_dep])
      - aksjomaty

    - Rekursja:
      - rekursja strukturalna
      - rekursja "monotoniczna" (fix w fiksie)
      - rekursja ogonowa
      - rekursja "po paliwie"
      - rekursja przez iterację
      - Bove-Capretta
      - rekursja dobrze ufundowana
      - [Function]

    - Indukcja:
      - jak dokładnie działa indukcja
      - proste reguły eliminacji
      - coś o generalizowaniu hipotezy indukcyjnej
      - foldy
      - skomplikowane reguły eliminacji
      - reguły dla [Prop]
      - reguły dla indukcji wzajemnej
      - reguły dla indukcji dobrze ufundowanej

    - Typy:
      - opisać lepiej produkt zależny
      - dodać podrozdział o zależnych typach induktywnych
      - dodać podrozdział o typach induktywnych z nieskończoną
        ilością argumentów rekurencyjnych (A -> T)
      - o silnych specyfikacjach

    - R3: Automatyzacja i taktyki
      - proofsearch (zadania chyba już są)
      - auto, eauto, intuition, omega etc.
      - przykłady: funkcje boolowskie

    - R4: Matematyka
      - teoria funkcji (injekcje, surjekcje, bijekcje, idempotencja,
   # CoqBook

To repozytorium zawiera źródła mojej [książki](https://zeimer.github.io/)

Co tu się dzieje:
- css/ i js/ to style i kod js, który daje książce w miarę znośny wygląd. Ukradzione ze starej wersji [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- book/ zawiera pliki .v, które stanowią źródła książki
- misc/ to rzeczy, z których będą powstawać przyszłe rozdziały
- HEAD_PREPEND robi porządek z nagłówkiem każdego rozdziału i dodaje analitiksy

Książkę można skompilować za pomocą polecenia
```bash
./compile.sh
```

Polecenie to kompiluje od zera wszystkie pliki .v znajdujące się w book/, generuje pliki .html z komentarzy i podmienia style oraz js na właściwe.

## Ogłoszenia parafialne

W tak zwanym międzyczasie trochę zmieniła się moja koncepcja na temat tego, jak ta książka powinna wyglądać. W mojej nowej wizji występują dwa typy rozdziałów:
- rozdziały teoretyczne opisują Coqa, stojące za nim idee, jego podstawy teoretyczne oraz różne quirki związane z jego użytkowaniem. W kluczowych momentach prezentują niewielkie ilości zadań sprawdzających zrozumienie materiału. Będę je numerował (póki co) literą R.
- rozdziały stosowane będą opisywać różne rzeczy z dziedziny informatyki i matematyki, a twoim zadaniem będzie ich implementacja i formalna weryfikacja w Coqu. Będę je numerował literą X.
- 
W dalszej perspektywie powstaną rozdziały stosowane dotyczące różnych, mniej lub bardziej konkretnych rzeczy: konkretnych typów induktywnych (list niepustych, wektorów, drzew, typów używanych w silnych specyfikacjach), struktur danych (stosy, ciągi, drzewa wyszukiwań, kolejki), relacji, porządków etc.

Mam nadzieję, że mój zapał nie będzie słomiany.

Zaczynam coś czuć, że nowy podział rozdziałów na _R_ i _X_ może się nie udać. *)

## TODO
Bardziej bliskie TODO:
- dokończyć podrozdział o regułach komputacji
- zapewnić kompatybilność z Coqiem 8.6
- zmienić skrypt kompilujący na skrypty build i rebuild *)

Bardziej odległe TODO:
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
  - [Function]
- Indukcja:
  - jak dokładnie działa indukcja
  - proste reguły eliminacji
  - coś o generalizowaniu hipotezy indukcyjnej
  - foldy
  - skomplikowane reguły eliminacji
  - reguły dla [Prop]
  - reguły dla indukcji wzajemnej
  - reguły dla indukcji dobrze ufundowanej
- Typy:
  - opisać lepiej produkt zależny
  - dodać podrozdział o zależnych typach induktywnych
  - dodać podrozdział o typach induktywnych z nieskończoną ilością argumentów rekurencyjnych (A -> T)
  - o silnych specyfikacjach
- R3: Automatyzacja i taktyki
  - proofsearch (zadania chyba już są)
  - auto, eauto, intuition, omega etc.
  - przykłady: funkcje boolowskie
- R4: Matematyka
  - teoria funkcji (injekcje, surjekcje, bijekcje, idempotencja, inwolucje etc.) — zadania zaczęte
  - teoria relacji (relacje zwrotne, przechodnie, symetryczne, antyzwrotne, antysymetryczne, asymetryczne, koprzechodnie, porządki, relacje równoważności, domknięcie zwrotne, domknięcie tranzytywne, domknięcie równoważnościowe etc.)
  - setoidy
  - częściowe porządki/teoria krat
  - monoidy/teoria grup
- R5: Funktory i monady
  - Funktory: przykłady na option i list, zadania na tree, state
  - Funktory aplikatywne
  - Monady
  - Alternative
  - MonadPlus
- R6: Teoria Kategorii — ho ho, pieśń przyszłości!
- Zadania TODO:
  - Zrób zadania z definiowania induktywnych typów i predykatów
- Kontent:
  - Przerobić _X1_ na rozdział o arytmetyce Peano.
  - Arytmetyka binarna (liczby naturalne, dodatnie i całkowite)
  - Typ [option]
  - Przerobić ćwiczenia z logiki na rozdział
  - Logika ternarna
  - Listy niepuste (nel)
  - Wektory (vec)
  - Drzewa binarne
  - lensy ? (ho ho, to się nie stanie)
- Inne:
  - definiowanie przez dowód
  - być może koindukcja
  - wzbogacanie struktur danych
- Sugestie:
  - być może przesunąć Empty_set i unit za Enumeracje, a prod i sum za Właściwości konstruktorów *)

## Najnowsze zmiany:

6.09.2017 — rozpoczęty rozdział o złożoności obliczeniowej
8.09.2017 — źródła wrzucone na githuba. Nowe, czytelne README.
