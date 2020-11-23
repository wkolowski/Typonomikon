# Indukcja vs koindukcja

| Cecha               | Indukcja             | Koindukcja                |
| ------------------- | -------------------- | ------------------------- |
| suma/produkt?       | suma produktów       | produkt sum               |
| podstawowa czynność | konstrukcja          | dekonstrukcja             |
| wysokość drzew      | koniecznie skończona | potencjalnie nieskończona |
| szerokość drzew     | dowolna              | dowolna                   |
| ewaluacja           | potencjalnie gorliwa | koniecznie leniwa         |
| definiujemy funkcje | z induktywną dziedziną <br> `I -> X` | z koinduktywną przeciwdziedziną <br> `X -> C` |
| każdy krok          | pomniejsza argument  | powiększa wynik           |

# Indukcja

1. Nazwana suma (niezależna) produktów (zależnych).
2. Typy pozytywne - zdeterminowane przez konstruktory.
3. Byty skończone - nie da się w skończonym czasie zbudować czegoś nieskończonego
4. Ewaluacja gorliwa - robimy, bo możemy
5. Wystąpienia rekurencyjne w definicjach typów ind. muszą być ściśle pozytywne.
6. Rekursja strukturalna pozwala definiować funkcje o typach I -> X
7. Wywołania rekurencyjne zmniejszają argument główny, co zapewnia terminację.
8. Indukcja strukturalna: funkcje o typach forall i : I, P i

# Koindukcja
1. Nazwany produkt (zależny) sum (zależnych).
2. Typy negatywne - zdeterminowane przez dekonstruktory.
3. Byty potencjalnie nieskończone - można w skończonym czasie opisać sposób dekonstrukcji nieskończonej struktury.
4. Ewaluacja leniwa - robimy, bo musimy.
5. Wystąpienia korekurencyjne w definicjach typów ind. muszą być ściśle pozytywne.
6. Korekursja strukturalna pozwala definiować funkcje o typach X -> C
7. Wywołania korekurencyjne muszą powiększać wynik, czyli muszą być produktywne.
8. Koindukcja strukturalna: nie ma w Coqu, ale jej odpowiednikiem jest najprawdopodobniej bipodobieństwo = równość (patrz prace chyba Setzera).