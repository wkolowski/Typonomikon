# Aksjomaty logiki klasycznej

## Bardziej oczywiste

| Nazwa                           | Skrót    | Definicja                               | Skutek |
| ------------------------------- | -------- | --------------------------------------- | ------ |
| Prawo wyłączonego środka        | `LEM`    | `P \/ ~ P`                              | wszystko wiadomo z góry <br> złamane prawo zachowania informacji |
| Eliminacja podwójnej negacji    | `DNE`    | `~ ~ P -> P`                            | dowodząc dysjunkcji można się rozmyślić i pójść w inną stronę niż początkowo |
| Consequentia mirabilis          | `CM`     | `(~ P -> P) -> P`                       | można dowodzić nie wprost       |
| Prawo Peirce'a                  | `Peirce` | `((P -> Q) -> P) -> P`                  | ???    |

## Mniej oczywiste - oparte o ideę silnych i słabych spójników"

| Rodzaj | Spójnik                         | Definicja              | Prawo                      | Nazwa            |
| ------ | ------------------------------- | ---------------------- | -------------------------- | ---------------- |
| Silna  | Implikacja                      | `~ P \/ Q`             | `(P -> Q) -> ~ P \/ Q`     | Prawo implikacji materialnej |
| Słaba  | Implikacja                      | `~ Q -> ~ P`           | `(~ Q -> ~ P) -> (P -> Q)` | Prawo kontrapozycji |
| Słaba  | Dysjunkcja                      | `~ P -> Q`             | `(~ P -> Q) -> P \/ Q`     | ???              |
| Słaba  | Koniunkcja                      | `~ (~ P \/ ~ Q)`       | `~ (~ P \/ ~ Q) -> P /\ Q` |                  |
| Silna  | Równoważność                    | `P /\ Q \/ ~ P /\ ~ Q` | `(P <-> Q) -> (P /\ Q \/ ~ P /\ ~ Q)` | Prawo równoważności materialnej |
| Silna  | Antyimplikacja                  | `P /\ ~ Q`             | `~ (P -> Q) -> (P /\ ~ Q)` |                  |
| Słaby  | xor                             | `~ (P <-> Q)`          | `~ (P <-> Q) -> xor P Q`   |                  |