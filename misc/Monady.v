

(*
    - Monady jako sposoby bycia:
      - [Id] nie reprezentuje żadnego efektu. Wartości typu [Id A] są w ten
        sposób, że po prostu są.
      - [option] reprezentuje częściowość. Wartości typu [option A] są w ten
        sposób, że albo są, albo ich nie ma
      - [sum E] reprezentuje możliwość wystąpienia błędu. Wartości typu
        [sum E A] są w ten sposób, że albo są poprawne, albo ich nie ma, gdyż
        wystąpił błąd typu [E].
      - [list] reprezentuje niedeterminizm (uporządkowany). Wartości typu
        [list A] są w ten sposób, że może ich być wiele lub może ich nie być
        wcale i są w sposób uporządkowany.
      - [State S] reprezentuje stan. Wartości typu [State S A] są w ten
        sposób, że są i mają pamięć, tzn. mogą się zmieniać w zależności
        od stanu.
      - [Reader R] reprezentuje możliwość odczytania konfiguracji.
      - [Writer W] reprezentuje możliwość zapisywania logów.
      - [Future] reprezentuję asynchroniczność. Wartości typu [Future A]
        są w ten sposób, że albo są teraz, albo będą później.
      - [STM] reprezentuje tranzakcje. Wartościu typu [STM A] są w ten
        sposób, że są w jednym kawałku, są tranzakcjami.
      - [SQL] reprezentuje operacje bazodanowe. Wartości typu [SQL A] są
        w ten sposób, że są w bazie danych.
*)