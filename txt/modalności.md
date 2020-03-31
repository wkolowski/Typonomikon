# Ściąga - modalności

| modalność     | Coq | wymowa    | jaki sposób wyraża |
| --------------| --- | --------- | ------------------ |
| neutralna     | `P` | `P`       | zwykły, domyślny   |
| trywialna     | `True` | brak   | niezbyt ciekawy    |
| klasyczna     | `LEM -> P` | klasycznie `P` | logikę klasyczną
| aksjomatyczna | `A -> P` | `P` pod warunkiem, że `A` | logikę z dodatkowym aksjomatem `A`
| niezaprzeczalna | `~ ~ P` | niezaprzeczalnie `P` | nie można danego zdania udowodnić wprost, ale nie można go też obalić
| pośrednia     | `(P -> C) -> C` | `C`, o ile wynika z `P` | zawoalowany
| bezpośrednia  | `forall C : Prop, (P -> C) -> C` | zachodzą wszystkie konsekwencje `P` | nic specjalnego - jest równoważna modalności neutralnej
