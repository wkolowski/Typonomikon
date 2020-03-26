# Ściąga - modalności

| modalność     | wymowa | Coq | jaki sposób wyraża |
| --------------| ------ | --- | --------- |
| neutralna     | brak   | `P` | nic specjalnego |
| trywialna     | brak   | `True` | nic ciekawego |
| klasyczna     | klasycznie | `LEM -> P` | logikę klasyczną
| aksjomatyczna | jeżeli aksjomat to zdanie | `A -> P` | logikę z dodatkowym aksjomatem `A`
| wymówkowa     | no chyba że <wymówka> | `E \/ P` | tanią wymówkę
| niezaprzeczalna | niezaprzeczalnie | `~ ~ P` | nie można danego zdania udowodnić wprost, ale nie można go też obalić
| pośrednia     | brak   | `(P -> C) -> C` | `P`, ale w zawoalowany sposób
| bezpośrednia  | brak | `forall C : Prop, (P -> C) -> C` | nic specjalnego - jest równoważna modalności neutralnej
