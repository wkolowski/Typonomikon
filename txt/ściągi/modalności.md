# Ściąga - modalności

| modalność       | Coq                                    | wymowa                              | jaki sposób wyraża
| --------------- | -------------------------------------- | ----------------------------------- | ------------------
| neutralna       | `P`                                    | `P`                                 | zwykły, domyślny   
| trywialna       | `True`                                 | brak                                | niezbyt ciekawy    
| wymówkowa       | `E \/ P`                               | `P`, no chyba że `E`                | tanią wymówkę      
| klasyczna       | `LEM -> P`                             | klasycznie `P`                      | logikę klasyczną
| aksjomatyczna   | `A -> P`                               | `P`, pod warunkiem że `A`           | logikę z dodatkowym aksjomatem `A`
| niezaprzeczalna | `~ ~ P` <br> `(P -> False) -> False`   | niezaprzeczalnie `P`                | nie można danego zdania udowodnić wprost, ale nie można go też obalić
| pośrednia       | `(P -> C) -> C`                        | `C`, o ile wynika z `P`             | zawoalowany
| wszechpośrednia | `forall C : Prop, (P -> C) -> C`       | zachodzą wszystkie konsekwencje `P` | Z jednej strony, nic specjalnego - jest równoważna modalności neutralnej. Z drugiej strony - wyraża ona pewną formę ekstensjonalności.