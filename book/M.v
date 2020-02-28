(** * M: Porządki i topologia *)

(** Najpierw nawiązanie do tego co było o relacjach i jakieś intuicje
    o porządkach. Potem trochę porządkologii i może jakieś dziedziny.
    Potem topologia. *)

(** * Legalna topologia *)

(** Tutaj o topologii takiej jak robi Martin Escardó, np. w tej pracy:
    "Infinite sets that satisfy the principle of omniscience in any
    variety of constructive mathematics", czyli odkrywamy, że klasycznie
    [nat] i [conat] są izomorficzne, ale [conat] jest konstruktywnie
    przeszukiwalne, zaś [nat] nie. Wszystko dzieje się w legalnym Coqu,
    z włączonym guard checkerem i bez żadnych homotopii. *)

(** * Nielegalna topologia *)

(** Tutaj o topologii takiej jak robi Martin Escardó głównie w tej
    książce: "Synthetic topology of data types and classical spaces",
    czyli wyłączamy guard checker i patrzymy jakie programy zatrzymują
    się, a jakie nie. *)