

(** * Logika klasyczna jako logika diabła *)

(** Dawno dawno temu w odległej galaktyce, a konkretniej w ZSRR, był
    sobie pewien rusek. Pewnego razu do ruska przyszedł diaboł (a to,
    jak wiadomo, coś dużo gorszego niż diabeł) i zaoferował mu taki
    dil: "dam ci miliard dolarów albo jeżeli dasz mi miliard dolarów,
    to spełnię dowolne twoje życzenie".

    Rusek trochę skonsternowany, nie bardzo widzi mu się podpisywanie
    cyrografu krwią. "Nie nie, żadnych cyrografów, ani innych takich
    kruczków prawnych", zapewnia go diaboł. Rusek myśli sobie tak:
    "pewnie hajsu nie dostanę, ale przecież nic nie tracę", a mówi:
    "No dobra, bierę".

    "Świetnie!" - mówi diaboł - "Jeżeli dasz mi miliard dolarów, to
    spełnie dowolne twoje życzenie". Cóż, rusek był zawiedziony, ale
    nie zaskoczony - przecież dokładnie tego się spodziewał. Niedługo
    później diaboł zniknął, a rusek wrócił do pracy w kołchozie.

    Jako, że był przodownikiem pracy i to na dodatek bardzo oszczędnym,
    bo nie miał dzieci ani baby, szybko udało mu się odłożyć miliard
    dolarów i jeszcze kilka rubli na walizkę. Wtedy znów pojawił się
    diaboł.

    "O, cóż za spotkanie. Trzym hajs i spełnij moje życzenie, tak jak
    się umawialiśmy" - powiedział rusek i podał diabołowi walizkę.
    "Wisz co" - odpowiedział mu diaboł - "zmieniłem zdanie. Życzenia
    nie spełnię, ale za to dam ci miliard dolarów. Łapaj" - i diaboł
    oddał ruskowi walizkę.

    Jaki morał płynie z tej bajki? Diaboł to bydle złe i przeokrutne,
    gdyż w logice, którą posługuje się przy robieniu dili (względnie
    podpisywaniu cyrografów) obowiązuje prawo eliminacji podwójnej
    negacji. *)

(** Prawo to prezentuje się podobnie jak prawo wyłączonego środka: *)

Lemma dne :
  forall P : Prop, ~ ~ P -> P.
Proof.
  intros P nnp.
Abort.

(** Po pierwsze, nie da się go konstruktywnie udowodnić. *)

Lemma DNE_irrefutable :
  forall P : Prop, ~ ~ (~ ~ P -> P).
Proof.
  intros P H.
  apply H.
  intro nnp.
  cut False.
    contradiction.
    apply nnp. intro p. apply H. intros _. assumption.
Qed.

(** Po drugie, jest ono niezaprzeczalne. *)

(** Po trzecie, jest równoważne prawu wyłączonego środka. *)