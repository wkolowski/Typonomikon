(** * B3: Logika klasyczna [TODO] *)

(* begin hide *)
Require Export B2.
(*
TODO: Wprowadzić pojęcie tabu (na aksjomaty etc.) i zacząć go używać.
TODO: Kodowanie logiki klasycznej jak z SSReflekta
*)
(* end hide *)

(** * Aksjomaty i prawa logiki klasycznej (TODO) *)

Definition LEM : Prop :=
  forall P : Prop, P \/ ~ P.

Definition MI : Prop :=
  forall P Q : Prop, (P -> Q) -> ~ P \/ Q.

Definition ME : Prop :=
  forall P Q : Prop, (P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q).

Definition DNE : Prop :=
  forall P : Prop, ~ ~ P -> P.

Definition CM : Prop :=
  forall P : Prop, (~ P -> P) -> P.

Definition Peirce : Prop :=
  forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition Contra : Prop :=
  forall P Q : Prop, (~ Q -> ~ P) -> (P -> Q).

Ltac u :=
  unfold LEM, DNE, CM, MI, ME, Peirce, Contra.

(** Tu o prawie zachowania informacji.

    A o paradoksach implikacji materialnej? *)

(** * Logika klasyczna jako logika Boga (TODO) *)

Lemma LEM_hard : forall P : Prop, P \/ ~ P.
Proof.
  intro P. left.
Restart.
  intro P. right. intro p.
Abort.

Lemma LEM_irrefutable :
  forall P : Prop, ~ ~ (P \/ ~ P).
Proof.
  intros P H.
  apply H. right. intro p.
  apply H. left. assumption.
Qed.

Lemma LEM_DNE :
  (forall P : Prop, P \/ ~ P) ->
    (forall P : Prop, ~ ~ P -> P).
(* begin hide *)
Proof.
  intros LEM P nnp. destruct (LEM P).
    assumption.
    contradiction.
Qed.
(* end hide *)

Lemma LEM_MI :
  (forall P : Prop, P \/ ~ P) ->
    (forall P Q : Prop, (P -> Q) -> ~ P \/ Q).
(* begin hide *)
Proof.
  intros LEM P Q H. destruct (LEM P) as [p | p].
    right. apply H. assumption.
    left. assumption.
Qed.
(* end hide *)

Lemma LEM_ME :
  (forall P : Prop, P \/ ~ P) ->
    (forall P Q : Prop, (P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q)).
(* begin hide *)
Proof.
  intros LEM P Q HPQ. destruct HPQ as [PQ QP].
    destruct (LEM P) as [p | np], (LEM Q) as [q | nq].
      left. split; assumption.
      specialize (PQ p). contradiction.
      specialize (QP q). contradiction.
      right. split; assumption.
Qed.
(* end hide *)

Lemma LEM_Peirce :
  (forall P : Prop, P \/ ~ P) ->
    (forall P Q : Prop, ((P -> Q) -> P) -> P).
(* begin hide *)
Proof.
  intros LEM P Q H. destruct (LEM P) as [p | np].
    assumption.
    apply H. intro. contradiction.
Qed.
(* end hide *)

Lemma LEM_CM :
  (forall P : Prop, P \/ ~ P) ->
    (forall P : Prop, (~ P -> P) -> P).
(* begin hide *)
Proof.
  intros LEM P H. destruct (LEM P) as [p | np].
    assumption.
    apply H. assumption.
Qed.
(* end hide *)

Lemma LEM_Contra :
  (forall P : Prop, P \/ ~ P) ->
    (forall P Q : Prop, (~ Q -> ~ P) -> (P -> Q)).
(* begin hide *)
Proof.
  intros LEM P Q H p. destruct (LEM Q) as [q | nq].
    assumption.
    specialize (H nq). contradiction.
Qed.
(* end hide *)

(** ** Metoda zerojedynkowa *)

(** Tutaj o rysowaniu tabelek. *)

(** * Logika klasyczna jako logika materialnej implikacji i równoważności (TODO) *)

Lemma material_implication_conv :
  forall P Q : Prop, ~ P \/ Q -> (P -> Q).
Proof.
  intros P Q H. destruct H as [np | q].
    intro p. contradiction.
    intro p. assumption.
Qed.

Lemma material_implication' :
  forall P Q : Prop, (P -> Q) -> ~ P \/ Q.
Proof.
  intros P Q H. left. intro p. specialize (H p).
Restart.
  intros P Q H. right. apply H.
Abort.

Lemma material_implication_irrefutable :
  forall P Q : Prop, ~ ~ ((P -> Q) -> ~ P \/ Q).
Proof.
  intros P Q H.
  apply H. intro pq.
  left. intro.
  apply H. intros _.
  right. apply pq.
  assumption.
Qed.

Lemma MI_LEM :
  MI -> LEM.
(* begin hide *)
Proof.
  unfold MI, LEM. intros MI P.
  destruct (MI P P).
    intro p. assumption.
    right. assumption.
    left. assumption.
Qed.
(* end hide *)

Lemma MI_DNE :
  MI -> DNE.
(* begin hide *)
Proof.
  u. intros MI P nnp. destruct (MI P P) as [np | p].
    intro p. assumption.
    contradiction.
    assumption.
Qed.
(* end hide *)

Lemma MI_CM :
  MI -> CM.
(* begin hide *)
Proof.
  u. intros MI P H. destruct (MI P P) as [np | p].
    intro p. assumption.
    apply H. assumption.
    assumption.
Qed.
(* end hide *)

Lemma MI_ME :
  MI -> ME.
(* begin hide *)
Proof.
  u. intros MI P Q [pq qp]. destruct (MI _ _ pq) as [np | q].
    right. split.
      assumption.
      intro q. apply np. apply qp. assumption.
    left. split.
      apply qp. assumption.
      assumption.
Qed.
(* end hide *)

Lemma MI_Peirce :
  MI -> Peirce.
(* begin hide *)
Proof.
  u. intros MI P Q H. destruct (MI P P).
    trivial.
    apply H. intro p. contradiction.
    assumption.
Qed.
(* end hide *)

Lemma MI_Contra :
  MI -> Contra.
(* begin hide *)
Proof.
  u. intros MI P Q H p. destruct (MI Q Q).
    trivial.
    contradiction H.
    assumption.
Qed.
(* end hide *)

Lemma material_equivalence_conv :
  forall P Q : Prop, (P /\ Q) \/ (~ P /\ ~ Q) -> (P <-> Q).
Proof.
  intros P Q H. destruct H as [pq | npnq].
    destruct pq as [p q]. split.
      intro p'. assumption.
      intro q'. assumption.
    destruct npnq as [np nq]. split.
      intro p. contradiction.
      intro q. contradiction.
Qed.

Lemma material_equivalence :
  forall P Q : Prop, (P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q).
Proof.
  intros P Q [pq qp]. left. split.
    apply qp. apply pq.
Restart.
  intros P Q [pq qp]. right. split.
    intro p.
Abort.

Lemma material_equivalence_irrefutable :
  forall P Q : Prop, ~ ~ ((P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q)).
Proof.
  intros P Q nme.
  apply nme. intros [pq qp].
  right. split.
    intro p. apply nme. intros _. left. split.
      assumption.
      apply pq. assumption.
    intro q. apply nme. intros _. left. split.
      apply qp. assumption.
      assumption.
Qed.

Lemma ME_LEM :
  ME -> LEM.
(* begin hide *)
Proof.
  u. intros ME P. destruct (ME P P).
    split; trivial.
    destruct H. left. assumption.
    destruct H. right. assumption.
Qed.
(* end hide *)

Lemma ME_DNE :
  ME -> DNE.
(* begin hide *)
Proof.
  u. intros ME P nnp. destruct (ME P P).
    split; trivial.
    destruct H. assumption.
    destruct H. contradiction.
Qed.
(* end hide *)

Lemma ME_MI :
  ME -> MI.
(* begin hide *)
Proof.
  u. intros ME P Q pq. destruct (ME P P).
    split; trivial.
    right. apply pq. destruct H. assumption.
    left. destruct H. assumption.
Qed.
(* end hide *)

Lemma ME_CM :
  ME -> CM.
(* begin hide *)
Proof.
  u. intros ME P H. destruct (ME P P) as [p | np].
    split; trivial.
    destruct p. assumption.
    destruct np. apply H. assumption.
Qed.
(* end hide *)

Lemma ME_Peirce :
  ME -> Peirce.
(* begin hide *)
Proof.
  u. intros ME P Q H. destruct (ME P P) as [p | np].
    split; trivial.
    destruct p. assumption.
    destruct np. apply H. intro p. contradiction.
Qed.
(* end hide *)

Lemma ME_Contra :
  ME -> Contra.
(* begin hide *)
Proof.
  u. intros ME P Q npnq p. destruct (ME Q Q).
    split; trivial.
    destruct H. assumption.
    destruct H. specialize (npnq H). contradiction.
Qed.
(* end hide *)

(** * Logika klasyczna jako logika diabła (TODO) *)

(* [P] jest stabilne, gdy [~ ~ P -> P] *)

Lemma not_not_True :
  ~ ~ True -> True.
(* begin hide *)
Proof.
  intros _. trivial.
Qed.
(* end hide *)

Lemma not_not_False :
  ~ ~ False -> False.
(* begin hide *)
Proof.
  intro H. apply H. intro H'. assumption.
Qed.
(* end hide *)

Lemma not_not_and :
  forall P Q : Prop,
    (~ ~ P -> P) -> (~ ~ Q -> Q) -> ~ ~ (P /\ Q) -> P /\ Q.
(* begin hide *)
Proof.
  intros P Q Hp Hq npq.
  split.
    apply Hp. intro np. apply npq. intro pq. destruct pq as [p q].
      apply np. assumption.
    apply Hq. intro nq. apply npq. intro pq. destruct pq as [p q].
      apply nq. assumption.
Qed.
(* end hide *)

Lemma not_not_impl :
  forall P Q : Prop,
    (~ ~ Q -> Q) -> ~ ~ (P -> Q) -> P -> Q.
(* begin hide *)
Proof.
  intros P Q nnq nnpq p.
  apply nnq. intro nq.
  apply nnpq. intro npq.
  apply nq, npq, p.
Qed.
(* end hide *)

Lemma not_not_forall :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, ~ ~ P x -> P x) -> ~ ~ (forall x : A, P x) ->
      forall x : A, P x.
(* begin hide *)
Proof.
  intros A P Hnn nnH x.
  apply Hnn. intro np.
  apply nnH. intro nap.
  apply np, nap.
Qed.
(* end hide *)

Lemma not_not_elim :
  forall P Q : Prop,
    (~ ~ Q -> Q) -> (P -> Q) -> ~ ~ P -> Q.
(* begin hide *)
Proof.
  intros P Q nnqq pq nnp.
  apply nnqq. intro nq.
  apply nnp. intro p.
  apply nq, pq, p.
Qed.
(* end hide *)

(** Dawno dawno temu w odległej galaktyce, a konkretniej w ZSRR, był
    sobie pewien rusek. Pewnego razu do ruska przyszedł diaboł (a to,
    jak wiadomo, coś dużo gorszego niż diabeł) i zaoferował mu taki
    dil: "dam ci miliard dolarów albo jeżeli dasz mi miliard dolarów,
    to spełnię dowolne twoje życzenie".

    Rusek trochę skonsternowany, nie bardzo widzi mu się podpisywanie
    cyrografu krwią. "Nie nie, żadnych cyrografów, ani innych takich
    kruczków prawnych", zapewnia go diaboł. Rusek myśli sobie tak:
    "pewnie hajsu nie dostanę, ale przecież nic nie tracę", a mówi:
    "No dobra, bierę".

    "Świetnie!" - mówi diaboł - "Jeżeli dasz mi miliard dolarów, to
    spełnie dowolne twoje życzenie". Cóż, rusek był zawiedziony, ale
    nie zaskoczony - przecież dokładnie tego się spodziewał. Niedługo
    później diaboł zniknął, a rusek wrócił do pracy w kołchozie.

    Jako, że był przodownikiem pracy i to na dodatek bardzo oszczędnym,
    bo nie miał dzieci ani baby, szybko udało mu się odłożyć miliard
    dolarów i jeszcze kilka rubli na walizkę. Wtedy znów pojawił się
    diaboł.

    "O, cóż za spotkanie. Trzym hajs i spełnij moje życzenie, tak jak
    się umawialiśmy" - powiedział rusek i podał diabołowi walizkę.
    "Wisz co" - odpowiedział mu diaboł - "zmieniłem zdanie. Życzenia
    nie spełnię, ale za to dam ci miliard dolarów. Łapaj" - i diaboł
    oddał ruskowi walizkę.

    Jaki morał płynie z tej bajki? Diaboł to bydle złe i przeokrutne,
    gdyż w logice, którą posługuje się przy robieniu dili (względnie
    podpisywaniu cyrografów) obowiązuje prawo eliminacji podwójnej
    negacji. *)

(** Prawo to prezentuje się podobnie jak prawo wyłączonego środka: *)

Lemma DNE_hard :
  forall P : Prop, ~ ~ P -> P.
Proof.
  intros P nnp.
Abort.

(** Po pierwsze, nie da się go konstruktywnie udowodnić. *)

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

Lemma DNE_LEM :
  DNE -> LEM.
(* begin hide *)
Proof.
  intros DNE P. apply DNE.
  intro H. apply H. right.
  intro p. apply H. left.
  assumption.
Qed.
(* end hide *)

Lemma DNE_MI :
  DNE -> MI.
(* begin hide *)
Proof.
  intros DNE P Q pq. apply DNE.
  intro H. apply H. left.
  intro p. apply H. right.
  apply pq. assumption.
Qed.
(* end hide *)

Lemma DNE_ME :
  DNE -> ME.
(* begin hide *)
Proof.
  intros DNE P Q [pq qp]. apply DNE.
  intro H. apply H.
  right. split.
    intro p. apply H. left. split.
      assumption.
      apply pq. assumption.
    intro q. apply H. left. split.
      apply qp. assumption.
        assumption.
Qed.
(* end hide *)

Lemma DNE_CM :
  DNE -> CM.
(* begin hide *)
Proof.
  intros DNE P H. apply DNE. intro np. apply np. apply H. assumption.
Qed.
(* end hide *)

Lemma DNE_Peirce :
  DNE -> Peirce.
(* begin hide *)
Proof.
  intros DNE P Q. apply DNE.
  intro H. apply H.
  intro pqp. apply DNE.
  intro np. apply np. apply pqp.
  intro p. contradiction.
Qed.
(* end hide *)

Lemma DNE_Contra :
  DNE -> Contra.
(* begin hide *)
Proof.
  intros DNE P Q nqnp. apply DNE.
  intro npq. apply nqnp.
    intro q. apply npq. intros _. assumption.
    apply DNE. intro np. apply npq. intro p. contradiction.
Qed.
(* end hide *)

(** * Logika klasyczna jako logika kontrapozycji (TODO) *)

Lemma contraposition' :
  forall P Q : Prop, (~ Q -> ~ P) -> (P -> Q).
Proof.
  intros P Q H p.
Abort.

Lemma contraposition_irrefutable :
  forall P Q : Prop, ~ ~ ((~ Q -> ~ P) -> (P -> Q)).
Proof.
  intros P Q H. apply H.
  intros nqnp p. cut False.
    contradiction.
    apply nqnp.
      intro. apply H. intros _ _. assumption.
      assumption.
Qed.

Lemma Contra_LEM :
  Contra -> LEM.
(* begin hide *)
Proof.
  unfold Contra, LEM.
  intros Contra P.
  apply (Contra (~ ~ (P \/ ~ P))).
    intros H1 H2. contradiction.
    intro H. apply H. right. intro p. apply H. left. assumption.
Qed.
(* end hide *)

Lemma Contra_MI :
  Contra -> MI.
(* begin hide *)
Proof.
  intros Contra P Q. apply Contra. intros H1 H2. apply H1.
    left. intro p. apply H1. right. apply H2. assumption.
Qed.
(* end hide *)

Lemma Contra_ME :
  Contra -> ME.
(* begin hide *)
Proof.
  intros Contra P Q. apply Contra. intros H [pq qp].
    apply H. right. split.
      intro p. apply H. left. split.
        assumption.
        apply pq. assumption.
      intro q. apply H. left. split.
        apply qp. assumption.
        assumption.
Qed.
(* end hide *)

Lemma Contra_DNE :
  Contra -> DNE.
(* begin hide *)
Proof.
  intros Contra P.
  apply (Contra (~ ~ P) P).
  intros np nnp.
  contradiction.
Qed.
(* end hide *)

Lemma Contra_CM :
  Contra -> CM.
(* begin hide *)
Proof.
  unfold Contra, CM.
  intros Contra P.
  apply Contra.
  intros np npp.
  apply np. apply npp.
  intro p. contradiction.
Qed.
(* end hide *)

Lemma Contra_Peirce :
  Contra -> Peirce.
(* begin hide *)
Proof.
  unfold Contra, Peirce.
  intros Contra P Q.
  apply Contra.
  intros np H.
  apply np, H.
  intro p.
  contradiction.
Qed.
(* end hide *)

(** * Logika klasyczna jako logika Peirce'a (TODO) *)

(** ** Logika cudownych konsekwencji (TODO) *)

Lemma consequentia_mirabilis :
  forall P : Prop, (~ P -> P) -> P.
Proof.
  intros P H. apply H. intro p.
Abort.

Lemma consequentia_mirabilis_irrefutable :
  forall P : Prop, ~ ~ ((~ P -> P) -> P).
Proof.
  intros P H. apply H.
  intro npp. apply npp.
  intro p. apply H.
  intros _. assumption.
Qed.

Lemma CM_LEM :
  CM -> LEM.
(* begin hide *)
Proof.
  intros CM P. apply CM.
  intro H. right.
  intro p. apply H.
  left. assumption.
Qed.
(* end hide *)

Lemma CM_MI :
  CM -> MI.
(* begin hide *)
Proof.
  intros CM P Q pq. apply CM.
  intro H. left.
  intro p. apply H.
  right. apply pq. assumption.
Qed.
(* end hide *)

Lemma CM_ME :
  CM -> ME.
(* begin hide *)
Proof.
  intros CM P Q H. destruct H as [pq qp]. apply CM. intro H.
    right. split.
      intro p. apply H. left. split.
        assumption.
        apply pq. assumption.
      intro q. apply H. left. split.
        apply qp. assumption.
        assumption.
Qed.
(* end hide *)

Lemma CM_DNE :
  CM -> DNE.
(* begin hide *)
Proof.
  intros CM P H. apply CM. intro np. contradiction.
Qed.
(* end hide *)

Lemma CM_Peirce :
  CM -> Peirce.
(* begin hide *)
Proof.
  intros CM P Q H. apply CM.
  intro np. apply H.
  intro p. contradiction.
Qed.
(* end hide *)

Lemma CM_Contra :
  CM -> Contra.
(* begin hide *)
Proof.
  intros CM P Q npnq p. apply CM.
  intro nq. contradiction npnq.
Qed.
(* end hide *)

(** ** Logika Peirce'a (TODO) *)

Lemma Peirce_hard :
  forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
  intros P Q H.
  apply H. intro p.
Abort.

Lemma Peirce_irrefutable :
  forall P Q : Prop, ~ ~ (((P -> Q) -> P) -> P).
Proof.
  intros P Q H.
  apply H. intro pqp.
  apply pqp. intro p.
  cut False.
    contradiction.
    apply H. intros _. assumption.
Qed.

Lemma Peirce_LEM :
  Peirce -> LEM.
(* begin hide *)
Proof.
  unfold Peirce, LEM.
  intros Peirce P.
  apply (Peirce _ (~ P)). intro H.
  right. intro p. apply H.
    left. assumption.
    assumption.
Qed.
(* end hide *)

Lemma Peirce_MI :
  Peirce -> MI.
(* begin hide *)
Proof.
  unfold Peirce, MI.
  intros Peirce P Q.
  apply (Peirce _ False).
  intros H pq. left.
  intro p. apply H.
  intros _. right.
  apply pq. assumption.
Qed.
(* end hide *)

Lemma Peirce_ME :
  Peirce -> ME.
(* begin hide *)
Proof.
  unfold Peirce, ME.
  intros Peirce P Q [pq qp]. apply (Peirce _ False). intros H.
    right. split.
      intro p. apply H. left. split.
        assumption.
        apply pq. assumption.
      intro q. apply H. left. split.
        apply qp. assumption.
        assumption.
Qed.
(* end hide *)

Lemma Peirce_DNE :
  Peirce -> DNE.
(* begin hide *)
Proof.
  unfold Peirce, DNE.
  intros Peirce P nnp.
  apply (Peirce P (~ P)).
  intro H. cut False.
    contradiction.
    apply nnp. intro p. apply H.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma Peirce_CM :
  Peirce -> CM.
(* begin hide *)
Proof.
  unfold Peirce, CM.
  intros Peirce P.
  apply Peirce.
Qed.
(* end hide *)

Lemma Peirce_Contra :
  Peirce -> Contra.
(* begin hide *)
Proof.
  unfold Peirce, Contra.
  intros Peirce P Q nqnp p.
  apply (Peirce Q (~ P)).
  intro qnp.
  cut False.
    contradiction.
    apply nqnp.
      intro q. contradiction qnp.
      assumption.
Qed.
(* end hide *)

(** * Paradoks pijoka *)

Theorem drinkers_paradox :
  LEM ->
    forall (man : Type) (drinks : man -> Prop) (random_guy : man),
      exists drinker : man, drinks drinker ->
        forall x : man, drinks x.
(* begin hide *)
(* TODO: poprawić paradoks pijoka! *)
Proof.
  intros lem **.
  destruct (lem (exists x : man, ~ drinks x)).
    destruct H as [x H]. exists x. intro. contradiction.
    exists random_guy. intros. destruct (lem (drinks x)).
      assumption.
      contradiction H. exists x. assumption.
Qed.
(* end hide *)

(** Na zakończenie zwróćmy swą uwagę ku kolejnemu paradoksowi, tym razem
    dotyczącemu logiki klasycznej. Z angielska zwie się on "drinker's
    paradox", ja zaś ku powszechnej wesołości używał będę nazwy "paradoks
    pijoka".

    Zazwyczaj jest on wyrażany mniej więcej tak: w każdym barze jest taki
    człowiek, że jeżeli on pije, to wszyscy piją. Jak to możliwe? Czy
    matematyka stwierdza istnienie magicznych ludzi zdolnych popaść swoich
    barowych towarzyszy w alkoholizm?

    Oczywiście nie. W celu osiągnięcia oświecenia w tej kwestii prześledźmy
    dowód tego faktu (jeżeli nie udało ci się go wymyślić, pomyśl jeszcze
    trochę).

    Ustalmy najpierw, jak ma się formalne brzmienie twierdzenia do naszej
    poetyckiej parafrazy dwa akapity wyżej. Początek "w każdym barze"
    możemy pominąć i sformalizować sytuację w pewnym konkretnym barze. Nie
    ma to znaczenia dla prawdziwości tego zdania.

    Sytuację w barze modelujemy za pomocą typu [man], które reprezentuje
    klientów baru, predykatu [drinks], interpretowanego tak, że [drinks x]
    oznacza, że [x] pije. Pojawia się też osoba określona tajemniczym
    mianem [random_guy]. Jest ona konieczna, gdyż nasza poetycka parafraza
    czyni jedno założenie implicite: mianowicie, że w barze ktoś jest.
    Jest ono konieczne, gdyż gdyby w barze nie było nikogo, to w szczególności
    nie mogłoby tam być nikogo, kto spełnia jakieś dodatkowe warunki.

    I tak docieramy do sedna sprawy: istnieje osoba, którą będziemy zwać
    pijokiem ([exists drinker : man]), taka, że jeżeli ona pije ([drinks
    drinker]), to wszyscy piją ([forall x : man, drinks x]).

    Dowód jest banalny i opiera się na zasadzie wyłączonego środka, w Coqu
    zwanej [classic]. Dzięki niej możemy sprowadzić dowód do analizy
    dwóch przypadków.

    Przypadek 1: wszyscy piją. Cóż, skoro wszyscy piją, to wszyscy piją.
    Pozostaje nam wskazać pijoka: mógłby to być ktokolwiek, ale z
    konieczności zostaje nim [random_guy], gdyż do żadnego innego klienta
    baru nie możemy się odnieść.

    Przypadek 2: nieprawda, że wszyscy piją. Parafrazując: istnieje ktoś,
    kto nie pije. Jest to obserwacja kluczowa. Skoro kolo przyszedł do baru
    i nie pije, to z automatu jest podejrzany. Uczyńmy go więc, wbrew
    zdrowemu rozsądkowi, naszym pijokiem.

    Pozostaje nam udowodnić, że jeżeli pijok pije, to wszyscy piją. Załóżmy
    więc, że pijok pije. Wiemy jednak skądinąd, że pijok nie pije. Wobec
    tego mamy sprzeczność i wszyscy piją (a także jedzą naleśniki z betonem
    serwowane przez gadające ślimaki i robią dużo innych dziwnych rzeczy —
    wszakże _ex falso quodlibet_).

    Gdzież więc leży paradoksalność całego paradoksu? Wynika ona w znacznej
    mierze ze znaczenia słowa "jeżeli". W mowie potocznej różni się ono
    znacznie od tzw. implikacji materialnej, w Coqu reprezentowanej (ale
    tylko przy założeniu reguły wyłączonego środka) przez implikację ([->]).

    Określenie "taka osoba, że jeżeli ona pije, to wszyscy piją" przeciętny
    człowiek interpretuje w kategoriach przyczyny i skutku, a więc przypisuje
    rzeczonej osobie magiczną zdolność zmuszania wszystkich do picia, tak
    jakby posiadała zdolność wznoszenia toastów za pomocą telepatii.

    Jest to błąd, gdyż zamierzonym znaczeniem słowa jeżeli jest tutaj (ze
    względu na kontekst matematyczny) implikacja materialna. W jednym z
    powyższych ćwiczeń udowodniłeś, że w logice klasycznej mamy tautologię
    [P -> Q <-> ~P \/ Q], a więc że implikacja jest prawdziwa gdy jej
    przesłanka jest fałszywa lub gdy jej konkluzja jest prawdziwa.

    Do paradoksalności paradoksu swoje cegiełki dokładają też reguły logiki
    klasycznej (wyłączony środek) oraz logiki konstruktywnej (_ex falso
    quodlibet_), których w użyliśmy w dowodzie, a które dla zwykłego człowieka
    nie muszą być takie oczywiste. *)

(** **** Ćwiczenie (logika klasyczna) *)

(** W powyższym dowodzie logiki klasycznej użyłem conajmniej dwukrotnie.
    Zacytuj wszystkie fragmenty dowodu wykorzystujące logikę klasyczną. *)

(** **** Ćwiczenie (niepusty bar) *)

(** Pokaż, że założenie o tym, że w barze jest conajmniej jeden klient,
    jest konieczne. Co więcej, pokaż że stwierdzenie "w barze jest taki
    klient, że jeżeli on pije, to wszyscy piją" jest równoważne stwierdzeniu
    "w barze jest jakiś klient".

    Które z tych dwóch implikacji wymagają logiki intuicjonistycznej, a
    które klasycznej? *)

Lemma dp_nonempty :
  LEM ->
    forall (man : Type) (drinks : man -> Prop),
      (exists drinker : man, drinks drinker ->
        forall x : man, drinks x) <->
      (exists x : man, True).
(* begin hide *)
Proof.
  intro lem.
  split; intros; destruct H as [random_guy _].
    exists random_guy. trivial.
    apply drinkers_paradox; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: alternatywne wersje paradoksu pijoka *)

Lemma dp2 :
  forall (Man : Type) (Drinks : Man -> Prop),
    (exists drinker : Man, Drinks drinker) ->
      forall m : Man, Drinks m.
Proof.
Abort.

(* end hide *)

(** * Paradoks Curry'ego (TODO) *)

(** "Jeżeli niniejsze zdanie jest prawdziwe, to Niemcy graniczą z Chinami." *)

(** Inne paradoksy autoreferencji: paradoks Richarda, słowa heterologiczne *)

(** * Zadania (TODO) *)

(** wyrzucić zadania mącące (mieszające typy i zdania) *)

(** * Ściąga (TODO) *)