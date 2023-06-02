(** * B4: Logika klasyczna [TODO] *)

(* begin hide *)
(* From Typonomikon Require Export B1.
From Typonomikon Require Export B2. *)
From Typonomikon Require Export B3.
(*
TODO 1: Wprowadzić pojęcie tabu (na aksjomaty etc.) i zacząć go używać.
TODO 2: Kodowanie logiki klasycznej jak z SSReflekta
TODO 3: rozróżnienie na logikę klasyczną:
        - w sensie subuniwersum [Prop]
          (np. dla DNE - subuniwersum zdań spełniających [~ ~ P -> P])
        - w sensie aksjomatu
        - w sensie dodatkowego założenia *)

(* end hide *)

(** * Aksjomaty i prawa logiki klasycznej (TODO) *)

(** TODO:
    - enumeracja, krótki opis
    - podział na grupy:
      [DNE]
      vs [LEM] (TODO': logika klasyczna jako logika zdań rozstrzygalnych)
      vs materialna implikacja i równoważność (i potencjalnie pozostałe "słabe" spójniki)
      vs kontrapozycja
      vs consequentia mirabilis i [Peirce] (jako rzeczy wyglądające podobnie do [DNE], a
         w praktyce wyłazące, jak człowiek próbuje użyć [LEM]) *)

Definition DNE : Prop :=
  forall P : Prop, ~ ~ P -> P.

Definition LEM : Prop :=
  forall P : Prop, P \/ ~ P.

Definition CM : Prop :=
  forall P : Prop, (~ P -> P) -> P.

Definition Peirce : Prop :=
  forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition Contra : Prop :=
  forall P Q : Prop, (~ Q -> ~ P) -> (P -> Q).

Definition MI : Prop :=
  forall P Q : Prop, (P -> Q) -> ~ P \/ Q.

Definition ME : Prop :=
  forall P Q : Prop, (P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q).

Definition or_wor : Prop :=
  forall P Q : Prop, (~ P -> Q) -> P \/ Q.

Definition and_wand : Prop :=
  forall P Q : Prop, ~ (~ P \/ ~ Q) -> P /\ Q.

Definition snimpl_nimpl : Prop :=
  forall P Q : Prop, ~ (P -> Q) -> (P /\ ~ Q).

Definition xor_wxor : Prop :=
  forall P Q : Prop, ~ (P <-> Q) -> xor P Q.

Ltac u :=
  unfold DNE, LEM, CM, Peirce, Contra, MI, ME, or_wor, and_wand, snimpl_nimpl, xor_wxor.

(** * Logika klasyczna jako logika diabła (TODO) *)

(** Dawno dawno temu w odległej galaktyce, a konkretniej w ZSRR, był
    sobie pewien rusek. Pewnego razu do ruska przyszedł diaboł (a
    diaboł to, jak wiadomo, coś dużo gorszego niż diabeł) i zaoferował
    mu taki oto deal: "dam ci miliard dolarów lub jeżeli dasz mi
    miliard dolarów, to spełnię dowolne twoje życzenie".

    Rusek trochę skonsternowany, nie bardzo widzi mu się podpisywanie
    cyrografu krwią. "Nie nie, żadnych cyrografów, ani innych takich
    kruczków prawnych", zapewnia go diaboł. Rusek myśli sobie tak:
    "pewnie hajsu nie dostanę, ale przecież nic nie tracę", po czym
    mówi: "No dobra, bierę".

    "Świetnie!" - mówi diaboł - "Jeżeli dasz mi miliard dolarów, to
    spełnie dowolne twoje życzenie". Cóż, rusek był zawiedziony, ale
    nie zaskoczony - przecież dokładnie tego się spodziewał. Niedługo
    później diaboł zniknął, a rusek wrócił do pracy w kołchozie.

    Jako, że był przodownikiem pracy i to na dodatek bardzo oszczędnym,
    bo nie miał dzieci ani baby, szybko udało mu się odłożyć miliard
    dolarów i jeszcze kilka rubli na walizkę, coby mieć gdzie trzymać
    dolary. Wtedy znów pojawił się diaboł.

    "O, cóż za spotkanie. Trzym hajs i spełnij moje życzenie, tak jak
    się umawialiśmy" - powiedział rusek i podał diabołowi walizkę.
    "Wisz co" - odpowiedział mu diaboł - "zmieniłem zdanie. Życzenia
    nie spełnię, ale za to dam ci miliard dolarów. Łapaj" - i diaboł
    oddał ruskowi walizkę.

    Jaki morał płynie z tej bajki? Diaboł to bydle złe i przeokrutne,
    gdyż w logice, którą posługuje się przy robieniu dealów (względnie
    podpisywaniu cyrografów) obowiązuje prawo eliminacji podwójnej
    negacji. *)

(** Prawo to prezentuje się podobnie jak prawo wyłączonego środka: *)

Lemma DNE_hard :
  forall P : Prop, ~ ~ P -> P.
Proof.
  intros P nnp.
Abort.

(** Po pierwsze, nie da się go konstruktywnie udowodnić. *)

Lemma Irrefutable_DNE :
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

(** ** Logika zdań stabilnych *)

(** [P] jest stabilne, gdy [~ ~ P -> P] *)

Definition Stable (P : Prop) : Prop :=
  ~ ~ P -> P.

Lemma Stable_True :
  Stable True.
(* begin hide *)
Proof.
  intros _. trivial.
Qed.
(* end hide *)

Lemma Stable_False :
  Stable False.
(* begin hide *)
Proof.
  intro H. apply H. intro H'. assumption.
Qed.
(* end hide *)

Lemma Stable_and :
  forall P Q : Prop,
    Stable P -> Stable Q -> Stable (P /\ Q).
(* begin hide *)
Proof.
  unfold Stable.
  intros P Q Hp Hq npq.
  split.
  - apply Hp. intro np. apply npq. intros [p q]. apply np. assumption.
  - apply Hq. intro nq. apply npq. intros [p q]. apply nq. assumption.
Restart.
  unfold Stable; tauto.
Qed.
(* end hide *)

Lemma Stable_impl :
  forall P Q : Prop,
    Stable Q -> Stable (P -> Q).
(* begin hide *)
Proof.
  unfold Stable.
  intros P Q nnq nnpq p.
  apply nnq. intro nq.
  apply nnpq. intro npq.
  apply nq, npq, p.
Qed.
(* end hide *)

Lemma Stable_forall :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, Stable (P x)) -> Stable (forall x : A, P x).
(* begin hide *)
Proof.
  unfold Stable.
  intros A P Hnn nnH x.
  apply Hnn. intro np.
  apply nnH. intro nap.
  apply np, nap.
Qed.
(* end hide *)

Lemma Stable_exists :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, Stable (P x)) -> Stable (exists x : A, P x).
Proof.
  unfold Stable.
  intros A P Hnnp nnex.
Abort.

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

(** * Logika klasyczna jako logika Boga (TODO) *)

Lemma LEM_hard : forall P : Prop, P \/ ~ P.
Proof.
  intro P. left.
Restart.
  intro P. right. intro p.
Abort.

Lemma Irrefutable_LEM :
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

(** ** Zdania określone *)

Definition Definite (P : Prop) : Prop :=
  P \/ ~ P.

Lemma Definite_True :
  Definite True.
(* begin hide *)
Proof.
  unfold Definite.
  now left.
Qed.
(* end hide *)

Lemma Definite_False :
  Definite False.
(* begin hide *)
Proof.
  unfold Definite.
  now right.
Qed.
(* end hide *)

Lemma Definite_impl :
  forall P Q : Prop,
    Definite P -> Definite Q -> Definite (P -> Q).
(* begin hide *)
Proof.
  unfold Definite.
  intros P Q pnp [q | nq].
  - now left.
  - destruct pnp as [p | np].
    + right; intros pq.
      apply nq, pq, p.
    + left; intros.
      contradiction.
Qed.
(* end hide *)

Lemma Definite_or :
  forall P Q : Prop,
    Definite P -> Definite Q -> Definite (P \/ Q).
(* begin hide *)
Proof.
  unfold Definite.
  tauto.
Qed.
(* end hide *)

Lemma Definite_and :
  forall P Q : Prop,
    Definite P -> Definite Q -> Definite (P /\ Q).
(* begin hide *)
Proof.
  unfold Definite.
  tauto.
Qed.
(* end hide *)

Lemma Definite_iff :
  forall P Q : Prop,
    Definite P -> Definite Q -> Definite (P <-> Q).
(* begin hide *)
Proof.
  unfold Definite.
  tauto.
Qed.
(* end hide *)

Lemma Definite_not :
  forall P : Prop,
    Definite P -> Definite (~ P).
(* begin hide *)
Proof.
  unfold Definite.
  tauto.
Qed.
(* end hide *)

Lemma Definite_forall_failed :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, Definite (P x)) -> Definite (forall x : A, P x).
Proof.
  unfold Definite.
  intros A P HD.
Abort.

Lemma Definite_exists_failed :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, Definite (P x)) -> Definite (exists x : A, P x).
Proof.
  unfold Definite.
  intros A P HD.
Abort.

(** ** Metoda zerojedynkowa (TODO) *)

(** Tutaj o rysowaniu tabelek. *)

(** * Logika klasyczna jako logika kontrapozycji *)

Lemma contraposition' :
  forall P Q : Prop, (~ Q -> ~ P) -> (P -> Q).
Proof.
  intros P Q H p.
Abort.

Lemma Irrefutable_Contra :
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

(** ** Zdania kontrapozowalne dziedzinowo (TODO) *)

Definition DomainContraposable (P : Prop) : Prop :=
  forall R : Prop, (~ R -> ~ P) -> (P -> R).

Lemma DomainContraposable_True_fail :
  DomainContraposable True.
Proof.
  unfold DomainContraposable.
  intros R nt _.
Abort.

Lemma DomainContraposable_False :
  DomainContraposable False.
(* begin hide *)
Proof.
  unfold DomainContraposable.
  intros R _ [].
Qed.
(* end hide *)

Lemma DomainContraposable_impl_fail :
  forall P Q : Prop,
    DomainContraposable P -> DomainContraposable Q -> DomainContraposable (P -> Q).
Proof.
  unfold DomainContraposable.
  intros P Q HP HQ R npq pq.
  apply HP. tauto.
Abort.

Lemma DomainContraposable_or :
  forall P Q : Prop,
    DomainContraposable P -> DomainContraposable Q -> DomainContraposable (P \/ Q).
(* begin hide *)
Proof.
  unfold DomainContraposable.
  intros P Q pr qr R H [p | q].
  - apply pr; [| assumption]. intros nr _. apply H; [| left]; assumption.
  - apply qr; [| assumption]. intros nq _. apply H; [| right]; assumption.
Qed.
(* end hide *)

Lemma DomainContraposable_and :
  forall P Q : Prop,
    DomainContraposable P -> DomainContraposable Q -> DomainContraposable (P /\ Q).
(* begin hide *)
Proof.
  unfold DomainContraposable.
  intros P Q pr qr R H [p q].
  apply pr; [| assumption]. intros nr _.
  apply H; [| split]; assumption.
Qed.
(* end hide *)

Lemma DomainContraposable_iff_fail :
  forall P Q : Prop,
    DomainContraposable P -> DomainContraposable Q -> DomainContraposable (P <-> Q).
Proof.
  unfold DomainContraposable.
  intros P Q pr qr R H [pq qp]. apply pr.
  - intros nr _. apply H; [| split]; assumption.
  -
Abort.

Lemma DomainContraposable_not_fail :
  forall P : Prop,
    DomainContraposable P -> DomainContraposable (~ P).
Proof.
  unfold DomainContraposable.
  intros P pr R nnp np.
  apply pr.
  - intros _. assumption.
  -
Abort.

Lemma DomainContraposable_forall_fail :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, DomainContraposable (P x)) -> DomainContraposable (forall x : A, P x).
Proof.
  unfold DomainContraposable.
Abort.

Lemma DomainContraposable_exists :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, DomainContraposable (P x)) -> DomainContraposable (exists x : A, P x).
(* begin hide *)
Proof.
  unfold DomainContraposable.
  intros A P r R H [x p].
  apply (r x); [| assumption].
  intros nr _. apply H; [assumption |].
  exists x. assumption.
Qed.
(* end hide *)

(** ** Zdania kontrapozowalne przeciwdziedzinowo *)

Definition CodomainContraposable (P : Prop) : Prop :=
  forall R : Prop, (~ P -> ~ R) -> (R -> P).

Lemma CodomainContraposable_True :
  CodomainContraposable True.
(* begin hide *)
Proof.
  unfold CodomainContraposable.
  trivial.
Qed.
(* end hide *)

Lemma CodomainContraposable_False :
  CodomainContraposable False.
(* begin hide *)
Proof.
  unfold CodomainContraposable.
  intros R nr r.
  apply nr; [| assumption].
  intros [].
Qed.
(* end hide *)

Lemma CodomainContraposable_impl :
  forall P Q : Prop,
    CodomainContraposable Q -> CodomainContraposable (P -> Q).
(* begin hide *)
Proof.
  unfold CodomainContraposable.
  intros P Q HQ R nr r p.
  apply HQ with R; [| assumption].
  intros nq _.
  apply nr; [| assumption].
  intros pq.
  apply nq, pq.
  assumption.
Qed.
(* end hide *)

Lemma CodomainContraposable_or_fail :
  forall P Q : Prop,
    CodomainContraposable P -> CodomainContraposable Q -> CodomainContraposable (P \/ Q).
Proof.
  unfold CodomainContraposable.
  intros P Q HP HQ R nr r.
  left; apply HP with R; [| assumption].
  intros np _.
  apply nr; [| assumption].
  intros [p | q]; [contradiction |].
Abort.

Lemma CodomainContraposable_and :
  forall P Q : Prop,
    CodomainContraposable P -> CodomainContraposable Q -> CodomainContraposable (P /\ Q).
(* begin hide *)
Proof.
  unfold CodomainContraposable.
  intros P Q HP HQ R nr r.
  split.
  - apply HP with R; [| assumption].
    intros np _.
    apply nr; [| assumption].
    intros [p _].
    contradiction.
  - apply HQ with R; [| assumption].
    intros np _.
    apply nr; [| assumption].
    intros [_ q].
    contradiction.
Qed.
(* end hide *)

Lemma CodomainContraposable_iff :
  forall P Q : Prop,
    CodomainContraposable P -> CodomainContraposable Q -> CodomainContraposable (P <-> Q).
(* begin hide *)
Proof.
  now intros; apply CodomainContraposable_and; apply CodomainContraposable_impl.
Qed.
(* end hide *)

Lemma CodomainContraposable_not :
  forall P : Prop,
    CodomainContraposable P -> CodomainContraposable (~ P).
(* begin hide *)
Proof.
  intros; apply CodomainContraposable_impl, CodomainContraposable_False.
Qed.
(* end hide *)

Lemma CodomainContraposable_forall :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, CodomainContraposable (P x)) -> CodomainContraposable (forall x : A, P x).
(* begin hide *)
Proof.
  unfold CodomainContraposable.
  intros A P HP R nr r x.
  apply HP with R; [| assumption].
  intros npx _.
  apply nr; [| assumption].
  intros np.
  apply npx, np.
Qed.
(* end hide *)

Lemma CodomainContraposable_exists_fail :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, CodomainContraposable (P x)) -> CodomainContraposable (exists x : A, P x).
Proof.
  unfold CodomainContraposable.
  intros A P HP R nr r.
Abort.

(** * Logika klasyczna jako logika cudownych konsekwencji (TODO) *)

(** ** Logika cudownych konsekwencji *)

Lemma consequentia_mirabilis :
  forall P : Prop, (~ P -> P) -> P.
Proof.
  intros P H. apply H. intro p.
Abort.

Lemma Irrefutable_CM :
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

(** *** Zdania cudowne *)

Definition Wonderful (P : Prop) : Prop :=
  (~ P -> P) -> P.

Lemma Wonderful_True :
  Wonderful True.
(* begin hide *)
Proof. unfold Wonderful; tauto. Qed.
(* end hide *)

Lemma Wonderful_False :
  Wonderful False.
(* begin hide *)
Proof. unfold Wonderful; tauto. Qed.
(* end hide *)

Lemma Wonderful_impl :
  forall P Q : Prop,
    Wonderful P -> Wonderful Q -> Wonderful (P -> Q).
(* begin hide *)
Proof. unfold Wonderful; tauto. Qed.
(* end hide *)

Lemma Wonderful_or_fail :
  forall P Q : Prop,
    Wonderful P -> Wonderful Q -> Wonderful (P \/ Q).
Proof.
  unfold Wonderful.
  intros P Q WP WQ H.
  apply H.
  intros [p | q].
Abort.

Lemma Wonderful_and :
  forall P Q : Prop,
    Wonderful P -> Wonderful Q -> Wonderful (P /\ Q).
(* begin hide *)
Proof. unfold Wonderful; tauto. Qed.
(* end hide *)

Lemma Wonderful_iff :
  forall P Q : Prop,
    Wonderful P -> Wonderful Q -> Wonderful (P <-> Q).
(* begin hide *)
Proof. unfold Wonderful; tauto. Qed.
(* end hide *)

Lemma Wonderful_not :
  forall P : Prop,
    Wonderful P -> Wonderful (~ P).
(* begin hide *)
Proof. unfold Wonderful; tauto. Qed.
(* end hide *)

Lemma Wonderful_forall :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, Wonderful (P x)) -> Wonderful (forall x : A, P x).
(* begin hide *)
Proof. unfold Wonderful; firstorder. Qed.
(* end hide *)

Lemma Wonderful_exists_fail :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, Wonderful (P x)) -> Wonderful (exists x : A, P x).
Proof.
  unfold Wonderful.
  intros A P W Hn.
  apply Hn. intros [x p].
Abort.

(** ** Logika Peirce'a *)

Lemma Peirce_hard :
  forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
  intros P Q H.
  apply H. intro p.
Abort.

Lemma not_Peirce_hard :
  forall P Q : Prop, ~ (((P -> Q) -> P) -> P).
Proof.
  intros P Q n.
Abort.

Lemma Irrefutable_Peirce :
  forall P Q : Prop, ~ ~ (((P -> Q) -> P) -> P).
Proof.
  intros P Q H.
  apply H. intro pqp.
  apply pqp. intro p.
  exfalso.
  apply H. intros _.
  assumption.
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

(** *** Logika zdań penetrowalnych *)

Definition Penetrable (P : Prop) : Prop :=
  forall R : Prop, ((P -> R) -> P) -> P.

Lemma Penetrable_True :
  Penetrable True.
(* begin hide *)
Proof.
  unfold Penetrable.
  intros Q _.
  trivial.
Qed.
(* end hide *)

Lemma Penetrable_False :
  Penetrable False.
(* begin hide *)
Proof.
  unfold Penetrable.
  intros Q f.
  apply f.
  intros [].
Qed.
(* end hide *)

Lemma Penetrable_and :
  forall P Q : Prop,
    Penetrable P -> Penetrable Q -> Penetrable (P /\ Q).
(* begin hide *)
Proof.
  unfold Penetrable.
  intros P Q HP HQ R HR.
  split.
  - apply (HP R). intros pr.
    apply HR. intros [p _].
    apply pr.
    assumption.
  - apply (HQ R). intros qr.
    apply HR. intros [_ q].
    apply qr.
    assumption.
Qed.
(* end hide *)

Lemma Penetrable_or_fail :
  forall P Q : Prop,
    Penetrable P -> Penetrable Q -> Penetrable (P \/ Q).
Proof.
  unfold Penetrable.
  intros P Q HP HQ R HR.
  apply HR.
  intros [p | q].
Restart.
  unfold Penetrable.
  intros P Q HP HQ R HR.
  left.
  apply HP with Q; intros pq.
  apply HP with R; intros pr.
  assert (P \/ Q).
  {
    apply HR.
    intros [p | q].
    - apply pr.
      assumption.
    - admit.
  }
Abort.

Lemma Penetrable_impl :
  forall P Q : Prop,
    Penetrable Q -> Penetrable (P -> Q).
(* begin hide *)
Proof.
  unfold Penetrable.
  intros P Q HQ R HR p.
  apply HQ with R. intros qr.
  apply HR; [| assumption].
  intros pq.
  apply qr, pq.
  assumption.
Qed.
(* end hide *)

Lemma Penetrable_not :
  forall P : Prop,
    Penetrable P -> Penetrable (~ P).
(* begin hide *)
Proof.
  intros; apply Penetrable_impl, Penetrable_False.
Qed.
(* end hide *)

Lemma Penetrable_forall :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, Penetrable (P x)) -> Penetrable (forall x : A, P x).
(* begin hide *)
Proof.
  unfold Penetrable.
  intros A P HP R HR x.
  apply HP with R; intros pr.
  apply HR; intros p.
  apply pr, p.
Qed.
(* end hide *)

Lemma Penetrable_exists_fail :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, Penetrable (P x)) -> Penetrable (exists x : A, P x).
Proof.
  unfold Penetrable.
  intros A P HP R HR.
  apply HR; intros [x px].
Abort.

(** * Silna negacja *)

(* begin hide *)
(** TODO: przepisać rozdział o silnej negacji

    Nowy pomysł: to samo co ostatnio, czyli dwie laseczki, ale tym razem
    podkreślić, że silna negacja znaczy "któreś zdanie nie zachodzi",
    zaś słaba negacja znaczy "zdania są ze sobą niekompatybilne".

    Nawiązać do aksjomatu [WLEM] ([P] i [~ P] są ze sobą niekompatybilne,
    ale silna negacja [~ P \/ ~ ~ P] jest tabu).

    Są też negacje pośrednie, co widać przy większej liczbie koniunktów,
    np. dla zdania [P /\ Q /\ R]:
    - [~ P \/ ~ Q \/ ~ R] - silna negacja, "któreś nie zachodzi"
    - [P /\ Q /\ R -> False] - słaba negacja, "wszystkie niekompatybilne"
    - [P /\ Q -> False] - pośrednia negacja, "niektóre niekompatybilne"
*)
(* end hide *)

(** Poznaliśmy uprzednio pewien spójnik, zapisywany wdzięcznym wygibaskiem
    [~], a zwany górnolotnie negacją. Powinniśmy się jednak zastanowić: czy
    spójnik ten jest dla nas zadowalający? Czy pozwala on nam wyrażać nasze
    przemyślenia w najlepszy możliwy sposób?

    Jeżeli twoja odpowiedź brzmi "tak", to uroczyście oświadczam, że wcale
    nie masz racji. Wyobraźmy sobie następującą sytuację: jesteśmy psycho
    patusem, próbującym pod pozorem podrywu poobrażać przeróżne panienki.

    Podbijamy do pierwszej z brzegu, która akurat jest normalną dziewczyną,
    i mówimy: "Hej mała, jesteś gruba i mądra". Nasza oburzona rozmówczyni,
    jako że jest szczupła, odpowiada nam: "Wcale nie jestem gruba. Spadaj
    frajerze".

    Teraz na cel bierzemy kolejną, która siedzi sobie samotnie przy stoliku
    w Starbuniu, popija kawkę z papierowego kubka i z uśmiechem na ustach
    próbuje udowodnić w Coqu jakieś bardzo skomplikowane twierdzenie.
    Podbijamy do niej i mówimy: "Hej mała, jesteś gruba i mądra". Jako, że
    ona też jest szczupła, oburza się i odpowiada nam tak:

    "Czekaj, czekaj, Romeo. Załóżmy, że twój tani podryw jest zgodny z
    prawdą. Gdybym była gruba i mądra, to byłabym w szczególności mądra,
    bo P i Q implikuje Q. Ale gdybym była mądra, to wiedziałabym, żeby
    tyle nie żreć, a skoro tak, to bym nie żarła, więc nie byłabym gruba,
    ale na mocy założenia jestem, więc twój podryw jest sprzeczny. Jeżeli
    nie umiesz logiki, nie idę z tobą do łóżka."

    Widzisz różnicę w tych dwóch odpowiedziach? Pierwsza z nich wydaje nam
    się bardzo naturalna, bo przypomina zaprzeczenia, jakich zwykli ludzie
    używają w codziennych rozmowach. Druga wydaje się zawoalowana i bardziej
    przypomina dowód w Coqu niż codzienne rozmowy. Między oboma odpowiedziami
    jest łatwo zauważalna przepaść.

    Żeby zrozumieć tę przepaść, wprowadzimy pojęcia silnej i słabej negacji.
    W powyższym przykładzie silną negacją posłużyła się pierwsza dziewczyna -
    silną negacją zdania "jesteś gruba i mądra" jest tutaj zdanie "wcale nie
    jestem gruba". Oczywiście jest też druga możliwość silnego zaprzeczenia
    temu zdaniu - "nie jestem mądra" - ale z jakichś powodów to zaprzeczenie
    nie padło. Ciekawe dlaczego? Druga dziewczyna natomiast posłużyła się
    słabą negacją, odpowiadając "gdybym była gruba i mądra, to... (tutaj
    długaśne rozumowanie)... więc sprzeczność".

    Słaba negacja to ta, którą już znamy, czyli Coqowe [not]. Ma ona
    charakter hipotetyczny, gdyż jest po prostu implikacją, której
    konkluzją jest [False]. W rozumowaniach słownych sprowadza się ona
    do schematu "gdyby tak było, to wtedy...".

    Silna negacja to najbardziej bezpośredni sposób zaprzeczenia danemu
    zdaniu. W Coqu nie ma żadnego spójnika, który ją wyraża, bo ma ona
    charakter dość ad hoc - dla każdego zdania musimy sami sobie wymyślić,
    jak brzmi zdanie, które najsilniej mu przeczy. W rozumowaniach słownych
    silna negacja sprowadza się zazwyczaj do schematu "nie jest tak".

    Spróbujmy przetłumaczyć powyższe rozważania na język logiki. Niech
    [P] oznacza "gruba", zaś [Q] - "mądra". Silną negacją zdania [P /\ Q]
    jest zdanie [~ P \/ ~ Q] ("nie gruba lub nie mądra"), zaś jego słabą
    negacją jest [~ (P /\ Q)], czyli [P /\ Q -> False] ("jeżeli gruba i
    mądra, to sprzeczność").

    Zauważmy, że o ile słaba negacja jest uniwersalna, tj. słabą negacją
    [P /\ Q] zawsze jest [~ (P /\ Q)], to silna negacja jest ad hoc w tym
    sensie, że gdyby [P] było postaci [P1 /\ P2], to wtedy silną negacją
    [P /\ Q] nie jest już [~ P \/ ~ Q], a [~ P1 \/ ~ P2 \/ ~ Q] - żeby
    uzyskać silną negację, musimy zanegować [P] silnie, a nie słabo.

    Dlaczego silna negacja jest silna, a słaba jest słaba, tzn. dlaczego
    nazwaliśmy je tak a nie inaczej? Wyjaśnia to poniższe twierdzenie oraz
    następująca po nim beznadziejna próba udowodnienia analogicznego
    twierdzenia z implikacją idącą w drugą stronę. *)

Lemma strong_to_weak_and :
  forall P Q : Prop, ~ P \/ ~ Q -> ~ (P /\ Q).
Proof.
  intros P Q Hor Hand.
  destruct Hand as [p q].
  destruct Hor as [notp | notq].
    apply notp. assumption.
    apply notq. assumption.
Qed.

(** Jak widać, silna negacja koniunkcji pociąga za sobą jej słabą negację.
    Powód tego jest prosty: jeżeli jeden z koniunktów nie zachodzi, ale
    założymy, że oba zachodzą, to w szczególności każdy z nich zachodzi
    osobno i mamy sprzeczność.

    A czy implikacja w drugą stronę zachodzi? *)

Lemma weak_to_strong_and :
  forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros P Q notpq. left. intro p. apply notpq. split.
    assumption.
Abort.

(** Jak widać, nie udało nam się udowodnić odwrotnej implikacji i to wcale
    nie dlatego, że jesteśmy mało zdolni - po prostu konstruktywnie nie da
    się tego zrobić.

    Powód tego jest prosty: jeżeli wiemy, że [P] i [Q] razem prowadzą do
    sprzeczności, to wiemy zdecydowanie za mało. Mogą być dwa powody:
    - [P] i [Q] mogą bez problemu zachodzić osobno, ale być sprzeczne
      razem
    - nawet jeżeli któryś z koniunktów prowadzi do sprzeczności, to nie
      wiemy, który

    Żeby zrozumieć pierwszą możliwość, niech [P] oznacza "siedzę", a [Q] -
    "stoję". Rozważmy zdanie [P /\ Q], czyli "siedzę i stoję". Żeby nie było
    za łatwo załóżmy też, że znajdujesz się po drugiej stronie kosmosu i mnie
    nie widzisz.

    Oczywiście nie mogę jednocześnie siedzieć i stać, gdyż czynności te się
    wykluczają, więc możesz skonkludować, że [~ (P /\ Q)]. Czy możesz jednak
    wywnioskować stąd, że [~ P \/ ~ Q], czyli że "nie siedzę lub nie stoję"?
    Konstruktywnie nie, bo będąc po drugiej stronie kosmosu nie wiesz, której
    z tych dwóch czynności nie wykonuję.

    Z drugim przypadkiem jest tak samo, jak z końcówką powyższego przykładu:
    nawet jeżeli zdania [P] i [Q] się wzajemnie nie wykluczają i niesłuszność
    [P /\ Q] wynika z tego, że któryś z koniunktów nie zachodzi, to możemy po
    prostu nie wiedzieć, o który z nich chodzi.

    Żeby jeszcze wzmocnić nasze zrozumienie, spróbujmy w zaskakujący sposób
    rozwinąć definicję (słabej) negacji dla koniunkcji: *)

Lemma not_and_surprising :
  forall P Q : Prop, ~ (P /\ Q) <-> (P -> ~ Q).
Proof.
  split.
    intros npq p q. apply npq. split.
      assumption.
      assumption.
    intros pnq pq. destruct pq as [p q]. apply pnq.
      assumption.
      assumption.
Qed.

(** I jeszcze raz... *)

Lemma not_and_surprising' :
  forall P Q : Prop, ~ (P /\ Q) <-> (Q -> ~ P).
(* begin hide *)
Proof.
  split.
    intros npq p q. apply npq. split.
      assumption.
      assumption.
    intros qnp pq. destruct pq as [p q]. apply qnp.
      assumption.
      assumption.
Qed.
(* end hide *)

(** Jak (mam nadzieję) widać, słaba negacja koniunkcji nie jest niczym
    innym niż stwierdzeniem, że oba koniunkty nie mogą zachodzić razem.
    Jest to więc coś znacznie słabszego, niż stwierdzenie, że któryś z
    koniunktów nie zachodzi z osobna. *)

Lemma mid_neg_conv :
  forall P Q : Prop, ~ (P /\ Q) -> ((P -> ~ Q) /\ (Q -> ~ P)).
Proof.
  firstorder.
Qed.

(** Jak napisano w Piśmie, nie samą koniunkcją żyje człowiek. Podumajmy
    więc, jak wygląda silna negacja dysjunkcji. Jeżeli chcemy dosadnie
    powiedzieć, że [P \/ Q] nie zachodzi, to najprościej powiedzieć:
    [~ P /\ ~ Q]. Słaba negacja dysjunkcji ma zaś rzecz jasna postać
    [~ (P \/ Q)]. *)

Lemma strong_to_weak_or :
  forall P Q : Prop, ~ P /\ ~ Q -> ~ (P \/ Q).
Proof.
  do 2 destruct 1; contradiction.
Qed.

(** Co jednak dość ciekawe, silna negacja nie zawsze jest silniejsza
    od słabej (ale z pewnością nie może być od niej słabsza - gdyby
    mogła, to nazywałaby się inaczej). W przypadku dysjunkcji obie
    negacje są równoważne, co obrazuje poniższe twierdzenie, które
    głosi, że słaba negacja implikuje silną (a to razem z powyższym
    daje równoważność): *)

Lemma weak_to_strong_or :
  forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  split; intro; apply H; [left | right]; assumption.
Qed.

(** Wynika to z faktu, że [~ P /\ ~ Q] to tak naprawdę para implikacji
    [P -> False] i [Q -> False], zaś [~ (P \/ Q)] to... gdy pomyślimy
    nad tym odpowiednio mocno... ta sama para implikacji. Jest tak
    dlatego, że jeżeli [P \/ Q] implikuje [R], to umieć wyprodukować
    [R] musimy zarówno z samego [P], jak i z samego [Q]. *)

Lemma deMorgan_dbl_neg :
  (forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q) <->
  (forall P : Prop, ~ ~ P -> P).
Proof.
  split.
    intros deMorgan P H.
Abort.

(** * Logika klasyczna jako logika silnych i słabych spójników *)

(** ** Silna implikacja *)

Definition simpl (P Q : Prop) : Prop := ~ P \/ Q.

Lemma impl_simpl :
  forall P Q : Prop,
    simpl P Q -> (P -> Q).
(* begin hide *)
Proof.
  unfold simpl. intros P Q [np | q] p.
  - contradiction.
  - assumption.
Qed.
(* end hide *)

Lemma simpl_simpl_impl :
  LEM ->
    forall P Q : Prop,
      simpl (simpl P Q) (P -> Q).
(* begin hide *)
Proof.
  unfold LEM, simpl.
  intros lem P Q.
  destruct (lem P) as [p | np], (lem Q) as [q | nq].
  - right. intros _. assumption.
  - left. intros [np | q]; contradiction.
  - right. intros _. assumption.
  - right. intros p. contradiction.
Qed.
(* end hide *)

Lemma simpl_impl_classically :
  LEM ->
    forall P Q : Prop,
      (P -> Q) -> simpl P Q.
(* begin hide *)
Proof.
  unfold LEM, simpl.
  intros lem P Q f.
  destruct (lem P) as [p | np].
  - right. apply f. assumption.
  - left. assumption.
Qed.
(* end hide *)

Lemma simpl_impl_tabu :
  (forall P Q : Prop, (P -> Q) -> simpl P Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, simpl.
  intros simpl_impl P.
  apply or_comm. apply simpl_impl. intros p. trivial.
Qed.
(* end hide *)

(** ** Słaba implikacja *)

Definition wimpl (P Q : Prop) : Prop := ~ Q -> ~ P.

Lemma wimpl_alternative :
  forall P Q : Prop, wimpl P Q <-> ~ (P /\ ~ Q).
(* begin hide *)
Proof. unfold wimpl; tauto. Qed.
(* end hide *)

Lemma wimpl_impl :
  forall P Q : Prop,
    (P -> Q) -> wimpl P Q.
(* begin hide *)
Proof.
  unfold wimpl. intros P Q f nq p.
  apply nq, f, p.
Qed.
(* end hide *)

Lemma impl_wimpl_irrefutable :
  forall P Q : Prop,
    ~ ~ (wimpl P Q -> (P -> Q)).
(* begin hide *)
Proof.
  unfold wimpl.
  intros P Q H. apply H.
  intros f p. exfalso. apply f; [| assumption].
  intros q. apply H. intros _ _. assumption.
Qed.
(* end hide *)

Lemma wimpl_impl_classically :
  LEM ->
    forall P Q : Prop,
      wimpl P Q -> (P -> Q).
(* begin hide *)
Proof.
  unfold LEM, wimpl.
  intros lem P Q f p.
  destruct (lem Q) as [q | nq].
  - assumption.
  - contradict p. apply f. assumption.
Qed.
(* end hide *)

Lemma impl_wimpl_wimpl :
  forall P Q : Prop,
    wimpl (P -> Q) (wimpl P Q).
(* begin hide *)
Proof.
  unfold LEM, wimpl.
  intros P Q f g. apply f.
  intros nq p. apply nq, g. assumption.
Qed.
(* end hide *)

Lemma impl_wimpl_tabu :
  (forall P Q : Prop, wimpl P Q -> (P -> Q)) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, wimpl.
  intros impl_wimpl P.
  specialize (impl_wimpl (~ ~ (P \/ ~ P)) (P \/ ~ P)).
  apply impl_wimpl.
  - tauto.
  - apply Irrefutable_LEM.
Qed.
(* end hide *)

(** ** Słaba dysjunkcja *)

Definition wor (P Q : Prop) : Prop := ~ P -> Q.

Lemma wor_or :
  forall P Q : Prop,
    P \/ Q -> wor P Q.
(* begin hide *)
Proof.
  unfold wor. intros P Q [p | q] np.
  - contradiction.
  - assumption.
Qed.
(* end hide *)

Lemma wor_introl :
  forall P Q : Prop,
    P -> wor P Q.
(* begin hide *)
Proof.
  unfold wor. intros P Q p np. contradiction.
Qed.
(* end hide *)

Lemma wor_intror :
  forall P Q : Prop,
    Q -> wor P Q.
(* begin hide *)
Proof.
  unfold wor. intros P Q q _. assumption.
Qed.
(* end hide *)

Lemma wor_False_l :
  forall P : Prop,
    wor False P <-> P.
(* begin hide *)
Proof.
  unfold wor. intros P; split.
  - intros p. apply p. intros f. contradiction.
  - intros p _. assumption.
Qed.
(* end hide *)

Lemma wor_False_r :
  LEM ->
    forall P : Prop,
      wor P False <-> P.
(* begin hide *)
Proof.
  unfold LEM, wor.
  intros lem P; split.
  - intros nnp. destruct (lem P) as [p | np].
    + assumption.
    + contradiction.
  - intros p np. contradiction.
Qed.
(* end hide *)

Lemma wor_True_l :
  forall P : Prop,
    wor True P <-> True.
(* begin hide *)
Proof.
  unfold wor. intros P; split.
  - intros _. trivial.
  - intros _ nt. contradiction.
Qed.
(* end hide *)

Lemma wor_True_r :
  forall P : Prop,
    wor P True <-> True.
(* begin hide *)
Proof.
  unfold wor. intros P; split; intros _; trivial.
Qed.
(* end hide *)

Lemma wor_assoc :
  forall P Q R : Prop,
    wor (wor P Q) R <-> wor P (wor Q R).
(* begin hide *)
Proof.
  unfold wor. intros P Q R; split.
  - intros f np nq. apply f. intros g. apply nq, g. assumption.
  - intros f ng. apply f.
    + intros p. apply ng. intros np. contradiction.
    + intros q. apply ng. intros _. assumption.
Qed.
(* end hide *)

Lemma wor_comm :
  LEM ->
    forall P Q : Prop,
      wor P Q <-> wor Q P.
(* begin hide *)
Proof.
  unfold LEM, wor.
  intros lem P Q; split.
  - intros f nq. destruct (lem P) as [p | np].
    + assumption.
    + contradict nq. apply f. assumption.
  - intros f np. destruct (lem Q) as [q | nq].
    + assumption.
    + contradict np. apply f. assumption.
Qed.
(* end hide *)

Lemma or_wor_classically :
  LEM ->
    forall P Q : Prop,
      wor P Q -> P \/ Q.
(* begin hide *)
Proof.
  unfold LEM, wor.
  intros lem P Q f.
  destruct (lem P) as [p | np].
  - left. assumption.
  - destruct (lem Q) as [q | nq].
    + right. assumption.
    + right. apply f. intros p. contradiction.
Qed.
(* end hide *)

Lemma or_wor_tabu :
  (forall P Q : Prop, wor P Q -> P \/ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, wor.
  intros or_wor P.
  apply or_wor. intros np. assumption.
Qed.
(* end hide *)

(** ** Słaba dysjunkcja przemienna *)

Definition wor2 (P Q : Prop) : Prop := (~ P -> Q) \/ (~ Q -> P).

Lemma wor2_or :
  forall P Q : Prop,
    P \/ Q -> wor2 P Q.
(* begin hide *)
Proof.
  unfold wor2. intros P Q [p | q].
  - right. intros _. assumption.
  - left. intros _. assumption.
Qed.
(* end hide *)

Lemma wor_wor2 :
  LEM ->
    forall P Q : Prop,
      wor2 P Q -> wor P Q.
(* begin hide *)
Proof.
  unfold LEM, wor2, wor.
  intros lem P Q [f | f] np.
  - apply f. assumption.
  - destruct (lem Q) as [q | nq].
    + assumption.
    + contradict np. apply f. assumption.
Qed.
(* end hide *)

Lemma wor2_wor :
  forall P Q : Prop,
    wor P Q -> wor2 P Q.
(* begin hide *)
Proof.
  unfold wor2, wor.
  intros P Q f. left. assumption.
Qed.
(* end hide *)

Lemma wor2_introl :
  forall P Q : Prop,
    P -> wor2 P Q.
(* begin hide *)
Proof.
  unfold wor2. intros P Q p. right. intros _. assumption.
Qed.
(* end hide *)

Lemma wor2_intror :
  forall P Q : Prop,
    Q -> wor2 P Q.
(* begin hide *)
Proof.
  unfold wor2. intros P Q q. left. intros _. assumption.
Qed.
(* end hide *)

Lemma wor2_False_l :
  LEM ->
    forall P : Prop,
      wor2 False P <-> P.
(* begin hide *)
Proof.
  unfold LEM, wor2.
  intros lem P; split.
  - intros [p | f].
    + apply p. intros f. contradiction.
    + destruct (lem P) as [p | np].
      * assumption.
      * contradiction.
  - intros p. left. intros _. assumption.
Qed.
(* end hide *)

Lemma wor2_False_r :
  LEM ->
    forall P : Prop,
      wor2 P False <-> P.
(* begin hide *)
Proof.
  unfold LEM, wor2.
  intros lem P; split.
  - intros [nnp | p].
    + destruct (lem P) as [p | np].
      * assumption.
      * contradiction.
    + apply p. intros f. assumption.
  - intros p. right. intros _. assumption.
Qed.
(* end hide *)

Lemma wor2_True_l :
  forall P : Prop,
    wor2 True P <-> True.
(* begin hide *)
Proof.
  unfold wor2. intros P; split.
  - intros _. trivial.
  - intros _. right. intros _. trivial.
Qed.
(* end hide *)

Lemma wor2_True_r :
  forall P : Prop,
    wor2 P True <-> True.
(* begin hide *)
Proof.
  unfold wor2. intros P; split; intros _.
  - trivial.
  - left. intros _. trivial.
Qed.
(* end hide *)

Lemma wor2_comm :
  forall P Q : Prop,
    wor2 P Q <-> wor2 Q P.
(* begin hide *)
Proof.
  unfold wor2. intros P Q. split.
  - intros [q | p]; [right | left]; assumption.
  - intros [p | q]; [right | left]; assumption.
Qed.
(* end hide *)

Lemma wor2_assoc :
  LEM ->
    forall P Q R : Prop,
      wor2 (wor2 P Q) R <-> wor2 P (wor2 Q R).
(* begin hide *)
Proof.
  unfold LEM.
  intros lem P Q R; split.
  - intros [r | npq].
    + unfold wor2. left. intros _. left. intros _. apply r. unfold wor2. admit.
    + red. left. intros np. red. right. intros nr.
      destruct (npq nr) as [q | p].
      * apply q. assumption.
      * contradict np. apply p. intros q.
Abort.
(* end hide *)

Lemma or_wor2_classically :
  LEM ->
    forall P Q : Prop,
      wor2 P Q -> P \/ Q.
(* begin hide *)
Proof.
  unfold LEM, wor2.
  intros lem P Q f.
  destruct (lem P) as [p | np].
  - left. assumption.
  - destruct (lem Q) as [q | nq].
    + right. assumption.
    + destruct f as [f | f].
      * right. apply f. intros p. contradiction.
      * left. apply f. intros q. contradiction.
Qed.
(* end hide *)

Lemma or_wor2_tabu :
  (forall P Q : Prop, wor2 P Q -> P \/ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, wor2.
  intros or_wor2 P.
  apply or_wor2. left. intros np. assumption.
Qed.
(* end hide *)

(** ** Słaba koniunkcja *)

Definition aand (P Q : Prop) : Prop := ~ (~ P \/ ~ Q).

Lemma and_aand :
  forall P Q : Prop,
    P /\ Q -> aand P Q.
(* begin hide *)
Proof.
  unfold aand.
  intros P Q [p q] [np | nq].
  - apply np. assumption.
  - apply nq. assumption.
Qed.
(* end hide *)

Lemma aand_and_classically :
  LEM ->
    forall P Q : Prop,
      aand P Q -> P /\ Q.
(* begin hide *)
Proof.
  unfold LEM, aand.
  intros lem P Q f; split.
  - destruct (lem P) as [p | np].
    + assumption.
    + contradict f. left. assumption.
  - destruct (lem Q) as [q | nq].
    + assumption.
    + contradict f. right. assumption.
Qed.
(* end hide *)

Lemma aand_and_tabu :
  (forall P Q : Prop, aand P Q -> P /\ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM, aand.
  intros aand_and P.
  destruct (aand_and (P \/ ~ P) True).
  - intros [f | f].
    + eapply Irrefutable_LEM. eassumption.
    + contradiction.
  - assumption.
Qed.
(* end hide *)

Lemma aand_elim :
  forall P Q R : Prop,
    (P -> R) -> (Q -> R) -> (~ ~ R -> R) -> ~ (~ P /\ ~ Q) -> R.
(* begin hide *)
Proof.
  intros P Q R pr qr nnrr pq.
  apply nnrr. intro nr.
  apply pq. split.
  - intro p. apply nr, pr, p.
  - intro q. apply nr, qr, q.
Qed.
(* end hide *)

(** ** Silna równoważność *)

Definition siff (P Q : Prop) : Prop := P /\ Q \/ ~ P /\ ~ Q.

Lemma iff_siff :
  forall P Q : Prop,
    siff P Q -> P <-> Q.
(* begin hide *)
Proof.
  unfold siff. intros P Q [[p q] | [np nq]].
  - split; intros _; assumption.
  - split; intros; contradiction.
Qed.
(* end hide *)

Lemma siff_iff :
  LEM ->
    forall P Q : Prop,
      P <-> Q -> siff P Q.
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P Q [pq qp].
  destruct (lem P) as [p | np], (lem Q) as [q | nq].
  - left. split; assumption.
  - contradiction nq. apply pq. assumption.
  - contradiction np. apply qp. assumption.
  - right. split; assumption.
Qed.
(* end hide *)

Lemma siff_iff_iff :
  LEM ->
    forall P Q : Prop,
      P <-> Q <-> siff P Q.
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P Q. split.
  - apply siff_iff. assumption.
  - apply iff_siff.
Qed.
(* end hide *)

Lemma siff_siff_iff :
  LEM ->
    forall P Q : Prop,
      siff (siff P Q) (P <-> Q).
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P Q.
  destruct (lem P) as [p | np], (lem Q) as [q | nq].
  - left. split.
    + left. split; assumption.
    + split; intros _; assumption.
  - right. split.
    + intros [[] | []]; contradiction.
    + intros [pq qp]. contradict nq. apply pq. assumption.
  - right. split.
    + intros [[] | []]; contradiction.
    + intros [pq qp]. contradict np. apply qp. assumption.
  - left. split.
    + right. split; assumption.
    + split; intros; contradiction.
Qed.
(* end hide *)

Lemma siff_xor :
  forall P Q : Prop,
    siff P Q -> xor P Q -> False.
(* begin hide *)
Proof.
  unfold siff, xor.
  intros P Q [[p q] | [np nq]] [[p' nq'] | [np' q']]; contradiction.
Qed.
(* end hide *)

Lemma siff_id :
  LEM ->
    forall P : Prop,
      siff P P.
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P.
  destruct (lem P) as [p | np].
  - left. split; assumption.
  - right. split; assumption.
Qed.
(* end hide *)

Lemma siff_comm :
  LEM ->
    forall P Q : Prop,
      siff (siff P Q) (siff Q P).
(* begin hide *)
Proof.
  unfold LEM, siff.
  intros lem P Q.
  destruct (lem P) as [p | np], (lem Q) as [q | nq]; firstorder.
Qed.
(* end hide *)

Lemma siff_assoc :
  LEM ->
    forall P Q R : Prop,
      siff (siff (siff P Q) R) (siff P (siff Q R)).
(* begin hide *)
Proof.
  unfold LEM.
  intros lem P Q R.
  specialize (lem P) as lemP.
  specialize (lem Q) as lemQ.
  specialize (lem R) as lemR.
  clear lem. unfold siff. tauto.
Qed.
(* end hide *)

(** ** Silna antyimplikacja *)

Definition snimpl (P Q : Prop) : Prop := P /\ ~ Q.

(* TODO: jakieś lematy *)

Definition NI : Prop :=
  forall P Q : Prop, ~ (P -> Q) -> P /\ ~ Q.

Lemma NI_LEM :
  NI -> LEM.
(* begin hide *)
Proof.
  unfold NI, LEM.
  intros NI P.
  destruct (NI (P \/ ~ P) False) as [lem _].
  - apply Irrefutable_LEM.
  - assumption.
Qed.
(* end hide *)

Definition wxor (P Q : Prop) : Prop := ~ (P <-> Q).

Lemma wxor_irrefl :
  forall P : Prop, ~ wxor P P.
(* begin hide *)
Proof.
  unfold wxor. intros A f.
  apply f. split; trivial.
Qed.
(* end hide *)

Lemma wxor_comm :
  forall P Q : Prop, wxor P Q -> wxor Q P.
(* begin hide *)
Proof.
  unfold wxor. intros P Q f g.
  apply f. apply iff_symm. assumption.
Qed.
(* end hide *)

Lemma wxor_cotrans :
  LEM ->
    (forall P Q R : Prop, wxor P Q -> wxor P R \/ wxor Q R).
(* begin hide *)
Proof.
  unfold LEM, wxor. intros lem P Q R f.
  destruct (lem (P <-> R)) as [HR | HR]; cycle 1.
  - left. assumption.
  - destruct (lem (Q <-> R)) as [HQ | HQ]; cycle 1.
    + right. assumption.
    + contradiction f. apply iff_trans with R.
      * assumption.
      * apply iff_symm. assumption.
Qed.
(* end hide *)

Lemma wxor_assoc :
  forall P Q R : Prop,
    wxor P (wxor Q R) <-> wxor (wxor P Q) R.
(* begin hide *)
Proof.
  unfold wxor. split; firstorder.
Qed.
(* end hide *)

Lemma wxor_xor :
  forall P Q : Prop, xor P Q -> wxor P Q.
(* begin hide *)
Proof.
  unfold xor, wxor.
  intros P Q [[p nq] | [np q]].
  - intros f. apply nq, f. assumption.
  - intros f. apply np, f. assumption.
Qed.
(* end hide *)

Lemma xor_wxor_classically :
  LEM ->
    forall P Q : Prop, wxor P Q -> xor P Q.
(* begin hide *)
Proof.
  unfold LEM, xor, wxor.
  intros lem P Q npq.
  destruct (lem P) as [p | np].
  - left. split; [assumption |]. intros q. apply npq. split; trivial.
  - right. split; [assumption |]. destruct (lem Q) as [q | nq].
    + assumption.
    + exfalso. apply npq. split; intros; contradiction.
Qed.
(* end hide *)

Lemma wxor_False_r_classically :
  LEM ->
    forall P : Prop, wxor P False <-> P.
(* begin hide *)
Proof.
  unfold LEM, wxor, iff.
  intros lem P. split.
  - intros f. destruct (lem P) as [p | np].
    + assumption.
    + contradict f. split; intros; contradiction.
  - intros p [np _]. contradiction.
Qed.
(* end hide *)

Lemma wxor_False_l_classically :
  LEM ->
    forall P : Prop, wxor False P <-> P.
(* begin hide *)
Proof.
  unfold LEM, wxor.
  intros lem P; split.
  - intros H. destruct (lem P) as [p | np].
    + assumption.
    + exfalso. apply H. split; [intros [] | contradiction].
  - intros p f. apply f. assumption.
Qed.
(* end hide *)

Lemma wxor_True_l :
  forall P : Prop, wxor True P <-> ~ P.
(* begin hide *)
Proof.
  unfold wxor. tauto.
Qed.
(* end hide *)

Lemma wxor_True_r :
  forall P : Prop, wxor P True <-> ~ P.
(* begin hide *)
Proof.
  unfold wxor. tauto.
Qed.
(* end hide *)

(** ** Klasyczna dysjunkcja (TODO) *)

Definition cor (P Q : Prop) : Prop :=
  ~ ~ (P \/ Q).

Lemma cor_in_l :
  forall P Q : Prop,
    P -> cor P Q.
(* begin hide *)
Proof.
  unfold cor. intros P Q p f.
  apply f. left. assumption.
Qed.
(* end hide *)

Lemma cor_in_r :
  forall P Q : Prop,
    Q -> cor P Q.
(* begin hide *)
Proof.
  unfold cor. intros P Q p f.
  apply f. right. assumption.
Qed.
(* end hide *)

Lemma cor_assoc :
  forall P Q R : Prop,
    cor (cor P Q) R <-> cor P (cor Q R).
(* begin hide *)
Proof.
  unfold cor. intros P Q; split; intros f g.
  - apply f. intros h. apply g. right. intros i. destruct h as [nnpq | r].
    + apply nnpq. intros [p | q].
      * apply g. left. assumption.
      * apply i. left. assumption.
    + apply i. right. assumption.
  - apply g. left. intros npq. apply f. intros [p | nnqr].
    + apply npq. left. assumption.
    + apply nnqr. intros [q | r].
      * apply npq. right. assumption.
      * apply g. right. assumption.
Qed.
(* end hide *)

Lemma cor_comm :
  forall P Q : Prop,
    cor P Q -> cor Q P.
(* begin hide *)
Proof.
  unfold cor. intros P Q f g.
  apply f. intros [p | q]; apply g.
  - right. assumption.
  - left. assumption.
Qed.
(* end hide *)

Lemma cor_True_l :
  forall P : Prop,
    cor True P <-> True.
(* begin hide *)
Proof.
  unfold cor. intros P; split.
  - intros _. trivial.
  - intros _ f. apply f. left. trivial.
Qed.
(* end hide *)

Lemma cor_True_r :
  forall P : Prop,
    cor P True <-> True.
(* begin hide *)
Proof.
  unfold cor. intros P; split.
  - intros _. trivial.
  - intros _ f. apply f. right. trivial.
Qed.
(* end hide *)

Lemma cor_False_l :
  forall P : Prop,
    cor False P <-> ~ ~ P.
(* begin hide *)
Proof.
  unfold cor. intros P; split.
  - intros f np. apply f. intros [? | p]; contradiction.
  - intros nnp f. apply nnp. intros p. apply f. right. assumption.
Qed.
(* end hide *)

Lemma cor_False_r :
  forall P : Prop,
    cor P False <-> ~ ~ P.
(* begin hide *)
Proof.
  unfold cor. intros P; split.
  - intros f np. apply f. intros [? | p]; contradiction.
  - intros nnp f. apply nnp. intros p. apply f. left. assumption.
Qed.
(* end hide *)

Lemma cor_or :
  forall P Q : Prop,
    P \/ Q -> cor P Q.
(* begin hide *)
Proof.
  unfold cor. intros P Q [p | q] npq.
  - apply npq. left. assumption.
  - apply npq. right. assumption.
Qed.
(* end hide *)

Lemma cor_LEM :
  forall P : Prop,
    cor P (~ P).
(* begin hide *)
Proof.
  unfold cor.
  intros P f.
  apply f. right. intros p.
  apply f. left. assumption.
Qed.
(* end hide *)

Lemma or_cor_classically :
  LEM -> forall P Q : Prop, cor P Q -> P \/ Q.
(* begin hide *)
Proof.
  unfold LEM, cor.
  intros lem P Q f. destruct (lem (P \/ Q)).
  - assumption.
  - contradiction.
Qed.
(* end hide *)

Lemma or_cor_tabu :
  (forall P Q : Prop, cor P Q -> P \/ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold cor, LEM.
  intros or_cor P. apply or_cor. tauto.
Qed.
(* end hide *)

Lemma cor_spec :
  forall P Q : Prop,
    cor P Q <-> ~ (~ P /\ ~ Q).
(* begin hide *)
Proof.
  split.
  - intros H [np nq]. apply H. intros [p | q].
    + apply np, p.
    + apply nq, q.
  - intros pq npq. apply pq. split.
    + intro p. apply npq. left. assumption.
    + intro q. apply npq. right. assumption.
Qed.
(* end hide *)

Lemma cor_wor :
  forall P Q : Prop,
    wor P Q -> cor P Q.
(* begin hide *)
Proof.
  unfold wor, cor.
  intros P Q f npq. apply npq. right. apply f.
  intros p. apply npq. left. assumption.
Qed.
(* end hide *)

Lemma cor_wor2 :
  forall P Q : Prop,
    wor2 P Q -> cor P Q.
(* begin hide *)
Proof.
  unfold wor2, cor.
  intros P Q [f | f] npq.
  - apply npq. right. apply f. intros p. apply npq. left. assumption.
  - apply npq. left. apply f. intros p. apply npq. right. assumption.
Qed.
(* end hide *)

(** ** Bonus: klasyczna koń-junkcja (TODO) *)

Lemma cand_and_LEM :
  (forall P Q : Prop, ~ ~ (P /\ Q) -> P /\ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM. intros H P.
  destruct (H (P \/ ~ P) True).
  - intros f. apply f. split.
    + right. intros p. apply f. split.
      * left. assumption.
      * trivial.
    + trivial.
  - assumption.
Qed.
(* end hide *)

(** ** Bonus 2: klasyczny kwantyfikator egzystencjalny (TODO) *)

Lemma weak_ex_elim :
  forall (A : Type) (P : A -> Prop) (R : Prop),
    (forall x : A, P x -> R) -> (~ ~ R -> R) ->
      ~ (forall x : A, ~ P x) -> R.
(* begin hide *)
Proof.
  intros A P R Hpr Hnr Hnp.
  apply Hnr. intro nr.
  apply Hnp. intros x np.
  apply nr, (Hpr x), np.
Qed.
(* end hide *)

(** ** Słaby kwantyfikator egzystencjalny *)

Definition wexists {A : Type} (P : A -> Prop) : Prop :=
  ~ forall x : A, ~ P x.

Lemma wexists_exists :
  forall {A : Type} (P : A -> Prop),
    ex P -> wexists P.
(* begin hide *)
Proof.
  unfold wexists.
  intros A P [x p] H.
  apply (H x). assumption.
Qed.
(* end hide *)

Lemma exists_wexists_classically :
  LEM ->
    forall {A : Type} (P : A -> Prop),
      wexists P -> ex P.
(* begin hide *)
Proof.
  unfold LEM, wexists.
  intros lem A P H.
  destruct (lem (exists y, P y)) as [e | ne].
  - assumption.
  - exfalso. apply H. intros x p. apply ne. exists x. assumption.
Qed.
(* end hide *)

Lemma exists_wexists_tabu :
  (forall {A : Type} (P : A -> Prop), wexists P -> ex P)
    ->
  LEM.
(* begin hide *)
Proof.
  unfold LEM, wexists.
  intros exists_wexists P.
  specialize (exists_wexists bool (fun b => if b then P else ~ P)); cbn in *.
  destruct exists_wexists as [[] H].
  - intros H.
    specialize (H true) as np; cbn in np.
    specialize (H false) as nnp; cbn in nnp.
    contradiction.
  - left. assumption.
  - right. assumption.
Qed.
(* end hide *)

(** ** Słaby kwantyfikator uniwersalny *)

Definition wforall {A : Type} (P : A -> Prop) : Prop :=
  ~ exists x : A, ~ P x.

Lemma wforall_forall :
  forall {A : Type} (P : A -> Prop),
    (forall x : A, P x) -> wforall P.
(* begin hide *)
Proof.
  unfold wforall.
  intros A P H [x np].
  apply np, H.
Qed.
(* end hide *)

Lemma forall_wforall_classically :
  LEM ->
    forall {A : Type} (P : A -> Prop),
      wforall P -> forall x : A, P x.
(* begin hide *)
Proof.
  unfold LEM, wforall.
  intros lem A P H x.
  destruct (lem (P x)) as [p | np].
  - assumption.
  - contradict H. exists x. assumption.
Qed.
(* end hide *)

Lemma forall_wforall_tabu :
  (forall {A : Type} (P : A -> Prop), wforall P -> forall x : A, P x)
    ->
  LEM.
(* begin hide *)
Proof.
  unfold LEM, wforall.
  intros forall_wforall P.
  apply (forall_wforall unit (fun _ => P \/ ~ P)).
  - intros [_ H]. apply Irrefutable_LEM in H. assumption.
  - exact tt.
Qed.
(* end hide *)

(** ** Wymyśl to sam... *)

(** **** Ćwiczenie *)

(** Jeżeli jeszcze ci mało, spróbuj sam wymyślić jakieś
    spójniki logiczne, których nie ma w logice konstruktywnej
    ani klasycznej.

    Zastanów się, czy taki spójnik ma sens matematyczny, czy nadaje się do
    użytku jedynie w językach naturalnych. Da się go jakoś wyrazić za pomocą
    znanych nam spójników, czy nie bardzo? Twój spójnik jest fajny czy głupi?
    Użyteczny czy bezużyteczny? *)

(** * Stary podrozdział, do naprawy *)

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

Lemma Irrefutable_MI :
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
(* begin hide *)
Proof.
  intros P Q H. destruct H as [pq | npnq].
    destruct pq as [p q]. split.
      intro p'. assumption.
      intro q'. assumption.
    destruct npnq as [np nq]. split.
      intro p. contradiction.
      intro q. contradiction.
Qed.
(* end hide *)

Lemma material_equivalence :
  forall P Q : Prop, (P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q).
Proof.
  intros P Q [pq qp]. left. split.
    apply qp. apply pq.
Restart.
  intros P Q [pq qp]. right. split.
    intro p.
Abort.

Lemma Irrefutable_ME :
  forall P Q : Prop, ~ ~ ((P <-> Q) -> (P /\ Q) \/ (~ P /\ ~ Q)).
(* begin hide *)
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
(* end hide *)

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

(** * Paradoks pijoka *)

Lemma drinkers_paradox :
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
    [P -> Q <-> ~ P \/ Q], a więc że implikacja jest prawdziwa gdy jej
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

(** * Klasyczna logika pierwszego rzędu (TODO) *)

(** TODO SUPER WAŻNE: logika klasyczna to nie tylko rachunek zdań, ale też kwantyfikatory! *)
Lemma not_not_forall :
  (forall (A : Type) (P : A -> Prop),
    (forall x : A, ~ ~ P x) -> (~ ~ forall x : A, P x))
    <->
  (~ ~ forall P : Prop, P \/ ~ P).
(* begin hide *)
Proof.
  split.
  - intros dns nlem. apply dns in nlem.
    + assumption.
    + tauto.
  - intros nnlem A P nnp np. apply nnlem. intros lem.
    apply np. intros x. destruct (lem (P x)).
    + assumption.
    + contradiction nnp with x.
Qed.
(* end hide *)

(** ** Double negation shift *)

(** Wzięte z https://ncatlab.org/nlab/show/double-negation+shift *)

Definition DNS : Prop :=
  forall (A : Type) (P : A -> Prop),
    (forall x : A, ~ ~ P x) -> ~ ~ forall x : A, P x.

Lemma DNS_not_not_LEM :
  DNS <-> ~ ~ LEM.
(* begin hide *)
Proof.
  unfold DNS, LEM.
  split.
    intros DNS H.
      specialize (DNS Prop (fun P => P \/ ~ P) Irrefutable_LEM).
      apply DNS. intro H'. contradiction.
    intros NNLEM A P H1 H2. apply NNLEM. intro LEM.
      assert (forall x : A, P x).
        intro x. destruct (LEM (P x)).
          assumption.
          specialize (H1 x). contradiction.
        contradiction.
Qed.
(* end hide *)

(** Klasyczna logika wyższego rzędu (TODO) *)

(** * Aksjomaty i pojęcie "tabu" (TODO) *)

(** * Interpretacja obliczeniowa logiki klasycznej, a raczej jej brak (TODO) *)

(** Tu opisać, jak aksjomaty mają się do prawa zachowania informacji i zawartości
    obliczeniowej. *)

(** * Porównanie logiki konstruktywnej i klasycznej (TODO) *)

(** * Uniwersum [SProp] *)

(** * Konkluzja (TODO) *)

(** ** Ściąga *)

(** * Zadania (TODO) *)

(** Wyrzucić zadania mącące (mieszające typy i zdania) *)

Require Classical.

Section ClassicalExercises.

Import Classical.

Hypotheses P Q R S : Prop.

(** Komenda [Require Import] pozwala nam zaimportować żądany
    moduł z biblioteki standardowej Coqa. Dzięki temu będziemy
    mogli używać zawartych w nim definicji, twierdzeń etc.

    Classical to moduł, który pozwala przeprowadzać rozumowania
    w logice klasycznej. Deklaruje on jako aksjomaty niektóre
    tautologie logiki klasycznej, np. zasadę wyłączonego środka,
    która tutaj nazywa się [classic]. *)

Check classic.
(* ===> forall P : Prop, P \/ ~ P *)

Lemma imp_and_or : (P -> Q \/ R) -> ((P -> Q) \/ (P -> R)).
(* begin hide *)
Proof.
  intros. destruct (classic P) as [HP | HnotP].
    destruct (H HP); [left | right]; intro; assumption.
    left. intro. cut False.
      inversion 1.
      apply HnotP. apply H0.
Qed.
(* end hide *)

Lemma deMorgan_2_conv : ~ (P /\ Q) -> ~ P \/ ~ Q.
(* begin hide *)
Proof. tauto. Qed.
(* end hide *)

Lemma not_impl : ~ (P -> Q) -> P /\ ~ Q.
(* begin hide *)
Proof.
  intro H. split.
    cut False.
      destruct 1.
      apply H. intro.
Abort.
(* end hide *)

Lemma impl_not_or : (P -> Q) -> (~ P \/ Q).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma material_implication : (P -> Q) <-> (~ P \/ Q).
(* begin hide *)
Proof.
  split; intros.
    destruct (classic P).
      right. apply H. assumption.
      left. intro. contradiction.
    destruct H.
      contradiction.
      assumption.
Qed.
(* end hide *)

Lemma contraposition_conv : (~ Q -> ~ P) -> (P -> Q).
(* begin hide *)
Proof.
  intros H p. cut False.
    destruct 1.
    apply H.
Abort.
(* end hide *)

Lemma excluded_middle : P \/ ~ P.
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma peirce : ((P -> Q) -> P) -> P.
(* begin hide *)
Proof.
Abort.
(* end hide *)

End ClassicalExercises.