(** * BC4a: Logika klasyczna [TODO] *)

(* begin hide *)
From Typonomikon Require Export BC2a.
(*
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
         w praktyce wyłażące, jak człowiek próbuje użyć [LEM]) *)

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

Lemma Stable_or_fail :
  forall P Q : Prop,
    Stable P -> Stable Q -> Stable (P \/ Q).
Proof.
  unfold Stable.
  intros P Q f g nnpq.
  left.
  apply f; intros p.
  apply nnpq.
  intros [p' | q].
  - contradiction.
  - 
Abort.

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

Lemma LEM_hard :
  forall P : Prop, P \/ ~ P.
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

(** ** Zależności między pojęciami (TODO) *)

Lemma Wonderful_Penetrable :
  forall P : Prop,
    Wonderful P -> Penetrable P.
Proof.
  unfold Wonderful, Penetrable.
  intros P w R prp.
  apply w.
  intros np.
  apply prp.
  intros p.
  contradiction.
Qed.

Lemma Penetrable_Wonderful :
  forall P : Prop,
    Penetrable P -> Wonderful P.
Proof.
  unfold Wonderful, Penetrable.
  intros P pen.
  apply pen.
Qed.


Lemma Stable_DomainContraposable :
  forall (P : Prop),
    Stable P -> DomainContraposable P.
Proof.
  unfold Stable, DomainContraposable.
  intros P s R np p.
Abort.

Lemma DomainContraposable_Stable :
  forall (P : Prop),
    DomainContraposable P -> Stable P.
Proof.
  unfold DomainContraposable, Stable.
  intros P dc nnp.
Abort.

Lemma Stable_CodomainContraposable :
  forall (P : Prop),
    Stable P -> CodomainContraposable P.
Proof.
  unfold Stable, CodomainContraposable.
  intros P s R nr r.
  apply s.
  intros np.
  apply nr; assumption.
Qed.

Lemma CodomainContraposable_Stable :
  forall (P : Prop),
    CodomainContraposable P -> Stable P.
Proof.
  unfold CodomainContraposable, Stable.
  intros P cdc nnp.
  apply cdc with True.
  - intros np.
    contradiction.
  - trivial.
Qed.

(** * Aksjomaty i pojęcie "tabu" (TODO) *)

(** Tutaj o tym, co to znaczy, że w logice konstruktywnej LEM i tympodobne są tabu. *)

(** Drobna klasyfikacja na coś w stylu:
    - zdania prawdziwe ([P] zachodzi)
    - zdania fałszywe ([~ P] zachodzi)
    - zdania niezaprzeczalne ([~ ~ P] zachodzi)
    - zdania kontyngentne ([P] jest fałszywym zdaniem postaci
      [forall x : A, Q x] i zachodzi [exists x : A, Q x]. Inne
      podejście: tylko w kontekście, w którym zdanie [P] składa
      się z nieznanych części, np. [P -> Q] jest kontyngentne,
      bo [P -> P] zachodzi, zaś [True -> False] nie zachodzi.
    - zdania klasycznie prawdziwe ([P] zachodzi w logice klasycznej)
    - zdania tabu ([P] implikuje jakieś inne tabu, np. [LEM])

    TODO: być może dać to do podrozdziału o [WLEM] *)

(** * Pułapki negacji. O negowaniu słabym i mocnym (TODO) *)

(* begin hide *)

(** TODO: Wesoły angielski tytuł dla tego rozdziału: Negating, weak and strong *)

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
    do schematu "gdyby tak było, to wtedy... a zatem sprzeczność".

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

(** * Klasyczna logika pierwszego rzędu (TODO) *)

(** ** Paradoks pijoka *)

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

    Jest to błąd, gdyż zamierzonym znaczeniem słowa "jeżeli" jest tutaj (ze
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

(** ** Double negation shift *)

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

(** * Klasyczna logika wyższego rzędu (TODO) *)

(** ** Aksjomat wyboru (TODO) *)

(** Być może jest to właściwe miejsce, by wprowadzić aksjomaty wyboru. *)

Lemma AC_sig :
  forall {A B : Type} (R : A -> B -> Prop),
    (forall x : A, {y : B | R x y}) -> {f : A -> B | forall x : A, R x (f x)}.
Proof.
  intros A B R H.
  exists (fun a => proj1_sig (H a)).
  intros x.
  destruct (H x); cbn.
  assumption.
Qed.

Lemma AC_exists :
  forall {A B : Type} (R : A -> B -> Prop),
    (forall x : A, exists y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).
Proof.
  intros A B R H.
  unshelve eexists.
  - intros x.
    specialize (H x).
    Fail destruct H.
    admit.
  - intros x; cbn.
    specialize (H x).
  destruct (H x); cbn.
  assumption.
Qed.

Module AC.

Inductive Bot : SProp := .

Inductive Box (P : SProp) : Type :=
| box : P -> Box P.

Module withChoice_DNE.

Axiom withChoice :
  forall (A : Type) (P : SProp),
    ((((A -> Bot) -> Bot) -> A) -> P) -> P.

Lemma dne :
  forall P : SProp,
    ((P -> Bot) -> Bot) -> P.
Proof.
  intros P.
  apply (withChoice (Box P)).
  intros choice nnp.
  apply choice.
  intros nbp.
  apply nnp.
  intros p.
  apply nbp.
  constructor.
  assumption.
Qed.

Axiom withChoice' :
  forall (P : SProp),
    ((forall A : Type, ((A -> Bot) -> Bot) -> A) -> P) -> P.

End withChoice_DNE.

Module withChoice_equiv.

Definition withChoice : SProp :=
  forall (A : Type) (P : SProp),
    ((((A -> Bot) -> Bot) -> A) -> P) -> P.

Definition withChoice' : SProp :=
  forall (P : SProp),
    ((forall A : Type, ((A -> Bot) -> Bot) -> A) -> P) -> P.

Lemma withChoice_withChoice' :
  withChoice' -> withChoice.
Proof.
  unfold withChoice', withChoice.
  intros AC' A P p.
  apply p.
  intros nna.
  cut Bot.
  - intros [].
  - apply nna.
    intros a.
    
Abort.

Lemma withChoice'_withChoice :
  withChoice -> withChoice'.
Proof.
  unfold withChoice, withChoice'.
  intros AC P p.
  apply p.
  intros A nna.
  
  apply p.
  intros nna.
  destruct nna.
  intros a.
Abort.

End withChoice_equiv.

End AC.
(** * Interpretacja obliczeniowa logiki klasycznej, a raczej jej brak (TODO) *)

(** Tu opisać, jak aksjomaty mają się do prawa zachowania informacji i zawartości
    obliczeniowej. *)

(** * Porównanie logiki konstruktywnej i klasycznej (TODO) *)

(** * Uniwersum [SProp] (TODO) *)

Inductive sEmpty : SProp := .

Inductive sUnit : SProp :=
| stt : sUnit.

Inductive seq {A : Type} (x : A) : A -> SProp :=
| srefl : seq x x.

Goal forall A : Type, sEmpty -> A.
Proof.
  destruct 1.
Qed.

Goal
  forall {A : Type} (P : A -> Type) (x y : A),
    seq x y -> P x -> P y.
Proof.
  intros A P x y Hs Hp.
Abort.

Inductive Box (A : Type) : Prop :=
| box : A -> Box A.

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