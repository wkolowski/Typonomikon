(** * W3: Logika klasyczna [schowana na końcu dla niepoznaki] *)

(** * Prawa logiki klasycznej *)

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

(** * Logika klasyczna jako logika Boga *)

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

(** * Logika klasyczna jako logika materialnej implikacji i równoważności *)

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

Lemma DNE_hard :
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

(** * Logika klasyczna jako logika kontrapozycji *)

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

(** * Logika klasyczna jako logika Peirce'a *)

(** ** Logika cudownych konsekwencji *)

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

(** ** Logika Peirce'a *)

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

(** * Paradoks Curry'ego *)

(** * Zadania *)

(** wyrzucić zadania mącące (mieszające typy i zdania) *)

(** * Ściąga *)