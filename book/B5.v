(** * B5: Strzępki logicznych kodów [TODO] *)

(** * i/lub (TODO)  *)

Inductive andor (P Q : Prop) : Prop :=
    | left  : P ->      andor P Q
    | right :      Q -> andor P Q
    | both  : P -> Q -> andor P Q.

Lemma and_or_l :
  forall P Q : Prop, P /\ Q -> P \/ Q.
(* begin hide *)
Proof.
  destruct 1 as [p q]. left. assumption.
Qed.
(* end hide *)

Lemma and_or_r :
  forall P Q : Prop, P /\ Q -> P \/ Q.
(* begin hide *)
Proof.
  destruct 1 as [p q]. right. assumption.
Qed.
(* end hide *)

Lemma andor_or :
  forall P Q : Prop, andor P Q <-> P \/ Q.
(* begin hide *)
Proof.
  split.
    destruct 1 as [p | q | p q].
      left. assumption.
      right. assumption.
      left. assumption.
    destruct 1 as [p | q].
      apply left. assumption.
      apply right. assumption.
Qed.
(* end hide *)

(** * [constructive_dilemma] (TODO) *)

Lemma constructive_dilemma :
  forall P Q R S : Prop,
    (P -> R) -> (Q -> S) -> P \/ Q -> R \/ S.
(* begin hide *)
Proof.
  intros P Q R S PR QS H.
  destruct H as [p | q].
    left. apply PR. assumption.
    right. apply QS. assumption.
Qed.
(* end hide *)

Lemma destructive_dilemma :
  forall P Q R S : Prop,
    (P -> R) -> (Q -> S) -> ~ R \/ ~ S -> ~ P \/ ~ Q.
(* begin hide *)
Proof.
  intros P Q R S PR QS H.
  destruct H as [nr | ns].
    left. intro p. apply nr, PR. assumption.
    right. intro q. apply ns, QS. assumption.
Qed.
(* end hide *)

Lemma idempotency_of_entailment :
  forall P Q : Prop,
    (P -> Q) <-> (P -> P -> Q).
(* begin hide *)
Proof.
  split.
    intros pq p1 p2. apply pq. assumption.
    intros ppq p. apply ppq.
      assumption.
      assumption.
Qed.
(* end hide *)

(** * Klasyczna dysjunkcja (TODO) *)

Require Import B B3.

(** Klasyczna dysjunkcja. Panie, na co to komu? *)
Definition cor (P Q : Prop) : Prop :=
  ~ ~ (P \/ Q).

Lemma cor_in_l :
  forall P Q : Prop, P -> cor P Q.
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma cor_in_r :
  forall P Q : Prop, Q -> cor P Q.
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma cor_assoc :
  forall P Q R : Prop, cor (cor P Q) R <-> cor P (cor Q R).
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma cor_comm :
  forall P Q : Prop, cor P Q -> cor Q P.
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma cor_True_l :
  forall P : Prop, cor True P <-> True.
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma cor_True_r :
  forall P : Prop, cor P True <-> True.
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma cor_False_l :
  forall P : Prop, cor False P <-> ~ ~ P.
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma cor_False_r :
  forall P : Prop, cor P False <-> ~ ~ P.
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma or_cor :
  forall P Q : Prop, P \/ Q -> cor P Q.
(* begin hide *)
Proof.
  firstorder.
Qed.
(* end hide *)

Lemma cor_LEM :
  forall P : Prop, cor P (~ P).
(* begin hide *)
Proof.
  unfold cor.
  intros P H.
  apply H. right. intro p.
  apply H. left. assumption.
Qed.
(* end hide *)

Lemma cor_or_LEM :
  (forall P Q : Prop, cor P Q -> P \/ Q)
    <->
  LEM.
(* begin hide *)
Proof.
  unfold cor, LEM; split.
    intros H P. apply H, cor_LEM.
    intros LEM P Q H. destruct (LEM (P \/ Q)).
      assumption.
      contradiction.
Qed.
(* end hide *)

Lemma cand_and_LEM :
  (forall P Q : Prop, ~ ~ (P /\ Q) -> P /\ Q) ->
    LEM.
(* begin hide *)
Proof.
  unfold LEM. intros H P.
  destruct (H (P \/ ~ P) True).
    firstorder.
    assumption.
Qed.
(* end hide *)

Lemma cor_spec :
  forall P Q : Prop,
    cor P Q <-> ~ (~ P /\ ~ Q).
(* begin hide *)
Proof.
  split.
    intros H [np nq]. apply H. intros [p | q].
      apply np, p.
      apply nq, q.
    intros pq npq. apply pq. split.
      intro p. apply npq. left. assumption.
      intro q. apply npq. right. assumption.
Qed.
(* end hide *)

(** * [WLEM] (TODO) *)

Definition WLEM : Prop :=
  forall P : Prop, ~ P \/ ~ ~ P.

Lemma WLEM_hard :
  forall P : Prop, ~ P \/ ~ ~ P.
(* begin hide *)
Proof.
  intro P. left. intro p.
Restart.
  intro P. right. intro np. apply np.
Abort.
(* end hide *)

Lemma WLEM_irrefutable :
  forall P : Prop, ~ ~ (~ P \/ ~ ~ P).
(* begin hide *)
Proof.
  intros P H.
  apply H. left. intro p.
  apply H. right. intro np.
  contradiction.
Qed.
(* end hide *)

Lemma LEM_WLEM :
  LEM -> WLEM.
(* begin hide *)
Proof.
  unfold LEM, WLEM.
  intros LEM P.
  destruct (LEM P) as [p | np].
    right. intro np. contradiction.
    left. assumption.
Qed.
(* end hide *)

Lemma MI_WLEM :
  MI -> WLEM.
(* begin hide *)
Proof.
  unfold MI, WLEM.
  intros MI P.
  destruct (MI P P) as [np | p].
    trivial.
    left. assumption.
    right. intro np. contradiction.
Qed.
(* end hide *)

Lemma ME_WLEM :
  ME -> WLEM.
(* begin hide *)
Proof.
  unfold ME, WLEM.
  intros ME P.
  destruct (ME P P) as [[p _] | [np _]].
    split; trivial.
    right. intro np. contradiction.
    left. assumption.
Qed.
(* end hide *)

Lemma DNE_WLEM :
  DNE -> WLEM.
(* begin hide *)
Proof.
  unfold DNE, WLEM.
  intros DNE P.
  apply DNE.
  intro H. apply H.
  right. intro np.
  apply H.
  left. assumption.
Qed.
(* end hide *)

Lemma CM_WLEM :
  CM -> WLEM.
(* begin hide *)
Proof.
  unfold CM, WLEM.
  intros CM P.
  apply CM. intro H.
  right. intro np.
  apply H.
  left. assumption.
Qed.
(* end hide *)

Lemma Peirce_WLEM :
  Peirce -> WLEM.
(* begin hide *)
Proof.
  unfold Peirce, WLEM.
  intros Peirce P.
  apply (Peirce _ False).
  intro H.
  right. intro np.
  apply H.
  left. assumption.
Qed.
(* end hide *)

Lemma Contra_WLEM :
  Contra -> WLEM.
(* begin hide *)
Proof.
  unfold Contra, WLEM.
  intros Contra P.
  apply (Contra True).
    intros H _. apply H. right. intro np. apply H. left. assumption.
    trivial.
Qed.
(* end hide *)

Definition LEM3 : Prop :=
  forall P : Prop, P \/ ~ P \/ ~ ~ P.

Lemma LEM3_WLEM :
  LEM3 -> WLEM.
(* begin hide *)
Proof.
  unfold LEM3, WLEM.
  intros LEM3 P.
  destruct (LEM3 P) as [p | [np | nnp]].
    right. intro np. contradiction.
    left. assumption.
    right. assumption.
Qed.
(* end hide *)

Lemma WLEM_LEM3 :
  WLEM -> LEM3.
(* begin hide *)
Proof.
  unfold WLEM, LEM3.
  intros WLEM P.
  destruct (WLEM P) as [np | nnp].
    right. left. assumption.
    right. right. assumption.
Qed.
(* end hide *)

Lemma LEM_LEM3 :
  LEM -> LEM3.
(* begin hide *)
Proof.
  unfold LEM, LEM3.
  intros LEM P.
  destruct (LEM P) as [p | np].
    left. assumption.
    right. left. assumption.
Qed.
(* end hide *)

(** * Paradoks Curry'ego (TODO) *)

Definition NI : Prop :=
  forall P Q : Prop, ~ (P -> Q) -> P /\ ~ Q.

Require Import B3.

Lemma NI_LEM :
  NI -> LEM.
(* begin hide *)
Proof.
  unfold NI, LEM.
  intros NI P.
  destruct (NI (P \/ ~ P) False).
    firstorder.
    assumption.
Qed.
(* end hide *)

Definition IOR : Prop :=
  forall P Q R : Prop, (P -> Q \/ R) -> (P -> Q) \/ (P -> R).

Lemma IOR_LEM :
  IOR -> LEM.
(* begin hide *)
Proof.
  unfold IOR, LEM.
  intros IOR P.
Abort.
(* end hide *)

Lemma IOR_WLEM :
  IOR -> WLEM.
(* begin hide *)
Proof.
  unfold IOR, WLEM.
  intros IOR P.
Abort.
(* end hide *)

Lemma WLEM_IOR :
  WLEM -> IOR.
(* begin hide *)
Proof.
  unfold WLEM, IOR.
  intros WLEM P Q R H.
  destruct (WLEM (P -> Q)).
    right. intro p. destruct (H p).
      contradiction H0. intros _. assumption.
      assumption.
    left. intro p.
Abort.
(* end hide *)

(** * Logika klasyczna jako (coś więcej niż) logika de Morgana (TODO) *)

Lemma deMorgan :
  forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
(* begin hide *)
Proof.
  intros P Q H. left. intro p. apply H. split.
    assumption.
Restart.
  intros P Q H. right. intro q. apply H. split.
Abort.
(* end hide *)

Lemma deMorgan_irrefutable :
  forall P Q : Prop, ~ ~ (~ (P /\ Q) -> ~ P \/ ~ Q).
(* begin hide *)
Proof.
  intros P Q H.
  apply H. intro npq.
  left. intro p.
  apply H. intros _.
  right. intro q.
  apply npq. split.
    assumption.
    assumption.
Qed.
(* end hide *)

Lemma deMorgan_WLEM :
  (forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q)
    <->
  (forall P : Prop, ~ P \/ ~ ~ P).
(* begin hide *)
Proof.
  split.
    intros deMorgan P. apply deMorgan. apply noncontradiction.
    intros WLEM P Q H. destruct (WLEM P) as [np | nnp].
      left. assumption.
      destruct (WLEM Q) as [nq | nnq].
        right. assumption.
        left. intro p. apply nnq. intro. apply H. split; assumption.
Qed.
(* end hide *)

Lemma deMorgan_big :
  forall (A : Type) (P : A -> Prop),
    A -> (~ forall x : A, P x) -> exists x : A, ~ P x.
(* begin hide *)
Proof.
  intros A P a H.
  exists a. intro pa.
  apply H. intro x.
Abort.
(* end hide *)

Lemma deMorgan_big_irrefutable :
  forall (A : Type) (P : A -> Prop),
    ~ ~ (A -> (~ forall x : A, P x) -> exists x : A, ~ P x).
(* begin hide *)
Proof.
  intros A P H1.
  apply H1. intros a H2.
  exists a. intro pa.
Abort.
(* end hide *)

Lemma LEM_deMorgan_big :
  (forall P : Prop, P \/ ~ P) ->
    (forall (A : Type) (P : A -> Prop),
       (~ forall x : A, P x) -> exists x : A, ~ P x).
(* begin hide *)
Proof.
  intros LEM A P H. destruct (LEM (exists x : A, ~ P x)).
    assumption.
    contradiction H. intro x. destruct (LEM (P x)).
      assumption.
      contradiction H0. exists x. assumption.
Qed.
(* end hide *)

Lemma deMorgan_big_WLEM :
  (forall (A : Type) (P : A -> Prop),
     (~ forall x : A, P x) -> exists x : A, ~ P x) ->
  (forall P : Prop, ~ P \/ ~ ~ P).
(* begin hide *)
Proof.
  intros DM P.
    specialize (DM bool (fun b => if b then P else ~ P)).
    cbn in DM. destruct DM as [b H].
      intro H. apply (H false). apply (H true).
      destruct b.
        left. assumption.
        right. assumption.
Qed.
(* end hide *)

(** * Double negation shift (TODO) *)

(** Wzięte z https://ncatlab.org/nlab/show/double-negation+shift *)

Definition DNS : Prop :=
  forall (A : Type) (P : A -> Prop),
    (forall x : A, ~ ~ P x) -> ~ ~ forall x : A, P x.

Print LEM.

Lemma DNS_not_not_LEM :
  DNS <-> ~ ~ LEM.
(* begin hide *)
Proof.
  unfold DNS, LEM. split.
    intros DNS H.
      specialize (DNS Prop (fun P => P \/ ~ P) LEM_irrefutable).
      apply DNS. intro H'. contradiction.
    intros NNLEM A P H1 H2. apply NNLEM. intro LEM.
      assert (forall x : A, P x).
        intro x. destruct (LEM (P x)).
          assumption.
          specialize (H1 x). contradiction.
        contradiction.
Qed.
(* end hide *)

(** * Godel-Dummet (TODO) *)

Definition GD : Prop :=
  forall P Q : Prop, (P -> Q) \/ (Q -> P).

Lemma GD_irrefutable :
  forall P Q : Prop, ~ ~ ((P -> Q) \/ (Q -> P)).
(* begin hide *)
Proof.
  intros P Q H.
  apply H. left. intro p.
  exfalso.
  apply H. right. intro q.
  assumption.
Qed.
(* end hide *)

Lemma LEM_GD :
  LEM -> GD.
(* begin hide *)
Proof.
  unfold LEM, GD. intros LEM P Q.
  destruct (LEM P) as [p | np].
    right. intros _. assumption.
    left. intro p. contradiction.
Qed.
(* end hide *)

Lemma MI_GD :
  MI -> GD.
(* begin hide *)
Proof.
  unfold MI, GD.
  intros MI P Q.
  destruct (MI P P) as [np | p].
    trivial.
    left. intro p. contradiction.
    right. intros _. assumption.
Qed.
(* end hide *)

Lemma ME_GD :
  ME -> GD.
(* begin hide *)
Proof.
  unfold ME, GD.
  intros ME P Q.
  destruct (ME P P) as [[p _] | [np _]].
    split; trivial.
    right. intros _. assumption.
    left. intro p. contradiction.
Qed.
(* end hide *)

Lemma DNE_GD :
  DNE -> GD.
(* begin hide *)
Proof.
  unfold DNE, GD.
  intros DNE P Q.
  apply DNE.
  apply GD_irrefutable.
Qed.
(* end hide *)

Lemma CM_GD :
  CM -> GD.
(* begin hide *)
Proof.
  unfold CM, GD.
  intros CM P Q.
  apply CM. intro H.
  left. intro p.
  exfalso. apply H.
  right. intros _.
  assumption.
Qed.
(* end hide *)

Lemma Peirce_GD :
  Peirce -> GD.
(* begin hide *)
Proof.
  unfold Peirce, GD.
  intros Peirce P Q.
  apply (Peirce _ False). intro H.
  left. intro p.
  exfalso. apply H.
  right. intros _.
  assumption.
Qed.
(* end hide *)

Lemma Contra_GD :
  Contra -> GD.
(* begin hide *)
Proof.
  unfold Contra, GD.
  intros Contra P Q.
  apply (Contra True).
    intros H _. apply H. left. intro p. exfalso.
      apply H. right. intros. assumption.
    trivial.
Qed.
(* end hide *)

(** * Słabe spójniki (TODO) *)

Lemma weak_and_elim :
  forall P Q R : Prop,
    (P -> R) -> (Q -> R) -> (~ ~ R -> R) -> ~ (~ P /\ ~ Q) -> R.
(* begin hide *)
Proof.
  intros P Q R pr qr nnrr pq.
  apply nnrr. intro nr.
  apply pq. split.
    intro p. apply nr, pr, p.
    intro q. apply nr, qr, q.
Qed.
(* end hide *)

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

Lemma ex_dec :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, P x \/ ~ P x) ->
      (exists x : A, P x) \/ ~ (exists x : A, P x).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma forall_dec :
  forall (A : Type) (P : A -> Prop),
    (forall x : A, P x \/ ~ P x) ->
      (forall x : A, P x) \/ ~ (forall x : A, P x).
(* begin hide *)
Proof.
  intros A P H.
Abort.
(* end hide *)

(** * [xor] (TODO) *)

(** Xor w logice intuicjonistycznej - ubaw po pachy. *)

Definition xor (A B : Prop) : Prop :=
  (A /\ ~ B) \/ (~ A /\ B).

Ltac xor := unfold xor.

Lemma xor_irrefl :
  forall P : Prop, ~ xor P P.
(* begin hide *)
Proof.
  xor. intros A H.
  destruct H as [[p np] | [np p]].
    apply np. assumption.
    apply np. assumption.
Qed.
(* end hide *)

Lemma xor_sym :
  forall P Q : Prop, xor P Q -> xor Q P.
(* begin hide *)
Proof.
  xor. intros P Q H.
  destruct H as [[p nq] | [q np]].
    right. split; assumption.
    left. split; assumption.
Qed.
(* end hide *)

Lemma xor_sym' :
  forall P Q : Prop, xor P Q <-> xor Q P.
(* begin hide *)
Proof.
  split; apply xor_sym.
Qed.
(* end hide *)

Lemma xor_cotrans :
  LEM ->
    (forall P Q R : Prop, xor P Q -> xor P R \/ xor Q R).
(* begin hide *)
Proof.
  unfold LEM, xor. intros LEM P Q R H.
  destruct H as [[p nq] | [q np]].
    destruct (LEM R) as [r | nr].
      right. right. split; assumption.
      left. left. split; assumption.
    destruct (LEM R) as [r | nr].
      left. right. split; assumption.
      right. left. split; assumption.
Qed.
(* end hide *)

Lemma xor_assoc :
  forall P Q R : Prop,
    xor P (xor Q R) <-> xor (xor P Q) R.
(* begin hide *)
Proof.
  unfold xor. split.
    firstorder.
Abort.
(* end hide *)

Lemma xor_not_iff :
  forall P Q : Prop, xor P Q -> ~ (P <-> Q).
(* begin hide *)
Proof.
  unfold xor, iff.
  intros P Q H1 H2.
  destruct H2 as [pq qp], H1 as [[p nq] | [np q]].
    apply nq, pq. assumption.
    apply np, qp. assumption.
Qed.
(* end hide *)

Lemma not_iff_xor :
  LEM ->
    forall P Q : Prop, ~ (P <-> Q) -> xor P Q.
(* begin hide *)
Proof.
  unfold LEM, xor.
  intros LEM P Q H.
  destruct (LEM P) as [p | np], (LEM Q) as [q | nq].
    contradiction H. split; trivial.
    left. split; assumption.
    right. split; assumption.
    contradiction H. split; intro; contradiction.
Qed.
(* end hide *)

Lemma xor_spec :
  forall P Q : Prop, xor P Q <-> (P \/ Q) /\ (~ P \/ ~ Q).
(* begin hide *)
Proof.
  unfold xor, iff. split.
    intros [[p nq] | [np q]].
      split.
        left. assumption.
        right. assumption.
      split.
        right. assumption.
        left. assumption.
    intros [[p | q] [np | nq]].
      contradiction.
      left. split; assumption.
      right. split; assumption.
      contradiction.
Qed.
(* end hide *)

Lemma xor_False_r :
  forall P : Prop, xor P False <-> P.
(* begin hide *)
Proof.
  unfold xor, iff. split.
    intro H. destruct H as [[p _] | [_ f]].
      assumption.
      contradiction.
    intro p. left. split.
      assumption.
      intro f. contradiction.
Qed.
(* end hide *)

Lemma xor_False_l :
  forall P : Prop, xor False P <-> P.
(* begin hide *)
Proof.
  split.
    intro x. apply xor_sym in x. apply xor_False_r. assumption.
    intro p. unfold xor. right. split.
      intro f. contradiction.
      assumption.
Qed.
(* end hide *)

Lemma xor_True_l :
  forall P : Prop, xor True P <-> ~ P.
(* begin hide *)
Proof.
  unfold xor, iff. split.
    intros [[_ np] | [f _]].
      assumption.
      contradiction.
    intro np. left. split.
      trivial.
      assumption.
Qed.
(* end hide *)

Lemma xor_True_r :
  forall P : Prop, xor P True <-> ~ P.
(* begin hide *)
Proof.
  intros. rewrite xor_sym', xor_True_l. reflexivity.
Qed.
(* end hide *)

(** * Zagadka (TODO) *)

Definition Classically (A : Type) : Type :=
  (forall P : Prop, P \/ ~ P) -> A.

Notation "f $ x" := (f x) (at level 100, only parsing).

Ltac cls := progress unfold Classically; intro LEM.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Sesshomaru, Naraku i Inuyasha należą do sekty Warring Era. Każdy
    członek tej sekty jest albo demonem, albo człowiekiem, albo i jednym
    i drugim. Żaden człowiek nie lubi deszczu, a wszystkie demony lubią
    śnieg. Naraku nie cierpi wszystkiego, co lubi Sesshomaru, a lubi
    wszystko czego nie lubi Sesshomaru. Sesshomaru lubi deszcz i śnieg.

    Wyraź opis powyższego tekstu w logice pierwszego rzędu. Czy jest
    ktoś, kto jest człowiekiem, ale nie jest demonem? Udowodnij, że
    twoja odpowiedź jest poprawna. *)

(* begin hide *)
Axioms
  (WarringEra : Type)
  (Sesshomaru Naraku Inuyasha : WarringEra)
  (isHuman isDemon : WarringEra -> Prop)
  (Thing : Type)
  (Rain Snow : Thing)
  (likes : WarringEra -> Thing -> Prop)
  (H0 : forall x : WarringEra,
    isHuman x \/ isDemon x \/ (isHuman x /\ isDemon x))
  (H1 : forall x : WarringEra, isHuman x -> ~ likes x Rain)
  (H2 : forall x : WarringEra, isDemon x -> likes x Snow)
  (H3 : forall x : Thing, likes Sesshomaru x -> ~ likes Naraku x)
  (H4 : forall x : Thing, ~ likes Sesshomaru x -> likes Naraku x)
  (H5 : likes Sesshomaru Rain)
  (H6 : likes Sesshomaru Snow).

Lemma isDemon_Sesshomaru :
  isDemon Sesshomaru.
Proof.
  elim: (H0 Sesshomaru) => [| [| []]];
  by try move/(@H1 _)/(_ H5) => [].
Qed.

Lemma isHuman_Naraku :
  isHuman Naraku.
Proof.
  elim: (H0 Naraku) => [| [| []]]; try done.
    by move/(@H2 _)/(H3 H6).
Qed.

Lemma not_isDemon_Naraku :
  ~ isDemon Naraku.
Proof.
  by move/H2/(H3 H6).
Qed.
(* end hide *)