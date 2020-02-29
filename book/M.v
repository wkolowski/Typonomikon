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

Require Import F2.

Class Searchable (A : Type) : Type :=
{
    search : (A -> bool) -> A;
    search_spec :
      forall p : A -> bool,
        p (search p) = false -> forall x : A, p x = false;
}.

(** Uwaga TODO: pamiętać o tym, że przeszukiwalność typu to coś jak
    paradoks pijoka:
    - jeżeli pijok pije, to wszyscy piją
    - jeżeli wyszukany element nie spełnia, to żaden nie spełnia *)

CoFixpoint search_conat (p : conat -> bool) : conat :=
{|
    pred := if p zero
            then None
            else Some (search_conat (fun n => p (succ n)))
|}.

Lemma sc_eq :
  forall p : conat -> bool,
    search_conat p =
      if p zero then zero else succ (search_conat (fun n => p (succ n))).
Proof.
  intros. apply eq_pred. cbn.
  destruct (p zero) eqn: Hp.
    cbn. reflexivity.
    cbn. reflexivity.
Qed.

Lemma search_conat_spec :
  forall p : conat -> bool,
    p (search_conat p) = false -> sim (search_conat p) omega.
Proof.
  cofix CH.
  intros p H.
  constructor. cbn. destruct (p zero) eqn: Hp.
    replace (search_conat p) with zero in H.
      congruence.
      apply eq_pred. cbn. rewrite Hp. reflexivity.
    right. do 2 eexists. split; [idtac | split].
      1-2: reflexivity.
      apply CH. rewrite sc_eq, Hp in H. assumption.
Qed.

Lemma sc_true :
  forall (p : conat -> bool) (n : conat),
    p n = true -> le (search_conat p) n.
Proof.
  cofix CH.
  intros p n H.
  constructor. rewrite sc_eq. destruct (p zero) eqn: Hp.
    left. cbn. reflexivity.
    right. cbn. destruct n as [[n' |]].
      Focus 2. unfold zero in Hp. congruence.
      do 2 eexists; split; [idtac | split].
        1-2: reflexivity.
        apply CH. rewrite <- H. f_equal.
Qed.

#[refine]
Instance Searchable_conat : Searchable conat :=
{
    search := search_conat;
}.
Proof.
  intros p H n.
  destruct (p n) eqn: Hpn.
    2: reflexivity.
    pose (Hpn' := Hpn). pose (H' := H).
      apply sc_true in Hpn'. apply search_conat_spec in H'.
      apply sim_eq in H'. rewrite H' in *.
      apply le_omega_l in Hpn'. apply sim_eq in Hpn'. subst.
      congruence.
Defined.

(** **** Ćwiczenie (trudne i niezbadane) *)

(** Czy typ [Stream A] jest przeszukiwalny? Jeżeli tak, udowodnij.
    Jeżeli nie, to znajdź jakiś warunek na [A], przy którym [Stream A]
    jest przeszukiwalny. *)

(** * Nielegalna topologia *)

(** Tutaj o topologii takiej jak robi Martin Escardó głównie w tej
    książce: "Synthetic topology of data types and classical spaces",
    czyli wyłączamy guard checker i patrzymy jakie programy zatrzymują
    się, a jakie nie. *)