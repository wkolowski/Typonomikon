(** * M: Topologia *)

(* begin hide *)

(*
TODO: Coś więcej o perspektywie topologicznej z gęstymi podprzestrzeniami.
TODO: Dla przykładu: [conat] to po prostu liczby konaturalne, ale już
TODO [{c : conat | Finite c \/ Infinite c}] to gęsta podprzestrzeń [conat]
TODO: (czyli, że jej dopełnienie jest puste), ale z dodatkową informacją o
TODO: tym, w jaki sposób podzielić [conat] na dwie (implicite rozłączne)
TODO: podprzestrzenie liczb skończonych i nieskończonych, które pokrywają
TODO: całą przestrzeń. Zaiste pasjonujące.
*)

(* end hide *)

(** Najpierw nawiązanie do tego co było o relacjach i jakieś intuicje
    o porządkach. Potem trochę porządkologii i może jakieś dziedziny.
    Potem topologia. *)

(** * Legalna topologia (TODO) *)

(** Tutaj o topologii takiej jak robi Martin Escardó, np. w tej pracy:
    "Infinite sets that satisfy the principle of omniscience in any
    variety of constructive mathematics", czyli odkrywamy, że klasycznie
    [nat] i [conat] są izomorficzne, ale [conat] jest konstruktywnie
    przeszukiwalne, zaś [nat] nie. Wszystko dzieje się w legalnym Coqu,
    z włączonym guard checkerem i bez żadnych homotopii. *)

Require Import F2.

Class Searchable (A : Type) : Type :=
{
    search : (A -> bool) -> A;
    search_spec :
      forall p : A -> bool,
        p (search p) = false -> forall x : A, p x = false;
}.

(** Uwaga TODO: pamiętać o tym, że przeszukiwalność typu to coś jak
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

Lemma search_conat_false :
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

Lemma search_conat_true :
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

Lemma sim_omega_le :
  forall n m : conat,
    sim n omega -> le n m -> sim m omega.
Proof.
  cofix CH.
  intros n m Hsim Hle.
  destruct Hle as [[]].
    destruct Hsim as [[]].
      destruct H0. inversion H1.
      destruct H0 as (n' & m' & H1 & H2). congruence.
    destruct H as (n' & m' & H1 & H2 & H3).
      constructor. right. exists m', omega. split.
        assumption.
        split.
          cbn. reflexivity.
          apply CH with n'.
            destruct Hsim as [[]].
              destruct H. congruence.
              destruct H as (n'' & m'' & H1' & H2' & H3').
                cbn in H2'. inv H2'. rewrite H1' in H1. inv H1.
                  assumption.
Qed.

(* begin hide *)
(* TODO *) Fixpoint cut (n : nat) (c : conat) : conat :=
match n with
    | 0 => zero
    | S n' =>
        match pred c with
            | None => zero
            | Some c' => succ (cut n' c')
        end
end.
(* TODO: czy da się pokazać [Searchable conat] bez aksjomatów? *)
(* end hide *)

#[refine]
Instance Searchable_conat : Searchable conat :=
{
    search := search_conat;
}.
Proof.
  intros p H c.
  destruct (p c) eqn: Hpn; try reflexivity.
  assert (sim (search_conat p) omega).
    apply search_conat_false. assumption.
  assert (le (search_conat p) c).
    apply search_conat_true. assumption.
  assert (sim c omega).
    apply sim_omega_le with (search_conat p); assumption.
  assert (search_conat p <> c).
    intro. subst. congruence.

  rewrite <- H, <- Hpn.
  f_equal. apply sim_eq.
  rewrite H0. assumption.
Defined.

(** **** Ćwiczenie (trudne i niezbadane) *)

(** Czy typ [Stream A] jest przeszukiwalny? Jeżeli tak, udowodnij.
    Jeżeli nie, to znajdź jakiś warunek na [A], przy którym [Stream A]
    jest przeszukiwalny. *)

(** Trochę właściwości, pewnie dość oczywistych. *)

Definition search_prod
  {A B : Type} (SA : Searchable A) (SB : Searchable B)
  (p : A * B -> bool) : A * B :=
    let a := search (fun a : A => p (a, search (fun b : B => p (a, b)))) in
    let b := search (fun b : B => p (a, b)) in
      (a, b).

#[refine]
Instance Searchable_prod
  {A B : Type}
  (SA : Searchable A) (SB : Searchable B) : Searchable (A * B) :=
{
    search := @search_prod _ _ SA SB
}.
Proof.
  intros p H [a b].
  unfold search_prod in *.
  destruct SA as [sa Ha], SB as [sb Hb]; cbn in *.
  specialize (Hb (fun b => p (a, b))); cbn in Hb.
  apply Hb.
  specialize (Ha (fun a => p (a, sb (fun b => p (a, b))))). cbn in Ha.
  apply Ha.
  assumption.
Defined.

#[refine]
Instance Searchable_sum
  {A B : Type}
  (SA : Searchable A) (SB : Searchable B) : Searchable (A + B) :=
{
    search p :=
      let a := search (fun a => p (inl a)) in
      let b := search (fun b => p (inr b)) in
        if p (inl a) then inl a else inr b
}.
Proof.
  intros p H x.
  destruct SA as [sa Ha], SB as [sb Hb]; cbn in *.
  destruct (p (inl (sa (fun a => p (inl a))))) eqn : Heq.
    congruence.
    destruct x as [a | b].
      apply (Ha (fun a => p (inl a))). assumption.
      apply (Hb (fun b => p (inr b))). assumption.
Defined.

(** Da się zrobić jakieś ciekawe funkcje? *)

Definition sex
  {A : Type} {_ : Searchable A} (p : A -> bool) : bool :=
    p (search p).

Definition sall
  {A : Type} {_ : Searchable A} (p : A -> bool) : bool :=
    let p' := fun a => negb (p a) in
      negb (p' (search p')).

(** Nie każdy [conat] jest zerem, brawo! *)
Compute
  sall (fun n => match pred n with | None => true | _ => false end).

(** To samo, tylko bardziej przyjazne sygnatury typów. *)

Inductive ospec
  {A : Type} (N : Prop) (S : A -> Prop) : option A -> Prop :=
    | ospec_None : N -> ospec N S None
    | ospec_Some : forall a : A, S a -> ospec N S (Some a).

Definition search'
  {A : Type} {SA : Searchable A} (p : A -> bool) : option A :=
    if p (search p) then Some (search p) else None.

Lemma search'_spec :
  forall {A : Type} {SA : Searchable A} (p : A -> bool),
    ospec (forall x : A, p x = false)
          (fun x : A => p x = true)
          (search' p).
Proof.
  intros. unfold search'.
  destruct (p (search p)) eqn: H; constructor.
    assumption.
    apply search_spec. assumption.
Qed.

(* begin hide *)
Require Import B3.
Check LEM.
Print LEM.

Search nat conat.
Search Infinite.
Search Finite.
Print Finite.

Inductive Finite' : conat -> Type :=
    | Finite'_zero : Finite' zero
    | Finite'_succ : forall n : conat, Finite' n -> Finite' (succ n).

Definition finite_nat {c : conat} (f : Finite c) : nat.
Proof.
Abort.

(* end hide *)

(** * Nielegalna topologia (TODO) *)

(** Tutaj o topologii takiej jak robi Martin Escardó głównie w tej
    książce: "Synthetic topology of data types and classical spaces",
    czyli wyłączamy guard checker i patrzymy jakie programy zatrzymują
    się, a jakie nie. *)