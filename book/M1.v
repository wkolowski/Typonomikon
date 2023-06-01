(** * M1: Legalna topologia *)

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

(** * Wstęp (TODO) *)

(** Najpierw nawiązanie do tego co było o relacjach i jakieś intuicje
    o porządkach. Potem trochę porządkologii i może jakieś dziedziny.
    Potem topologia. *)

(** * Typy przeszukiwalne (TODO) *)

(** Tutaj o topologii takiej jak robi Martin Escardó, np. w tej pracy:
    "Infinite sets that satisfy the principle of omniscience in any
    variety of constructive mathematics", czyli odkrywamy, że klasycznie
    [nat] i [conat] są izomorficzne, ale [conat] jest konstruktywnie
    przeszukiwalne, zaś [nat] nie. Wszystko dzieje się w legalnym Coqu,
    z włączonym guard checkerem i bez żadnych homotopii. *)

From Typonomikon Require Import F3.

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
  out := if p zero then Z else S (search_conat (fun n => p (succ n)))
|}.

Lemma sc_eq :
  forall p : conat -> bool,
    sim (search_conat p)
      (if p zero then zero else succ (search_conat (fun n => p (succ n)))).
Proof.
  constructor; cbn.
  destruct (p zero) eqn: Hp; cbn; constructor.
  reflexivity.
Qed.

Lemma search_conat_false :
  forall p : conat -> bool,
    p (search_conat p) = false -> sim (search_conat p) omega.
Proof.
  cofix CH.
  intros p H.
  constructor. destruct (p zero) eqn: Hp.
    replace (search_conat p) with zero in H.
      congruence.
      admit. (* cbn. rewrite Hp. reflexivity. *)
    cbn. rewrite Hp. constructor.
    apply CH.
    admit. (* rewrite sc_eq, Hp in H. assumption. *)
Admitted.

Lemma search_conat_true :
  forall (p : conat -> bool) (n : conat),
    p n = true -> le (search_conat p) n.
Proof.
Admitted.
(*
  cofix CH.
  intros p n H.
  constructor. rewrite sc_eq. destruct (p zero) eqn: Hp.
    left. cbn. reflexivity.
    destruct n as [[| n']].
      unfold zero in Hp. congruence.
      eright; cbn; try reflexivity. apply CH. assumption.
Qed.
*)

Definition pred (c : conat) : conat :=
{|
  out :=
    match out c with
    | Z => Z
    | S c' => out c'
    end
|}.

Lemma sim_omega_le :
  forall n m : conat,
    sim n omega -> le n m -> sim m omega.
Proof.
Admitted.
(*
  cofix CH.
  intros n m [[Hn1 | n1 m1 Hn1 Hm1 Hsim]] [[Hn2 | n2 m2 Hn2 Hm2 Hle]];
  cbn in *; try congruence.
  constructor; eright; cbn; eauto.
  inv Hm1. apply (CH n1 m2); congruence.
Qed.
*)

(* begin hide *)
(* TODO *) Fixpoint cut (n : nat) (c : conat) : conat :=
match n with
| 0 => zero
| Datatypes.S n' =>
  match out c with
  | Z => zero
  | S c' => succ (cut n' c')
  end
end.
(* TODO: czy da się pokazać [Searchable conat] bez aksjomatów? *)
(* end hide *)

#[refine]
#[export]
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
  f_equal. rewrite <- sim_eq.
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
#[export]
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
#[export]
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
  sall (fun n => match out n with | Z => true | _ => false end).

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

Inductive Finite' : conat -> Type :=
| Finite'_zero : Finite' zero
| Finite'_succ : forall n : conat, Finite' n -> Finite' (succ n).

Fixpoint Finite'_to_nat {c : conat} (f : Finite' c) : nat :=
match f with
| Finite'_zero => 0
| Finite'_succ _ f' => Datatypes.S (Finite'_to_nat f')
end.

(* end hide *)