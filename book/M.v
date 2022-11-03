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

From Typonomikon Require Import F2.

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
    out := if p zero
            then Z
            else S (search_conat (fun n => p (succ n)))
|}.

Lemma sc_eq :
  forall p : conat -> bool,
    search_conat p =
      if p zero then zero else succ (search_conat (fun n => p (succ n))).
Proof.
  intros. apply eq_out. cbn.
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
  constructor. destruct (p zero) eqn: Hp.
    replace (search_conat p) with zero in H.
      congruence.
      apply eq_out. cbn. rewrite Hp. reflexivity.
    eright; cbn; rewrite ?Hp; try reflexivity.
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
    destruct n as [[| n']].
      unfold zero in Hp. congruence.
      eright; cbn; try reflexivity. apply CH. assumption.
Qed.

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
  cofix CH.
  intros n m [[Hn1 | n1 m1 Hn1 Hm1 Hsim]] [[Hn2 | n2 m2 Hn2 Hm2 Hle]];
  cbn in *; try congruence.
  constructor; eright; cbn; eauto.
  inv Hm1. apply (CH n1 m2); congruence.
Qed.

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
From Typonomikon Require Import B4.

Inductive Finite' : conat -> Type :=
| Finite'_zero : Finite' zero
| Finite'_succ : forall n : conat, Finite' n -> Finite' (succ n).

Fixpoint Finite'_to_nat {c : conat} (f : Finite' c) : nat :=
match f with
| Finite'_zero => 0
| Finite'_succ _ f' => Datatypes.S (Finite'_to_nat f')
end.

(* end hide *)

(** * Nielegalna topologia (TODO) *)

(** Tutaj o topologii takiej jak robi Martin Escardó głównie w tej
    książce: "Synthetic topology of data types and classical spaces",
    czyli wyłączamy guard checker i patrzymy jakie programy zatrzymują
    się, a jakie nie. *)

Require Import Lia.

(** ** Kombinatory punktu stałego i nieterminacja *)

(** Da się zrobić kombinator punktu stałego i zamknąć go w monadę/modalność
    tak, żeby sprzeczność nie wyciekła na zewnątrz i żeby wszystko ładnie się
    liczyło, jeżeli wynik nie jest bottomem? TAK! *)

Module SafeFix.

Private Inductive Div (A : Type) : Type :=
| pure : A -> Div A.

Arguments pure {A} _.

Definition divmap {A B : Type} (f : A -> B) (x : Div A) : Div B :=
match x with
| pure a => pure (f a)
end.

Definition divbind {A B : Type} (x : Div A) (f : A -> Div B) : Div B :=
match x with
| pure a => f a
end.

Definition divjoin {A : Type} (x : Div (Div A)) : Div A :=
match x with
| pure (pure a) => pure a
end.

Unset Guard Checking.
Fixpoint efix {A B : Type} (f : (A -> Div B) -> (A -> Div B)) (x : A) {struct x} : Div B :=
  f (efix f) x.
Set Guard Checking.

Arguments efix {A B} f x / : simpl nomatch.

Lemma unfix :
  forall {A B : Type} (f : (A -> Div B) -> (A -> Div B)) (x : A),
    efix f x = f (efix f) x.
Proof.
  intros. unfold efix at 1.
Admitted.

Private Inductive Terminates {A : Type} : Div A -> Prop :=
| terminates : forall x : A, Terminates (pure x).

Definition extract {A : Type} {x : Div A} (t : Terminates x) : A :=
match x with
| pure a => a
end.

Lemma Terminates_pure :
  forall {A : Type} (x : A),
    Terminates (pure x).
Proof.
  constructor.
Defined.

Lemma Terminates_divmap :
  forall {A B : Type} (f : A -> B) {x : Div A},
    Terminates x -> Terminates (divmap f x).
Proof.
  destruct 1; cbn; constructor.
Qed.

Lemma Terminates_divbind :
  forall {A B : Type} (f : A -> Div B) (x : Div A),
    Terminates x -> (forall x : A, Terminates (f x)) -> Terminates (divbind x f).
Proof.
  intros A B f x [] H. cbn. apply H.
Defined.

Definition wut : Div (Div nat) :=
  pure (efix (fun f n => f (1 + n)) 0).

(* Lemma Terminates_divjoin :
  forall {A : Type} (x : Div (Div A)),
    Terminates x -> Terminates (divjoin x).
Proof.
  intros A x []. cbn.
  intros A [[]]. cbn. []. cbn.
Defined. *)

Lemma extract_divmap :
  forall {A B : Type} (f : A -> B) {x : Div A} (t : Terminates x),
    f (extract t) = extract (Terminates_divmap f t).
Proof.
  intros. destruct t. cbn. reflexivity.
Defined.

End SafeFix.

Import SafeFix.

Definition euclid (n m : nat) : Div nat :=
  efix (fun euclid '(n, m) =>
    match n with
    | 0 => pure m
    | _ => euclid (PeanoNat.Nat.modulo m n, n)
    end) (n, m).

Time Compute euclid (2 * 3 * 5 * 7) (2 * 7 * 11).

Lemma euclid_eq :
  forall n m : nat,
    euclid n m
      =
    match n with
    | 0 => pure m
    | _ => euclid (PeanoNat.Nat.modulo m n) n
    end.
Proof.
  intros. unfold euclid. rewrite unfix. reflexivity.
Defined.

Lemma Terminates_euclid :
  forall n m : nat, Terminates (euclid n m).
Proof.
  apply (well_founded_induction Wf_nat.lt_wf (fun n => forall m, Terminates (euclid n m))).
  intros n IH m.
  rewrite euclid_eq.
  destruct n as [| n'].
  - apply Terminates_pure.
  - apply IH. apply PeanoNat.Nat.mod_upper_bound. inversion 1.
Defined.

Definition euclid' (n m : nat) : nat :=
  extract (Terminates_euclid n m).

Compute euclid' 5 2.

Definition div (n m : nat) : Div nat :=
  efix (fun div '(n, m) =>
    if Nat.ltb n m
    then pure 0
    else divmap (plus 1) (div (n - m, m)))
  (n, m).

Compute div 51 12.

Lemma div_eq :
  forall n m : nat,
    div n m
      =
    if Nat.ltb n m
    then pure 0
    else divmap (plus 1) (div (n - m) m).
(* begin hide *)
Proof.
  intros. unfold div. rewrite unfix. reflexivity.
Qed.
(* end hide *)

Lemma Terminates_div :
  forall n m : nat, 0 < m -> Terminates (div n m).
(* begin hide *)
Proof.
  apply (well_founded_induction Wf_nat.lt_wf
          (fun n => forall m, 0 < m -> Terminates (div n m))).
  intros n IH m Hlt.
  rewrite div_eq.
  destruct (Nat.ltb n m) eqn: Hltb.
  - apply Terminates_pure.
  - apply Terminates_divmap. apply IH.
    + apply PeanoNat.Nat.ltb_ge in Hltb. lia.
    + apply PeanoNat.Nat.ltb_nlt in Hltb. lia.
Qed.
(* end hide *)

Definition div' (n m : nat) (H : 0 < m) : nat :=
  extract (Terminates_div n m H).

Compute div' 15 1.

Definition stupid (n : nat) : Div nat :=
  efix (fun stupid n => divmap (plus 1) (stupid (1 + n))) n.

Lemma stupid_eq :
  forall n : nat,
    stupid n
      =
    divmap (plus 1) (stupid (1 + n)).
Proof.
  intros. unfold stupid. rewrite unfix. reflexivity.
Qed.

Lemma nat_bounded_stupid :
  forall (f : nat -> nat),
    (forall n : nat, f n = 1 + f (1 + n)) ->
      forall n m : nat, n <= f m.
Proof.
  induction n as [| n']; cbn; intros m.
  - lia.
  - rewrite H. apply le_n_S. apply IHn'.
Qed.

Lemma Terminates_stupid :
  ~ (forall n : nat, Terminates (stupid n)).
Proof.
  intros H.
  pose (e := fun n => extract (H n)).
  assert (forall n : nat, n <= e 0).
  {
    intros n. apply nat_bounded_stupid.
    intros k. unfold e.
    unfold extract.
    rewrite stupid_eq.
    admit.
  }
  specialize (H0 (1 + e 0)).
  lia.
Admitted.

Definition ack' (n m : nat) : Div nat :=
  efix (fun ack' '(n, m) =>
    match n, m with
    | 0, _ => pure (1 + m)
    | Datatypes.S n', 0 => ack' (n', 1)
    | Datatypes.S n', Datatypes.S m' => divbind (ack' (n, m')) (fun r => ack' (n', r))
    end) (n, m).

Lemma ack'_eq :
  forall n m : nat,
    ack' n m
      =
    match n, m with
    | 0, _ => pure (1 + m)
    | Datatypes.S n', 0 => ack' n' 1
    | Datatypes.S n', Datatypes.S m' => divbind (ack' n m') (fun r => ack' n' r)
    end.
(* begin hide *)
Proof.
  intros. unfold ack'. rewrite unfix. reflexivity.
Qed.
(* end hide *)

Lemma Terminates_ack' :
  forall n m : nat,
    Terminates (ack' n m).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros m.
  - apply Terminates_pure.
  - induction m as [| m'].
    + rewrite ack'_eq. apply IHn'.
    + rewrite ack'_eq. apply Terminates_divbind.
      * assumption.
      * assumption.
Qed.
(* end hide *)

Definition ack (n m : nat) : nat :=
  extract (Terminates_ack' n m).

Compute ack 3 5.