Require Import F2.

Inductive ospec
  {A : Type} (N : Prop) (S : A -> Prop) : option A -> Prop :=
    | ospec_None : N -> ospec N S None
    | ospec_Some : forall a : A, S a -> ospec N S (Some a).

Class Searchable (A : Type) : Type :=
{
    search : (A -> bool) -> option A;
    search_spec :
      forall p : A -> bool,
        ospec
          (forall x : A, p x = false)
          (fun x : A => p x = true)
          (search p)
}.

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
    search p := if p (search_conat p) then Some (search_conat p) else None
}.
Proof.
  intro p. case (p (search_conat p)) eqn: H.
    constructor. assumption.
    constructor. intro n.
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