(** * F3v2: Liczby konaturalne [TODO] *)

Set Primitive Projections.

Set Warnings "+cannot-define-projection".
Set Warnings "+non-primitive-record".

(** Zdefiniuj liczby konaturalne oraz ich relację bipodobieństwa. Pokaż,
    że jest to relacja równoważności. *)

(* begin hide *)
Inductive NatF (X : Type) : Type :=
| Z : NatF X
| S : X -> NatF X.

Arguments Z {X}.
Arguments S {X} _.

CoInductive conat : Type :=
{
  out : NatF conat;
}.

Inductive simF (R : conat -> conat -> Prop) : NatF conat -> NatF conat -> Prop :=
| simF_Z : simF R Z Z
| simF_S : forall n1 n2 : conat, R n1 n2 -> simF R (S n1) (S n2).

CoInductive sim (n m : conat) : Prop :=
{
  sim' : simF sim (out n) (out m);
}.

Lemma sim_refl :
  forall n : conat, sim n n.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct (out n) as [| n'].
  - now constructor.
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma sim_sym :
  forall n m : conat, sim n m -> sim m n.
(* begin hide *)
Proof.
  cofix CH.
  intros n m H; constructor.
  destruct H as [[]].
  - now constructor.
  - constructor.
    now apply CH.
Qed.
(* end hide *)

Lemma sim_trans :
  forall a b c : conat, sim a b -> sim b c -> sim a c.
(* begin hide *)
Proof.
  cofix CH.
  intros a b c ab bc.
  constructor.
  destruct ab as [ab], bc as [bc].
  inversion ab; inversion bc; [| congruence.. |].
  - now constructor.
  - constructor.
    now apply CH with n2; [| congruence].
Qed.
(* end hide *)

Inductive simBigF (R : conat -> conat -> Prop) : NatF conat -> NatF conat -> Prop :=
| simBigF_S : forall n1 n2 : conat, R n1 n2 -> simBigF R (S n1) (S n2)
| simBigF_refl : forall n : NatF conat, simBigF R n n
| simBigF_sym : forall n m : NatF conat, simBigF R m n -> simBigF R n m
| simBigF_trans :
    forall (n1 n2 n3 : NatF conat), simBigF R n1 n2 -> simBigF R n2 n3 -> simBigF R n1 n3.

CoInductive simBig (n m : conat) : Prop :=
{
  simBig' : simBigF sim (out n) (out m);
}.

Lemma sim_to_simBig :
  forall n m : conat,
    sim n m -> simBig n m.
Proof.
  intros n m H.
  constructor.
  destruct H as [[]].
  - now constructor.
  - now constructor.
Qed.

Lemma simBig_to_sim :
  forall n m : conat, 
    simBig n m -> sim n m.
Proof.
  cofix CH.
  intros n m H.
  constructor.
  destruct H as [[]].
  - now constructor.
  - now apply (sim_refl {| out := n0 |}).
(*
  - apply simBigF_sym in H.
    apply (Build_simBig {| out := n0 |} {| out := m0 |}) in H.
    apply CH in H. apply H.
*)
  - apply (CH {| out := n0 |} {| out := m0 |}).
    constructor; cbn.
    now apply simBigF_sym.
  - apply (CH {| out := n1 |} {| out := n3 |}).
    constructor; cbn.
    now apply simBigF_trans with n2.