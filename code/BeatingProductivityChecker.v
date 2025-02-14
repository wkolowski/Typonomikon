(** * F3v2: Liczby konaturalne [TODO] *)

Require Import Coq.Program.Equality.

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
Defined.
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
Defined.
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
Defined.
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
  cofix CH.
  intros n m H.
  constructor.
  destruct H as [[]].
  - now constructor.
  - now constructor.
Defined.

Lemma simBig_to_sim :
  forall n m : conat, 
    simBig n m -> sim n m.
Proof.
  intros n m H.
  constructor.
  destruct H as [H].
  induction H.
  - now constructor.
  - now apply (sim_refl {| out := n0 |}).
  - destruct (sim_sym {| out := m0 |} {| out := n0 |}); [| easy].
    now constructor; cbn.
  - now destruct (sim_trans {| out := n1 |} {| out := n2 |} {| out := n3 |}).
Qed.

Module wut.

Inductive simBigF (R : conat -> conat -> Prop) : NatF conat -> NatF conat -> Prop :=
(* | simBigF_sim : forall n1 n2 : NatF conat, sim {| out := n1 |} {| out := n2 |} -> simBigF R n1 n2 *)
| simBigF_Z : simBigF R Z Z
| simBigF_S : forall n1 n2 : conat, R n1 n2 -> simBigF R (S n1) (S n2)
(* | simBigF_refl : forall n : NatF conat, simBigF R n n *)
| simBigF_sym : forall n m : NatF conat, simBigF R m n -> simBigF R n m
| simBigF_trans :
    forall (n1 n2 n3 : NatF conat), simBigF R n1 n2 -> simBigF R n2 n3 -> simBigF R n1 n3.

CoInductive simBig (n m : conat) : Prop :=
{
  simBig' : simBigF simBig (out n) (out m);
}.

Lemma sim_to_simBig :
  forall n m : conat,
    sim n m -> simBig n m.
Proof.
  cofix CH.
  intros n m H.
  constructor.
  destruct H as [[]].
  - now constructor.
  - constructor.
    now apply CH.
Defined.

Lemma wut :
  forall n1 n2,
    simBig n1 n2 -> sim {| out := S n1 |} {| out := S n2 |}.
Proof.
  cofix CH.
  intros n1 n2 H.
  constructor; cbn.
  destruct H as [H]; inversion H; subst.
  - do 2 constructor.
    rewrite <- H1, <- H2.
    now constructor.
  - do 2 constructor.
    admit.
  - admit.
  - 
Abort.

Lemma simBig_to_sim :
  forall n m : conat, 
    simBig n m -> sim n m.
Proof.
  cofix CH.
  intros n m H.
  destruct H as [H].
  dependent induction H.
  - constructor.
    rewrite <- x, <- x0.
    constructor.
  - constructor.
    rewrite <- x, <- x0.
    constructor.
    apply CH.
Abort.

Lemma simBig_to_sim :
  forall n m : conat, 
    simBig n m -> sim n m.
Proof.
  intros n m H.
  destruct H as [H].
  remember (out n) as n' eqn: Hn'.
  remember (out m) as m' eqn: Hm'.
  induction H.
  - constructor. rewrite <- Hn', <- Hm'. admit.
  - revert n m n1 n2 Hn' Hm' H.
    cofix CH.
    constructor.
    rewrite <- Hn', <- Hm'.
    constructor.
    eapply CH.
Abort.

End wut.