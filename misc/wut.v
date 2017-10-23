(** * Maximal and minimal principles *)

(** Let's get back to inductive propositions. They differ from ordinary
    inductive types in another way we haven't described yet. *)

Check Empty_set_ind.
(* ==> Empty_set_ind
     : forall (P : Empty_set -> Prop) (e : Empty_set), P e *)

Check unit_ind.
(* ===> unit_ind
     : forall P : unit -> Prop, P tt -> forall u : unit, P u *)

Check bool_ind.
(* ===> bool_ind
     : forall P : bool -> Prop, P true -> P false -> forall b : bool, P b *)

Check nat_ind.
(* ===> nat_ind
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n *)

Check False_ind.
(* ===> False_ind
     : forall P : Prop, False -> P *)

Check True_ind.
(* ===> True_ind
     : forall P : Prop, P -> True -> P *)

Check VeryTrue_ind.
(* ===> VeryTrue_ind
     : forall P : Prop, P -> P -> VeryTrue -> P *)

Check TheTruest_ind.
(* ===> TheTruest_ind
     : forall P : Prop, P -> (TheTruest -> P -> P) -> TheTruest -> P *)

(** As you see, the induction principles for [Empty_set], [unit], [bool]
    and [nat] are very different from these for [False], [True], [VeryTrue]
    and [TheTruest], respectively. But why?

    To answer this question, we have to introduce maximal and minimal
    induction principles. Maximal principles are the ones that you
    are already familiar with. Coq generates them automatically for
    every inductive type living in [Set] or [Type], but not for these
    living in [Prop].

    We can generate maximal principles with the command [Scheme]. By the
    way, here's a joke: Scheme is not a programming language, [Scheme] is
    just a Coq command for generating induction principles. *)

Scheme False_ind_max := Induction for False Sort Prop.
Scheme True_ind_max := Induction for True Sort Prop.
Scheme VeryTrue_ind_max := Induction for VeryTrue Sort Prop.
Scheme TheTruest_ind_max := Induction for TheTruest Sort Prop.

Check False_ind_max.
(* ===> False_ind_max
     : forall (P : False -> Prop) (f : False), P f *)

Check True_ind_max.
(* ===> True_ind_max
     : forall P : True -> Prop, P I -> forall t : True, P t *)

Check VeryTrue_ind_max.
(* ===> VeryTrue_ind_max
     : forall P : VeryTrue -> Prop,
       P proof -> P other_proof -> forall v : VeryTrue, P v *)

Check TheTruest_ind_max.
(* ===> TheTruest_ind_max
     : forall P : TheTruest -> Prop,
       P ShortProof ->
       (forall t : TheTruest, P t -> P (LongProof t)) ->
       forall t : TheTruest, P t *)

(** Compare these carefully with the principles for [Empty_set], [unit],
    [bool] and [nat]. They look very similar, don't they? If you compare
    them to the minimal principles that Coq generated automatically, you
    will also notice that they are more general.

    For example, the minimal principle for [True] suffices to only prove
    propositions ([P : Prop]) and not predicates ([P : True -> Prop]).
    So, why does Coq generate the less general minimal principles than the
    more general maximal ones for propositions?

    To answer this question, first we have to notice that there's other
    side to the coin: maximal principles are more complex than minimal
    principles. So, the question boils down to why we would prefer simpler,
    but less general principles over more complex and more general ones.

    The simpler answer is: we don't care about generality. The more precise
    answer we have already seen is: proof irrelevance. Even though Coq is
    not proof irrelevant by default — we saw we have to explicitly assume
    irrelevance if we want it — it is proof irrelevant at the philosophical
    level.

    This is because we can't use proofs to construct programs. We can only
    use proofs to construct other proofs and, as we saw, when it comes to
    proofs the only thing that matters is whether they exist or not. In
    other words, Coq's philosophical proof irrelevance comes from the fact
    that it was designed to allow the actual proof irrelevance we saw before.

    Coq knows that most likely we won't care about properties of proofs, so
    by default it generates us the minimal principles.

    To finish the comparison, let's have a look at the minimal principles
    that we can generate for [Empty_set], [unit], [bool] and [nat] using
    the [Scheme] command. *)

Scheme Empty_set_ind_min := Minimality for Empty_set Sort Prop.
Scheme unit_ind_min := Minimality for unit Sort Prop.
Scheme bool_ind_min := Minimality for bool Sort Prop.
Scheme nat_ind_min := Minimality for nat Sort Prop.

Check Empty_set_ind_min.
(* ===> Empty_set_ind_min
     : forall P : Prop, Empty_set -> P *)

Check unit_ind_min.
(* ===> unit_ind_min
     : forall P : Prop, P -> unit -> P *)

Check bool_ind_min.
(* ===> bool_ind_min
     : forall P : Prop, P -> P -> bool -> P *)

Check nat_ind_min.
(* ===> nat_ind_min
     : forall P : Prop, P -> (nat -> P -> P) -> nat -> P *)

(** As you see, since they are of the form [P -> ... -> P], the principles
    for [unit], [bool] and [nat] are quite useless.

    If you didn't get it, don't panic. There's another angle from which we
    may view the difference between maximal and minimal principles. To do
    this, let's compare induction principles for [prod] and [sum] with these
    for [and] and [or]. Their induction principles aren't as useless as those
    we saw above, so they will possibly be more illuminating. *)

Check prod_ind.
(* ===> prod_ind
     : forall (A B : Type) (P : A * B -> Prop),
       (forall (a : A) (b : B), P (a, b)) -> forall p : A * B, P p *)

Check sum_ind.
(* ===> sum_ind
     : forall (A B : Type) (P : A + B -> Prop),
       (forall a : A, P (inl a)) ->
       (forall b : B, P (inr b)) -> forall s : A + B, P s *)

Check and_ind.
(* ===> and_ind
     : forall A B P : Prop, (A -> B -> P) -> A /\ B -> P *)

Check or_ind.
(* ===> or_ind
     : forall A B P : Prop, (A -> P) -> (B -> P) -> A \/ B -> P *)
