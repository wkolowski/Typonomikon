(** * Seminar: Induction *)

(** This chapter is written in English because its main purpose is to serve
    as notes for my seminar talk whose topic was "Inductive predicates". It
    is a bit broader than that and covers all forms of structural induction,
    including functional induction, and even more. It does not touch the
    topic of well-founded induction, though.

    The grading policy is at the end. *)

(** * Inductive propositions and types with a grain of axioms *)

(** Let's start with inductive propositions: *)

Print False.

(* ===> Inductive False : Prop := *)

Print True.

(* ===> Inductive True : Prop :=
            | I : True *)

(** [False] and [True] have very simple definitions. [False] doesn't have
    any constructors and [True] does have one, called [I]. This name is
    arbitrary — it has to be there, because constructors can't be nameless,
    but doesn't really matter, because we're only interested in its existence,
    not name.

    The definitions are not that interesting if you have seen them already,
    so let's have a look at something weirder: *)

Inductive VeryTrue : Prop :=
    | proof : VeryTrue
    | other_proof : VeryTrue.

(** How is this one different from [True]? Well, [False], [True] and
    [VeryTrue] can be likened to [Empty_set], [unit] and [bool]: *)

Print Empty_set.

(* ===> Inductive Empty_set : Set := .*)

Print unit.

(* ===> Inductive unit : Set :=
            | tt : unit *)

Print bool.

(* ===> Inductive bool : Set :=
            | true : bool
            | false : bool *)

(** The similarities are striking — these two series of types from a
    high-level point of view look (nearly) the same. The dissimilarities
    are more subtle.

    Besides names the only difference lies in the sorts — [Prop] and
    [Set] — but it's a colossal one.

    Note: if a proof isn't there, it's an exercise. *)

Theorem bool_inhabited : bool.
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

Theorem VeryTrue_inhabited : VeryTrue.
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

(** First off, both [bool] and [VeryTrue], which correspond in the series,
    are inhabited. This means that [bool] has an element and [VeryTrue] is
    indeed true. No surprise here. *)

Theorem unit_contractible :
  forall x y : unit, x = y.
(* begin hide *)
Proof. destruct x, y. trivial. Qed.
(* end hide *)

Theorem bool_not_contractible :
  exists x y : bool, x <> y.
(* begin hide *)
Proof.
  exists true, false. inversion 1.
Qed.
(* end hide *)

(** Secondly, [unit] is contractible and [bool] is not. This means roughly
    that [unit] has one element and [bool] has more than one (in fact it
    has two). We could believe that this is also the case for [True] and
    [VeryTrue], but it's not that simple. *)

Theorem True_contractible :
  forall x y : True, x = y.
(* begin hide *)
Proof. destruct x, y. trivial. Qed.
(* end hide *)

Theorem VeryTrue_not_contractible :
  exists x y : VeryTrue, x <> y.
Proof.
  exists proof, other_proof. inversion 1.
Abort.

(** Even though [True] has the same property that holds for [unit],
    it looks like the trickery of [inversion] is not enough to prove
    that [VeryTrue] is contractible. *)

Require Import ProofIrrelevance.

Theorem VeryTrue_contractible :
  forall x y : VeryTrue, x = y.
(* begin hide *)
Proof.
  intros. apply proof_irrelevance.
Qed.
(* end hide *)

(** No, it's not about lack of trickery — it may simply be not true. In
    fact, it's axiom-dependent. In vanilla Coq we can't do much, but if
    we assume the Axiom of Proof Irrelevance, we can prove that both
    constructors of [VeryTrue] construct the very same proof. *)

Check proof_irrelevance.
(* ===> proof_irrelevance :
        forall (P : Prop) (p1 p2 : P), p1 = p2 *)

(** The Axiom of Proof Irrelevance states that all proofs of any proposition
    are equal. This is exactly the statement we wanted to prove. You may
    wonder if we're allowed to assume such an axiom, but it was proved
    that this axiom is consistent with the Calculus of Inductive Constructions
    (so, it won't introduce any contradictions to Coq).

    But before we go on we have to clarify what was meant by "proof" in the
    above statement in order to avoid falling into an equivocation lurking
    in the darkness out there.

    In the context of Coq the word "proof" can mean two things:
    - "proofterm". Proofterm is just a term. To prove [P] we have to
      construct [p : P] and this [p] is the proofterm that proves [P].
    - "proofscript". A proofscript is the text that appears between the
      theorem statement and the keyword [Qed]. *)

(** What I meant by "all proofs of any proposition are equal" could be
    better rephrased as "all proofterms of any proposition are equal". *)

Require Import Logic.FinFun.

(** Note: module FinFun contains definitions of injections, surjections and
    bijections.

    These are not the only differences. *)

Theorem no_bij_unit_bool :
  ~ exists f : unit -> bool, Bijective f.
(* begin hide *)
Proof.
  destruct 1 as [f [g [H H']]].
  assert (H1 := H' true).
  assert (H2 := H' false).
  destruct (g true), (g false). congruence.
Qed.
(* end hide *)

(** Even though there are functions going from [unit] to [bool] and the
    other way around too, they are in no sense equivalences. Particularly,
    [unit] is not in bijection with [bool]. *)

Theorem unit_not_bool : unit <> bool.
(* begin hide *)
Proof.
  intro. assert (forall P : Type -> Prop, P unit <-> P bool).
    intro. rewrite H. firstorder.
    specialize (H0 (fun T => exists f : unit -> T, Bijective f)).
    cbn in H0.
    apply no_bij_unit_bool. rewrite <- H0.
    exists (@id unit). exists (@id unit). firstorder.
Qed.
(* end hide *)

(** Since Leibniz it is known that two equal things must also have the
    same properties. Using this fact we can prove that [unit] is not
    equal to [bool] (since they differ in the property of being in
    bijection with [unit]). *)

Theorem VeryTrue_True : VeryTrue <-> True.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

(** [VeryTrue] and [True] are, however, logically equivalent. This really
    shouldn't surprise us, because both can be proved without any assumptions.
    But this is not all that's true about their relationship. *)

Theorem bij_VeryTrue_True :
  exists f : VeryTrue -> True, Bijective f.
(* begin hide *)
Proof.
  exists (fun _ => I). red. exists (fun _ => proof).
  intuition (apply proof_irrelevance).
Qed.
(* end hide *)

(** From the Axiom of Proof Irrelevance it follows that [VeryTrue] and
    [True] are in bijection with each other. This too isn't that much
    of a surprise because we have shown before that they both are
    contractible, i.e. both have only a single element. *)

Module Classical.

Require Import ClassicalFacts.

(** There's another axiom we can assume: the Axiom of Propositional
    Extensionality, which lives in the module [ClassicalFacts]. *)

Print prop_extensionality.
(* ===> prop_extensionality =
        forall A B : Prop, A <-> B -> A = B : Prop *)

(** This axiom states that if two propositions are logically equivalent,
    then they are equal. It also has been proved that adding it to Coq
    is consistent (even if we already have proof irrelevance). *)

Axiom prop_ext : prop_extensionality.

(** Note: assuming this axiom is technically realized differently than
    assuming [proof_irrelevance]. To assume [proof_irrelevance], we only
    had to import the relevant module and the axiom was sitting there
    waiting for us. However, to assume [prop_extensionality] we have to
    write it out explicitly after importing the module. *)

Theorem VeryTrue_is_True : VeryTrue = True.
(* begin hide *)
Proof.
  apply prop_ext. apply VeryTrue_True.
Qed.
(* end hide *)

(** Using this axiom, we can prove that [VeryTrue] and [True] are not only
    logically equivalent and in bijection with each other, but actually
    equal. Propositions are very different from ordinary types. *)

End Classical.

(** Let's try to sum up the above lesson using slogans and metaphors.
    An often repeated phrase is "propositions as types". By this it is
    most often meant that proposition can be represented by types and
    logic can be reduced to operations on types.

    This is mostly accurate, but as we have seen, proposition and types
    are not exactly the same thing in Coq. We can imagine that a type is
    just a bag of dots. The bag is the type proper and the dots are just
    repeated applications of the type's constructors.

    We can then in search of dots put our hand into the bag and if there
    are some, we can pull them out. If there are many of them, we can
    distinguish them by looking at them or doing more complicated operations.

    Propositions can be thought of as bags of dots in the same way, but if
    we put our hand into the bag, only two things can possibly happen:
    - We pull out a big blob of glue with some dots glued to it. We can't
      unglue them, but we know there are some dots
    - There's nothing *)

(** The moral of this story is as follows: in case of types (those terms
    whose type is [Set] or [Type], to be more precise) we are interested
    in what the terms look like, how many are there and so on. In the
    case of propositions (terms whose type is [Prop]) we can possibly
    only be interested in whether there are any terms (proofs) or not. *)

(** **** Exercise (easy) *)

(** Prove that [bool <> nat]. *)

(** * On the number of constructors *)

(** Let's consider how the truth of a proposition depends on the number
    of its constructors. *)

Inductive TheTruest : Prop :=
    | ShortProof : TheTruest
    | LongProof : TheTruest -> TheTruest.

(** This proposition dangerously resembles the type [nat]. It appears to
    have an infinite amount of proofs constructred by two constructors,
    one of which corresponds to [0] and the other to [S]. *)

Theorem TheTruest_True : TheTruest <-> True.
(* begin hide *)
Proof. repeat constructor. Qed.
(* end hide *)

Theorem TheTruest_contractible :
  forall x y : TheTruest, x = y.
(* begin hide *)
Proof.
  apply proof_irrelevance.
Qed.
(* end hide *)

(** This is not really the case. Since all the proofs are equal to each
    other, there in fact is only a single proof. So even though this
    proposition has two constructors one of which is recursive, it
    resembles [unit] more than [nat], to which it would be equivalent
    if it lived in [Set] or [Type].

    This leads us to ask a somewhat contrived question: for propositions,
    are all constructors besides one useless? Or rather, does a single one
    suffice to make a proposition true? *)

Inductive BePatient : Prop :=
    | the_longest_proof : BePatient -> BePatient.

(** The above proposition has a single constructor, so we could be led
    to believe it's true. *)

Theorem BePatient_false : ~ BePatient.
(* begin hide *)
Proof. induction 1. trivial. Qed.
(* end hide *)

Theorem BePatient_False : BePatient <-> False.
(* begin hide *)
Proof.
  split.
    apply BePatient_false.
    inversion 1.
Qed.
(* end hide *)

(** However it happens that this proposition is not at all true. How is
    this possible? It has a constructor, so it must be true... not quite.
    Recall that we can build terms of inductive types by applying their
    constructors only a _finite_ number of times.

    The "word" finite is crucial here. If we try to apply the constructor
    [the_longest_proof] repeatedly, our only hope at finishing is if we
    do it _ad infinitum_. This is exactly the thing that is forbidden by
    the definition of inductive types.

    So, a proposition with one constructor can be false. We could add
    more constructors like [the_longest_proof] and they wouldn't help
    if all of them were recursive. Thus we have proven (but only at the
    metatheoretical level) that a false proposition can have any number
    of constructors: 0 ([False]), 1 ([BePatient]), 2 or more ([BePatient]
    on steroids with more constructors).

    But what about nonrecursive constructors? Can a proposition with a
    nonrecursive constructor be false? *)

Inductive LatentFalsity : Prop :=
    | I_am_true : False -> LatentFalsity.

(** Well, this one has one nonrecursive constructor, so again we could be
    led to believe it's true... but beware. *)

Theorem LatentFalsity_false : ~ LatentFalsity.
(* begin hide *)
Proof.
  destruct 1. destruct H.
Qed.
(* end hide *)

Theorem LatentFalsity_False : LatentFalsity <-> False.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

(** This proposition is false because its only constructor takes a proof
    of [False] as an argument. Since there isn't one, this constructor can
    never be used to build a proof of [LatentFalsity].

    Our voyage into the land of constructors looks rather grim. We have
    met false propositions with any number of constructors, recursive or
    not. We have also seen that true propositions can have one or more
    constructors.

    The only certainty we discovered is that a proposition without any
    constructors must necessarily be false. As soon as it has at least
    one, it can be provable or not depending on how they look like. *)

(** **** Exercise (easy) *)

(** Does [TheTruest = VeryTrue] hold? If yes, under what assumptions? *)

(* begin hide *)
Theorem no_bij_bool_nat :
  ~ exists f : bool -> nat, Bijective f.
Proof.
  destruct 1 as [f [g [H H']]].
  assert (H0 := H' 0).
  assert (H1 := H' 1).
  assert (H2 := H' 2).
  destruct (g 0), (g 1), (g 2); congruence.
Qed.

Theorem bool_not_nat : bool <> nat.
Proof.
  intro. assert (forall P : Type -> Prop, P bool <-> P nat).
    rewrite H. firstorder.
    specialize (H0 (fun T => exists f : bool -> T, Bijective f)).
      cbn in H0. apply no_bij_bool_nat. rewrite <- H0.
      exists (@id bool), (@id bool). auto.
Qed.

(** [VeryTrue = True] holds if we assume propositional extensionality. *)
(* end hide *)

(** **** Exercise (medium) *)

(** Find a simple heuristic for deciding (at the metatheoretical level)
    whether an inductive proposition can be proven or not. Assume that
    this inductive proposition's constructors can only refer to other
    inductive propositions. *)

(* begin hide *)
(** A proposition is true if it has at least one nonrecursive constructor
    whose all arguments' types are nonempty. *)
(* end hide *)

(** * Induction and induction principles for types *)

(** Let's say we want to prove that all elements of a type [T] have some
    property. How can we go about it? There are three possibilites that
    depend on the particular form of [T].

    First of all, if [T] is finite, then we can prove our desired statement
    just by considering each element of [T] separately. This reasoning can
    be captured by a case analysis principle. Such a principle is a theorem
    of the form [forall P : T -> Prop, P x1 -> ... -> P xN -> forall x : T,
    P x], where [x1], ..., [xN] are all the elements of [T].

    Let's see an example case analysis principle for [bool]: *)

Check bool_ind.
(* ===> bool_ind :
        forall P : bool -> Prop,
          P true -> P false -> forall b : bool, P b *)

(** Note: [bool_ind] is the case analysis principle for [bool] that Coq
    automatically generated for us. The suffix [_ind] stands for induction,
    since case analysis principles are a special case of induction principles.
    Because induction principles can be used not only to prove that all terms
    have some property, but also to define a dependent function, Coq actually
    generates us three principles for each definition we make.

    For type [T] these are called [T_rect], [T_rec] and [T_ind]. They differ
    only in the sort of the type that depends on [T]: for [T_rect] this is
    [Type], for [T_rec] it's Set and for [T_ind] it's [Prop]. The two latter
    are implemented by simply calling [T_rect].

    We see that in order to prove that all terms of type [bool] have some
    property, we only have to prove that [true] has it and that [false]
    also has it. This is because these two are the only terms of type [bool].*)

Print bool_rect.
(* ===> bool_rect =
        fun (P : bool -> Type)
            (f : P true) (f0 : P false) (b : bool) =>
              if b as b0 return (P b0) then f else f0
        : forall P : bool -> Type, P true -> P false ->
            forall b : bool, P b *)

(** When we look at the definition we can see an [if] here. This is just a
    syntactic sugar for [match], which shows us that the principle is not
    magical or built-in and can be derived manually using pattern matching.

    But how to use this principle to prove something? *)

Theorem negb_involutive' :
  forall b : bool, negb (negb b) = b.
Proof.
  apply bool_ind; cbn; trivial.
Restart.
  destruct b; cbn; trivial.
Qed.

(** Since an induction principle is just a normal theorem, we can apply it
    like a theorem. This is precisely what the [destruct] tactic does — it
    applies for us the standard case analysis principle associated with the
    type of its argument.

    Let's get back to our question of how to prove that all terms of some
    type have some property. The above was just the finite case for inductive
    types. But what if our type is infinite?

    This is the second case. In general, if our type is infinite and we want
    to be done with our proving in finite time and using finite resources,
    then we're doomed. A representative example of this case are functions
    [nat -> nat] — there are so many of them that we can't prove anything
    nontrivial about all of them.

    Not all hope is lost, however. The third case is: our type is infinite,
    but defined inductively. In this case we can do as much as in the finite
    case. Even though we can't check each element of [T] separately, we know
    that it is "finitely generated", meaning that it can be constructed by
    applying one of finitely many constructors of [T] a finite number of
    times.

    It turns out this is enough for us. Let's see how the induction principle
    for [nat] looks like. *)

Check nat_ind.
(* ===> nat_ind :
        forall P : nat -> Prop,
          P 0 -> (forall n : nat, P n -> P (S n)) ->
            forall n : nat, P n *)

(** To prove that all natural numbers have the property [P], we only have
    to prove that [0] has it and that [S n] has it under the assumption that
    [n] does. This is because these two constructors are everything we need
    in order to generate all natural numbers.

    The second argument is of particular interest to us: if it were
    [forall n : nat, P (S n)], we would only have a case analysis
    principle. However, it also has the premise [P n], which makes it
    recursive. *)

Print nat_rect.
(* ===> nat_rect =
        fun (P : nat -> Type) (f : P 0)
            (f0 : forall n : nat, P n -> P (S n)) =>
        fix F (n : nat) : P n :=
        match n as n0 return (P n0) with
            | 0 => f
            | S n0 => f0 n0 (F n0)
        end
        : forall P : nat -> Type,
            P 0 -> (forall n : nat, P n -> P (S n)) ->
              forall n : nat, P n *)

(** As we see, this principle too is neither magical nor built-in. It can
    be derived manually using just pattern matching and recursion. This is
    the case for all induction principles of inductive types: they can be
    derived manually using [match] and [fix]. *)

Theorem plus_assoc' :
  forall a b c : nat, a + (b + c) = (a + b) + c.
Proof.
  apply nat_ind.
Restart.
  apply (nat_ind
  (fun a : nat => forall b c : nat, a + (b + c) = (a + b) + c)).
    cbn. trivial.
    cbn. intros. rewrite H. trivial.
Restart.
  induction a; cbn; intros.
    trivial.
    rewrite IHa. trivial.
Defined.

(** As in the case of [bool_ind], we can use our induction principle just
    by applying it. This time however it is a bit harder: simply doing
    [apply] is weird, because it produces three goals, first of which is
    equivalent to the original one, the second is a trivial implication and
    the third asks us for a natural number.

    It works that way because Coq can't guess what is the [P : nat -> Prop]
    that we want to use [nat_ind] with. We can solve this problem by giving
    it manually, just as in our second try.

    We also see that the tactic [induction] is there to do just this for us
    automatically: it correctly identifies the [P] we want to use and then
    applies the induction principle. *)

(** **** Exercise (medium) *)

(** Find a simple metatheoretic algorithm for generating standard induction
    principles for any inductive type [T]. *)

(** * Parameters and indices *)

(** It's high time to see how to define inductive predicates, relations and,
    more generally, families of types. There are two ways: using parameters
    and indices. After we study both in separation, we will compare them.

    A parametric family of inductive types looks like this: *)

Print option.
(* ===> Inductive option (A : Type) : Type :=
            | Some : A -> option A
            | None : option A *)

(** Because [(A : Type)] appears before the final colon, [option] is not
    a type, but a family of types, parametrized by a type [A]. We can see
    this with the [Check] command. *)

Check option.
(* ===> option : Type -> Type *)

(** Parametric definitions basically tell Coq to define a separate inductive
    type for every possible value of the parameter. In the constructors of
    the type family, the parameter is fixed: every time it appears, it has
    to be the same as in the header of the inductive definition.

    This is sometimes a limitation, but often it's just fine. The most common
    use of parameters is the one presented above: defining polymorphic types,
    containers, relations and predicates. We can easily find more examples of
    such a usage: *)

Print prod.
(* ===> Inductive prod (A B : Type) : Type :=
            | pair : A -> B -> A * B *)

Print sum.
(* ===> Inductive sum (A B : Type) : Type :=
            | inl : A -> A + B
            | inr : B -> A + B *)

Print sigT.
(* ===> Inductive sigT (A : Type) (P : A -> Type) : Type :=
            | existT : forall x : A, P x -> {x : A & P x} *)

Print and.
(* ===> Inductive and (A B : Prop) : Prop :=
            | conj : A -> B -> A /\ B *)

Print or.
(* ===> Inductive or (A B : Prop) : Prop :=
            | or_introl : A -> A \/ B
            | or_intror : B -> A \/ B *)

Print ex.
(* ===> Inductive ex (A : Type) (P : A -> Prop) : Prop :=
            | ex_intro : forall x : A, P x -> exists y, P y *)

(** We see that parameters are engouh to implement a whole bunch of most
    common polymorphic types like products, sums and dependent pairs.

    On the other hand, we can define fully general indexed families of
    types like this: *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

(** Here we have nothing before the final colon (the one after [even]),
    so there aren't any parameters. However, after the colon we see
    [nat -> Prop], which means [even] is a family of propositions indexed
    by a natural number, i.e. a predicate on [nat]. We can verify this
    with the command [Check]: *)

Check even.
(* ===> even : nat -> Prop *)

(** In the constructors of [even], the index is not fixed: in [even0] it
    is [0], whereas in [evenSS] it is [S (S n)], which is different from
    [0]. Because of this, indexed families are more general than parametric
    families. *)

(** **** Exercise (easy) *)

(** These exercises are stolen from the first chapter of Essentials of
    Programming Languages (exercises 1.1, 1.2). Each one is in a separate
    module in order to avoid name clashes. Do them.

    You can use the tactic [omega], which can solve arithmetical goals with
    [0], [S], [+] and multiplication by a constant. *)

Require Import Omega.

Module Ex1_1.

Inductive P : nat -> Prop :=
    | c0 : P 2
    | c1 : forall n : nat, P n -> P (S (S (S n))).

Theorem P_char :
  forall n : nat, P n <-> exists k : nat, n = 2 + 3 * k.
(* begin hide *)
Proof.
  split.
    induction 1.
      exists 0. cbn. trivial.
      destruct IHP as [k IH]. exists (S k). rewrite IH. omega.
    destruct 1 as [k H]. subst. induction k as [| k'].
      cbn. constructor.
      replace (2 + 3 * S k') with (S (S (S (2 + 3 * k')))).
        constructor. assumption.
        omega.
Qed.
(* end hide *)

End Ex1_1.

Module Ex1_2.

Inductive P : nat -> Prop :=
    | c0 : P 1
    | c1 : forall n : nat, P n -> P (2 + n)
    | c2 : forall n : nat, P n -> P (3 + n).

Theorem P_char :
  forall n : nat, P n <-> exists k l : nat, n = 1 + 2 * k + 3 * l.
(* begin hide *)
Proof.
  split.
    induction 1.
      exists 0, 0. cbn. trivial.
      destruct IHP as [k [l IH]]. exists (S k), l. subst. cbn. omega.
      destruct IHP as [k [l IH]]. exists k, (S l). subst. cbn. omega.
    destruct 1 as [k [l H]]. subst. induction k as [| k'].
      induction l as [| l'].
        cbn. constructor.
        replace (P _) with (P (3 + 1 + 3 * l')).
          apply c2. cbn in *. assumption.
          f_equal. omega.
      replace (P _) with (P (2 + 1 + 2 * k' + 3 * l)).
        constructor. assumption.
        f_equal. omega.
Qed.
(* end hide *)

End Ex1_2.

Module Ex1_3.

Inductive P : nat -> nat -> Prop :=
    | c0 : P 0 1
    | c1 : forall n m : nat, P n m -> P (1 + n) (2 + m).

Theorem P_char :
  forall n m : nat, P n m <-> m = 1 + 2 * n.
(* begin hide *)
Proof.
  split.
    induction 1.
      trivial.
      subst. omega.
    intros ->. induction n as [| n'].
      cbn. constructor.
      replace (1 + 2 * _) with (2 + 1 + 2 * n').
        constructor. assumption.
        omega.
Qed.
(* end hide *)

End Ex1_3.

Module Ex1_4.

Inductive P : nat -> nat -> Prop :=
    | c0 : P 0 0
    | c1 : forall n m : nat, P n m -> P (S n) (m + 2 * n + 1).

Theorem P_char :
  forall n m : nat, P n m <-> m = n * n.
(* begin hide *)
Proof.
  split.
    induction 1.
      trivial.
      subst. cbn. rewrite (mult_comm _ (S n)). cbn. omega.
    intros ->. induction n as [| n'].
      cbn. constructor.
      replace (S n' * S n') with (n' * n' + 2 * n' + 1).
        constructor. assumption.
        subst. cbn. rewrite (mult_comm _ (S n')). cbn. omega.
Qed.
(* end hide *)

End Ex1_4.

Module Ex2_1.

Inductive P : nat -> nat -> Prop :=
    | c0 : P 0 1
    | c1 : forall n m : nat, P n m -> P (1 + n) (7 + m).

Theorem P_char :
  forall n m : nat, P n m <-> m = 1 + 7 * n.
(* begin hide *)
Proof.
  split.
    induction 1.
      cbn. trivial.
      omega.
    intros ->. induction n as [| n'].
      cbn. constructor.
      cbn. rewrite <- !plus_n_Sm. constructor. assumption.
Qed.
(* end hide *)

End Ex2_1.

Module Ex2_2.

Inductive P : nat -> nat -> Prop :=
    | c0 : P 0 1
    | c1 : forall n m : nat, P n m -> P (S n) (2 * m).

Require Import FunInd.

Function pow2 (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => 2 * pow2 n'
end.

Theorem P_char :
  forall n m : nat, P n m <-> m = pow2 n.
(* begin hide *)
Proof.
  split.
    induction 1; cbn; omega.
    intros ->. induction n as [| n']; cbn; constructor; assumption.
Qed.
(* end hide *)

End Ex2_2.

Module Ex2_3.

Inductive P : nat -> nat -> nat -> Prop :=
    | c0 : P 0 0 1
    | c1 : forall a b c : nat, P a b c -> P (S a) c (b + c).

Function fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') => fib n' + fib n''
end.

Theorem P_char :
  forall a b c : nat, P a b c <-> b = fib a /\ c = fib (S a).
(* begin hide *)
Proof.
  split.
    induction 1.
      cbn. split; trivial.
      destruct IHP; subst; split; cbn; omega.
    intros [-> ->]. induction a as [| a']; cbn in *.
      constructor.
      rewrite plus_comm. constructor. assumption.
Qed.
(* end hide *)

End Ex2_3.

Module Ex2_4.

Inductive P : nat -> nat -> nat -> Prop :=
    | c0 : P 0 1 0
    | c1 : forall a b c : nat, P a b c -> P (1 + a) (2 + b) (b + c).

Theorem P_char :
  forall a b c : nat, P a b c <-> b = 1 + 2 * a /\ c = a * a.
(* begin hide *)
Proof.
  split.
    induction 1.
      cbn. split; trivial.
      destruct IHP; subst. split; cbn in *.
        omega.
        rewrite (mult_comm _ (S a)). cbn. omega.
    intros [-> ->]. induction a as [| a']; cbn.
      constructor.
      rewrite (mult_comm _ (S _)). replace (P _ _ _) with
      (P (1 + a') (2 + 1 + 2 * a') ((1 + 2 * a') + (a' * a'))).
        constructor. assumption.
        f_equal; cbn; omega.
Qed.
(* end hide *)

End Ex2_4.

(** **** Exercise (easy) *)

(** This exercise is also stolen from Essentials of Programming Languages
    (besides the last part of it, which is mine).

    Define two inductives predicates [T] and [T'], such that:
    - they both satisfy the property [P]
    - they are not equal
    - [T] is contained in [T']  *)

Module Ex3.

Definition P (R : nat -> Prop) : Prop :=
  R 0 /\ forall n : nat, R n -> R (3 + n).

(* begin hide *)
Inductive T : nat -> Prop :=
    | T_c0 : T 0
    | T_c1 : forall n : nat, T n -> T (3 + n).

Inductive T' : nat -> Prop :=
    | T'_c0 : T' 0
    | T'_c1 : T' 1
    | T'_c2 : forall n : nat, T' n -> T' (3 + n).
(* end hide *)

Theorem P_T : P T.
(* begin hide *)
Proof.
  red. split.
    constructor.
    induction n as [| n']; cbn; intros; constructor; assumption.
Qed.
(* end hide *)

Theorem P_T' : P T'.
(* begin hide *)
Proof.
  red. split.
    constructor.
    induction n as [| n']; cbn; intros; constructor; assumption.
Qed.
(* end hide *)

Theorem T_not_T' : T <> T'.
(* begin hide *)
Proof.
  intro. cut (forall P : (nat -> Prop) -> Prop, P T <-> P T').
    intro. assert (~ T 1).
      inversion 1.
      apply H1. rewrite (H0 (fun T => T 1)). constructor.
    intro. rewrite H. reflexivity.
Qed.
(* end hide *)

Theorem T_sub_T' :
  forall n : nat, T n -> T' n.
(* begin hide *)
Proof.
  induction 1; constructor; auto.
Qed.
(* end hide *)

End Ex3.

(** Parameters and indices are not mutually exclusive. They can be combined
    freely. A typical example of such usage is the less or equal order
    relation on the natural numbers. *)

Print le.
(* ===> Inductive le (n : nat) : nat -> Prop :=
            | le_n : n <= n
            | le_S : forall m : nat, n <= m -> n <= S m *)

(** In the definition of [le], the parameter [n] is fixed in all constructors,
    but the index varies: in [le_n] it is [n], but in [le_S] it is first [m]
    and then [S m]. Because of this it can't be rewritten using parameters
    only, but it can be rewritten using only indices. *)

Inductive le' : nat -> nat -> Prop :=
    | le'_n : forall n : nat, le' n n
    | le'_S : forall n m : nat, le' n m -> le' n (S m).

(** We see that in the definition of [le'] we have to quantify over [n] in
    each constructor separately in order to use it. This is a disadvantage
    of indexed families: if the index doesn't vary, we have to write more
    code when compared to a definition using a parameter instead. *)

Theorem le_le' :
  forall n m : nat, n <= m <-> le' n m.
(* begin hide *)
Proof.
  split; induction 1; cbn; intros; constructor; auto.
Qed.
(* end hide *)

Theorem le_plus :
  forall n m k : nat, le n m -> le (n + k) (m + k).
(* begin hide *)
Proof.
  induction 1; cbn; intros; constructor; assumption.
Qed.
(* end hide *)

Theorem le'_plus :
  forall n m k : nat, le' n m -> le' (n + k) (m + k).
(* begin hide *)
Proof.
  induction 1; cbn; intros; constructor; assumption.
Qed.
(* end hide *)

(** We can easily prove that both definitions yield equivalent relations.
    Moreover, it is equally easy to prove both [le_plus] and [le'_plus].
    So, which of these two definitions is better? The answer is that [le]
    is better. To see it, let's take a look at the induction principles. *)

Check le_ind.
(* ===> le_ind :
        forall (n : nat) (P : nat -> Prop),
          P n -> (forall m : nat, n <= m -> P m -> P (S m)) ->
            forall n0 : nat, n <= n0 -> P n0 *)

Check le'_ind.
(* ===> le'_ind :
        forall P : nat -> nat -> Prop,
          (forall n : nat, P n n) ->
          (forall n m : nat, le' n m -> P n m -> P n (S m)) ->
            forall n n0 : nat, le' n n0 -> P n n0 *)

(** Don't wory if you don't understand these principles yet. We will come
    back to them later. The only thing to you need to notice now is that
    [le'_ind] is more complex than [le_ind].

    Because using parameters means writing less code while having simpler
    induction principles, we should prefer them wherever possible. There
    isn't much more to be said: knowing whether to use parameters or
    indices comes with practice. The only simple heuristic is that often
    you will want types (and propositions) to be parameters.

    If you don't know which one to use, you may use indices first and then
    check whether any one of them is fixed throughout the definition. If
    there is one, you can refactor it into a parameter.

    Let's now proceed to learn about induction principles for families of
    types. *)

(** * Induction principles for type families *)

(** Now that we know how to define parametric and indexed families of types
    and how to derive standard recursion principles for ordinary inductive
    types, the next natural question to consider is how to derive induction
    principles for families of types. Let's take the next step on our path
    to enlightenment.

    Let's start by looking at parametric families. *)

Module MonomorphicList.

(** We will make a new module in order not pollute the global namespace.
    The name [MonomorphicList] means that we're going to define lists
    that can hold elements of only a single type. *)

Parameter A : Type.

(** We will call this type [A]. The command [Parameter] is a synonym of
    [Axiom], [Hypothesis] and a few more. *)

Inductive listA : Type :=
    | nilA : listA
    | consA : A -> listA -> listA.

(** [listA] is just like [list A] (note the lack of space in the first
    name), but it's not parametric. Rather, the [A] is fixed. Let's
    compare the induction principle for [listA] with that of [list]. *)

Check listA_ind.
(* ===> listA_ind :
        forall P : listA -> Prop,
          P nilA ->
          (forall (a : A) (l : listA), P l -> P (consA a l)) ->
            forall l : listA, P l *)

Check list_ind.
(* ===> list_ind :
        forall (A : Type) (P : list A -> Prop),
          P nil ->
          (forall (a : A) (l : list A), P l -> P (a :: l)%list) ->
            forall l : list A, P l *)

(** The principle [listA_ind] says that in order to prove that all [listA]s
    have some property [P : listA -> Prop], it is necessary to prove that
    [P] holds for [nilA] and that if it holds for [l], then it holds for
    [consA a l] where [a : A] is arbitrary. Not a big surprise.

    If we look at the principle for [list], it says nearly the same. The
    only difference is that the type [A] is not fixed. It is a parameter
    and this is reflected in the principle: the first quantifier says
    [forall (A : Type)].

    When it comes to induction principles for parametric families, this is
    it: quantifiers have to first quantify over the parameters of the type
    family. The rest of the principle is as usual. *)

End MonomorphicList.

(** We have described only maximal principles for parametric families, but
    don't worry: the minimal ones work exactly the same way, so let's move
    on to indexed families. *)

Module IndexedList.

Inductive ilist : Type -> Type :=
    | inil : forall A : Type, ilist A
    | icons : forall A : Type, A -> ilist A -> ilist A.

(** We will continue the above comparison by looking at the induction
    principle of a polymorphic list type, but written using indices
    instead of parameters. *)

Check icons _ 5 (icons _ 42 (inil _)).
(* ===> icons nat 5 (icons nat 42 (inil nat)) : ilist nat *)

Fail Check icons _ 42 (icons _ true (inil _)).
(* ===> The term "icons bool true (inil bool)" has type "ilist bool"
        while it is expected to have type "ilist nat". *)

(** This type is just like the ordinary [list]: we can have lists of
    elements of any type we like, but we can't put elements of different
    types in the same list. *)

Check ilist_ind.
(* ===> ilist_ind :
        forall P : forall T : Type, ilist T -> Prop,
          (forall A : Type, P A (inil A)) ->
          (forall (A : Type) (a : A) (i : ilist A),
            P A i -> P A (icons A a i)) ->
              forall (T : Type) (i : ilist T), P T i *)

(** The principle is much more complex than that for ordinary [list]s.
    First thing to notice is that there is no quantification over the
    type [T] at the beginning of the principle: [T] in theory can be
    different each time it appears, so we can't quantify it once and
    for all (even if in reality it is always the same).

    Because of this, we havy to quantify over it each time separately.
    This can be seen in the type of the predicate [P]. It is a predicate
    on [ilist T], but in order to be well-typed it has to quantify over
    [T : Type].

    Then the principle looks very similar to that of [list], but as we said
    before, the case for each constructor has to quantify over [T] (here
    called [A]) separately. The end of the principle is also similar, but
    once again a quantification over [T] appears.

    This is it: induction principles for indexed families are about having
    to quantify over the indices separately each time they appear somewhere. *)

End IndexedList.

(** The last thing are definitions having both parameters and indices. They
    adhere to the above rules: in their principles parameters are quantified
    over right at the start and the indices are quantified over separately
    each time they appear. *)

(** * Maximal and minimal principles *)

(** If you look carefully at the induction principle for [le], it seems not
    to follow the rules we saw above. This is because propositions (and all
    families of propositions) are treated a bit differently from ordinary
    types (and type families). Our goal in this subchapter will be to learn
    about this difference.

    Let's compare the induction principles for [prod] and [sum] (which live
    in [Type]) with [and] and [or], their counterparts living in [Prop].
    Before we start, I have to admit that I lied to you once more.

    I told you that for every inductive type we define, Coq generates us
    three induction principles. This is actually the case only for types
    living in [Set] and [Type]. For these in [Prop], only one induction
    principles is generated.

    Therefore, in our comparison we will compare the principles [prod_rect]
    and [sum_rect] to [and_ind] and [or_ind]. *)

Check prod_rect.
(* ===> prod_rect :
        forall (A B : Type) (P : A * B -> Type),
          (forall (a : A) (b : B), P (a, b)) ->
            forall p : A * B, P p *)

Check sum_rect.
(* ===> sum_rect :
        forall (A B : Type) (P : A + B -> Type),
          (forall a : A, P (inl a)) ->
          (forall b : B, P (inr b)) ->
            forall s : A + B, P s *)

Check and_ind.
(* ===> and_ind :
        forall A B P : Prop,
          (A -> B -> P) -> A /\ B -> P *)

Check or_ind.
(* ===> or_ind :
        forall A B P : Prop,
          (A -> P) -> (B -> P) -> A \/ B -> P *)

(** We could have expected them to be very alike, since the only differences
    between [prod]/[and] and [sum]/[or] (and the associated principles) are
    in the sorts. Yet they are very different. Why is this?

    In order to answer, we have to introduce the distinction between maximal
    and minimal induction principles. All principles you have seen until now
    (not including [and_ind]/[or_ind]) were maximal principles. When we define
    an inductive type or family living in [Set] or [Type], a maximal principle
    is generated for it by default. But when its sort is [Prop], a minimal
    principle is generated.

    It is not the case however that maximal principles are unique to [Set]s
    and [Type]s and minimal principles are unique to [Prop]s. We can have
    both for an inductive type of any sort. To understand the distinction,
    let's generate minimal principles for [prod] and [sum].

    We can do this with the command [Scheme]. By the way, here's a joke:
    Scheme is not a programming language, [Scheme] is just a Coq command
    for generating induction principles. *)

Scheme prod_rect_min := Minimality for prod Sort Type.
Scheme sum_rect_min := Minimality for sum Sort Type.

Check prod_rect_min.
(* ===> prod_ind_min :
        forall (A B : Type) (P : Type),
          (A -> B -> P) -> A * B -> P *)

Check sum_rect_min.
(* ===> sum_ind_min :
        forall (A B : Type) (P : Type),
          (A -> P) -> (B -> P) -> A + B -> P *)

(** These are much more like the principles for [and]/[or] than the maximal
    principles for [prod]/[sum].

    [prod_rect] tells us that in order to define a dependent function
    [forall p : A * B, P p], we have to provide a dependent function
    [forall (a : A) (b : B), P (a, b)]. On the other hand, [prod_rect_min]
    tells us that in order to define a nondependent function [A * B -> P]
    we have to provide another nondependent function [A -> B -> P].

    Likewise [sum_rect] tells us that in order to define a dependent
    function [forall s : A + B, P s] we have to provide two dependent
    functions [forall a : A, P (inl a)] and [forall b : B, P (inr b)].
    On the other hand, [sum_rect_min] tells us that in order to define
    a nondependent function [A + B -> P] we have to provide two
    nondependent functions [A -> P] and [B -> P].

    This is it! The distinction between maximal and minimal principles
    boils down to the fact that maximal principles are for defining
    dependent functions (and proving predicates), whereas the minimal
    ones are for nondependent functions (and proving propositions).

    So, maximal principles are more general than minimal principles.
    The last question that remains is: why are the less general
    principles generated by Coq, if it can generate the more general
    ones?

    To answer this, let's first have a look at the maximal principles
    for [and] and [or]. These can be generated with a different variant
    of the command [Scheme]. *)

Scheme and_ind_max := Induction for and Sort Prop.
Scheme or_ind_max := Induction for or Sort Prop.

Check and_ind_max.
(* ===> and_ind_max :
        forall (A B : Prop) (P : A /\ B -> Prop),
          (forall (a : A) (b : B), P (conj a b)) ->
            forall a : A /\ B, P a *)

Check or_ind_max.
(* ===> or_ind_max :
        forall (A B : Prop) (P : A \/ B -> Prop),
          (forall a : A, P (or_introl a)) ->
          (forall b : B, P (or_intror b)) ->
            forall o : A \/ B, P o *)

(** We now see another side of the coin: the maximal principles are not
    only more general, but also more complex. So, the question boils down
    to why should we prefer simplicity over generality.

    The last thing we have to do is notice that the generality is really
    just the ability to prove properties of proofs of propositions. They
    are uninteresting because when we assume proof irrelevance, for any
    property [P], either all proofs have it or none has.

    However, what if we don't assume proof irrelevance? Even though Coq
    is not proof irrelevant by default — we saw we have to explicitly
    assume irrelevance if we want it — it is proof irrelevant at the
    philosophical level.

    This is because we can't use proofs to construct programs. We can only
    use proofs to construct other proofs and, as we saw, when it comes to
    proofs the only thing that matters is whether they exist or not. In
    other words, Coq's philosophical proof irrelevance comes from the fact
    that it was designed to allow the actual proof irrelevance.

    To sum it up: the mere ability to assume irrelevance makes investigating
    properties of proofs uninteresting and therefore we are not interested
    in having maximal induction principles generated for propositions by
    default. We instead prefer minimal principles. *)

(** **** Exercise (medium) *)

(** Come up with a (metatheoretical) algorithm that can derive a minimal
    principle from a maximal one. Start by comparing maximal and minimal
    principles for some types other than [prod] and [sum]. Make sure it
    also works for indexed families.

    Do you now understand why the induction principle for [le] looks the
    way it does? *)

(** * Mutual induction *)

(** There's one more kind of induction we haven't covered yet: mutual
    induction. It is a very straightforward generalization of ordinary
    induction.

    When we define and inductive type (or an inductive family), we can
    make references to everything we have defined before and also to the
    thing we are currently defining. But we are defining only one thing
    at time. Recall the definition of [even]: *)

Print even.
(* ===> Inductive even : nat -> Prop :=
            | even0 : even 0
            | evenSS : forall n : nat, even n -> even (S (S n)) *)

(** We have a predicate for even numbers, but what about odd numbers? *)

Inductive odd : nat -> Prop :=
    | odd1 : odd 1
    | oddSS : forall n : nat, odd n -> odd (S (S n)).

(** Looks fine. These definitions say that an even number is either zero
    or [2 + n], where [n] is even and that an odd number is either one or
    [2 + n], where [n] is odd.

    In English we can give a different, but equivalent definition of both
    even and odd numbers at once:
    - 0 is even
    - if n is even, then n + 1 is odd
    - if n is odd, then n + 1 is even *)

(** In the above paragraph, we defined evenness and oddness not separately,
    but together. This kind of definition is not specific to English (or any
    other natural language for that matter) — it is also possible to use it
    in Coq and it's called mutual induction. *)

Inductive even' : nat -> Prop :=
    | even'_0 : even' 0
    | even'_S : forall n : nat, odd' n -> even' (S n)

with odd' : nat -> Prop :=
    | odd'_S : forall n : nat, even' n -> odd' (S n).

(** In definitions by mutual induction the first definition is introduced
    by the keyword [Inductive] and each subsequent one by the keyword [with].
    The dot we have to put only after the last definition finishes. It's
    just like the ordinary [Inductive] definitions, but in the constructors
    of a type [T] we can reference all the other types that we are defining
    simultaneously.

    The inductive definition of [even'] and [odd'] mimics what we have seen
    above (we just have to call our predicates [even'] and [odd'] because
    the names [even] and [odd] are already taken).

    Let's see how good this definition is when compared to the previous
    non-inductive definitions. *)

Theorem even_2n :
  forall n : nat, even n -> exists k : nat, n = 2 * k.
(* begin hide *)
Proof.
  induction 1.
    exists 0. trivial.
    destruct IHeven as [k IH]. exists (S k). cbn. omega.
Qed.
(* end hide *)

Theorem odd_2n_1 :
  forall n : nat, odd n -> exists k : nat, n = 2 * k + 1.
(* begin hide *)
Proof.
  induction 1.
    exists 0. trivial.
    destruct IHodd as [k IH]. exists (S k). omega.
Qed.
(* end hide *)

(** The ordinary ones are easy. *)

Theorem even'_2n :
  forall n : nat, even' n -> exists k : nat, n = 2 * k.
Proof.
  induction 1.
    exists 0. trivial.
    induction H.
      trivial.
Abort.

(** This proof attempt fails because we lack the necessary inductive
    hypothesis saying something alone the lines of
    [forall n : nat, odd' n -> exists k : nat, n = 2 * k + 1]. Let's
    try to prove this as a theorem. *)

Theorem odd'_2n_1 :
  forall n : nat, odd' n -> exists k : nat, n = 2 * k + 1.
Proof.
  induction 1.
    exists 0. trivial.
    induction H.
      trivial.
Abort.

(** We have the same problem here. An induction hypothesis is missing that
    would look just like the theorem [even'_2n] we wanted to prove above.
    So, if the induction doesn't work as well as we would like it to, let's
    check the induction principles of [even'] and [odd']. *)

Check even'_ind.
(* ===> even'_ind :
        forall P : nat -> Prop,
          P 0 ->
          (forall n : nat, odd' n -> P (S n)) ->
            forall n : nat, even' n -> P n *)

(** A careful glance reveals that there's no induction in this induction
    principle! If you check [odd'_ind], you will see the same thing: no
    induction there.

    This doesn't have any deep philosophical reasons. It's just that for
    some mystical reason Coq by default decides to generate nonmutual
    induction principles even for mutually inductive types. We can easily
    fix it. *)

Scheme even'_odd'_ind := Induction for even' Sort Prop
with odd'_even'_ind := Induction for odd' Sort Prop.

Check even'_odd'_ind.
(* ===> even'_odd'_ind :
        forall
        (P : forall n : nat, even' n -> Prop)
        (P0 : forall n : nat, odd' n -> Prop),
          P 0 even'_0 ->
          (forall (n : nat) (o : odd' n),
            P0 n o -> P (S n) (even'_S n o)) ->
          (forall (n : nat) (e : even' n),
            P n e -> P0 (S n) (odd'_S n e)) ->
              forall (n : nat) (e : even' n), P n e *)

(** This is exactly what we need. First, we have two predicates, [P] and [P0].
    [P] is the one we will be proving. It will be automatically inferred by
    Coq. [P0] is the induction hypothesis that was missing in our last attempt
    There are three cases in the principle. This is because our definition had
    three constructors: two for [even'] and one for [odd'].

    Notice that this principle is maximal. There's also the other principle
    — [odd'_even'_ind]. It's there because when we define stuff by mutual
    induction, we have to mutually generate the induction principles too.

    Let's see how to use this principle. *)

Theorem even'_2n :
  forall n : nat, even' n -> exists k : nat, n = 2 * k.
Proof.
  induction 1 using even'_odd'_ind
  with (P0 := fun (n : nat) (H : odd' n) => exists k : nat, n = 2 * k + 1).
    exists 0. trivial.
    destruct IHeven' as [k IH]. exists (S k). omega.
    destruct IHeven' as [k IH]. exists k. omega.
Qed.

(** It was much easier this time. To prove the theorem we use [induction 1]
    as before, but this time we add the clause [using even'_odd'_ind] which
    tells Coq which induction principle to use. Then we use the [with]
    clause to tell Coq how [P0] should look like. We don't have to tell it
    about [P] because it can infer it from the goal.

    Note that the [with] keyword here has nothing to do with the [with] we
    used in the inductive definition. It's just a coincidence of names. We
    have three cases that we solve easily. This shape of induction was what
    we expected at the very beginnig. *)

Theorem odd'_2n_1 :
  forall n : nat, odd' n -> exists k : nat, n = 2 * k + 1.
(* begin hide *)
Proof.
  induction 1 using odd'_even'_ind
  with (P := fun (n : nat) (H : even' n) => exists k : nat, n = 2 * k).
    exists 0. trivial.
    destruct IHodd' as [k IH]. exists (S k). omega.
    destruct IHodd' as [k IH]. exists k. omega.
Qed.
(* end hide *)

(** The second proof is quite similar. But how does the two proofs compare?
    The ones for [even] and [odd] were 14 lines long in total (at least for
    me) and weren't too hard. Quite the opposite. The ones for [even'] and
    [odd'] were 18 lines long in total and we're harder to carry out: we
    had to manually specify the predicates Coq couldn't infer from context.

    So, is mutual induction useless? Not really. *)

Theorem even'_2n' :
  forall n : nat, even' n -> exists k : nat, n = 2 * k
with odd'_2n_1' :
  forall n : nat, odd' n -> exists k : nat, n = 2 * k + 1.
Proof.
  destruct 1.
    exists 0. trivial.
    destruct (odd'_2n_1' _ H) as [k IH]. exists (S k). omega.
  destruct 1.
    destruct (even'_2n' _ H) as [k IH]. exists k. omega.
Qed.

(** The above alternative proof is only 11 lines long, which is better
    than the proofs for [even] and [odd] (but don't take it too seriously
    — proof length measured in lines of code need not be a good measure of
    easiness).

    These theorems are similar to the previous ones, but this time we stated
    and proved both of them at once. We also didn't need to use [induction] 
    (and thus write any predicates explicitly in any place other than the
    theorem statement). This is because using the command [Theorem] in the
    above way adds the inductive hypotheses we need to our context.

    We then proceed as above, but with [destruct] inside of induction.
    We also have to write a bit more in order to destruct our inductive
    hypotheses, but that's not a problem.

    So, is mutual induction useful, if it can give us shorter proofs? I don't
    know a good answer to this question. I can only tell you that I haven't
    seen it used too often. *)

(** * Custom induction principles *)

(** We saw in the previous sections how induction principles look like and
    that Coq generates us one (or rather, three) for every inductive
    definition we make. We also saw that these principles can be derived
    by hand.

    Another fact is that these principles are not unique — quite the
    opposite. Usually there can be many different principles for each
    type: for dependent and non-dependent functions, for true induction
    or just for case analysis, they can even differ by their order of
    taking arguments.

    But even more is possible. Induction principles don't need, in general,
    to be associated with any particular type. We can thus have principles
    for proving facts about relations of type [P : nat -> list bool -> Prop]
    or proving properties of the function [plus].

    We will call the principles Coq generates us "standard" and the ones we
    write ourselves "non-standard" or "custom". In this subchapter we will
    learn to devise and implement non-standard principles and to use them
    with standard tactics like [destruct] and [induction].

    We will also learn about the basics of functional induction, a powerful
    tool for proving properties of recursive functions. *)

Definition bool_ind'
  (P : bool -> Prop) (f : P false) (t : P true) (b : bool) : P b :=
match b with
    | true => t
    | false => f
end.

(** This is a nonstandard case analysis principle for [bool]. The only thing
    that makes it different from the principle [bool_ind] is the order of
    arguments: it takes  that of type [P false] first, whereas [bool_ind]'s
    first argument has type [P true]. It is obvious that it is correct,
    because we can prove [P] for [true] and [false] in any order we like. *)

Definition bool_ind'' :
  forall P : bool -> Prop,
    P false -> P true ->
      forall b : bool, P b.
Proof.
  destruct b; assumption.
Qed.

(** We can also use the tactic language to simply prove the principle as a
    theorem. This doesn't make much difference now, but for more complex
    principles it is often easier to establish them that way.

    But how do we use such nonstndard principles? Standard case analysis on
    the term [t] is usually performed by using the tactic [destruct t]. Our
    nonstandard one can be likewise performed with the tactic [destrct t
    using our_principle]. Of course it can also be used directly with [apply],
    but we already saw that it isn't the best possibility.

    Let's see both principles in action. *)

Theorem negb_involutive'' :
  forall b : bool, negb (negb b) = b.
Proof.
  destruct b; cbn. all: trivial.
Restart.
  destruct b using bool_ind; cbn. all: trivial.
Restart.
  destruct b using bool_ind'; cbn. all: trivial.
Restart.
  destruct b using bool_ind''; cbn. all: trivial.
Qed.

(** Here we see that the tactic [destruct b] is in fact equivalent to
    [destruct b using bool_ind], in which the standard induction principle
    is named explicitly. In these two equivalent cases, our first subgoal
    is [true = true] and the second is [false = false]. On the contrary,
    when we use one of our custom principles, our first goal is of the form
    [false = false] and the second is [true = true].

    Let's see a custom principle for [nat]. *)

Fixpoint nat_ind_2
  (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
  (HSS : forall n : nat, P n -> P (S (S n)))
  (n : nat) : P n :=
match n with
    | 0 => H0
    | 1 => H1
    | S (S n') => HSS n' (nat_ind_2 P H0 H1 HSS n')
end.

Fixpoint nat_ind_2'
  (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
  (HSS : forall n : nat, P n -> P (S (S n)))
  (n : nat) : P n.
Proof.
  destruct n as [| [| n']].
    apply H0.
    apply H1.
    apply HSS. apply nat_ind_2'; assumption.
Defined.

(** In case of [nat], we can customize our induction principle more than
    by just changing the order of the arguments. For example, we can do
    "induction by 2's". This means that rather than starting at [0] and
    applying [S] once in each step, we have two base cases, [0] and [1],
    and we apply [S] twice in each step.

    This principle is correct because we can generate all natural numbers
    this way: starting from [0] and applying [S] twice in each step we
    can generate all even numbers, whereas starting from [1] and applying
    [S] twice in each step we can generate all odd numbers. Because each
    natural number is either even or odd, we see that our custom principle
    covers all cases.

    We also see that when our principles have recursion, defining them with
    tactics is easier than without tactics. *)

Require Import Div2.

(** Div2 is a module that contains the function [div2], which performs
    integer division by two. Here is its definition: *)

Eval compute in div2.
(* ===> = fix div2 (n : nat) : nat :=
          match n with
              | 0 => 0
              | 1 => 0
              | S (S n') => S (div2 n')
          end
          : nat -> nat *)

(** Note: we use [Eval compute] instead of [Print] because [div2] is only
    a notation.

    We see that [div2] is defined differently than [plus] or [mult]. These
    two have just two cases in their respective [match]es: [0] and [S n'],
    whereas [div2] has [0], [1] and [S (S n')]. Let's try proving some
    theorem.  *)

Theorem lt_div2' :
  forall n : nat, 0 < n -> div2 n < n.
Proof.
  induction n as [| n']; cbn; intros; auto.
    destruct n'; cbn in *; auto.
Restart.
  induction n as [| | n'] using nat_ind_2; cbn; intros; auto.
    destruct n' as [| [| n'']]; cbn in *; auto.
      unfold lt in *. apply le_n_S. apply le_S. apply IHn'. apply le_n_S.
        apply le_0_n.
Qed.

(** Trying induction on [n] using the standard induction principle doesn't
    help us much. A kind of a "mismatch" occurs: when we have [n'] in the
    hypothesis, we have [match n' with ...] in the goal and vice versa. This
    is because the shape of induction in the standard principle is different
    from the shape of recursion that was used to define [div2]. If we use
    the custom principle, we get rid of that problem and we are able to prove
    the goal easily.

    So, our nonstandard principles are no different from the standard ones,
    we just have to create them manually and type a bit more in order to
    use them... or do we? *)

Require Import List.
Import ListNotations.

Fixpoint swap_blocks {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [x] => [x]
    | x :: y :: t => y :: x :: swap_blocks t
end.

Compute swap_blocks [1; 2; 3; 4; 5].
(* ===> = [[2; 1; 4; 3; 5]] : list nat *)

(** Note: [Compute] is equivalent to [Eval compute in], but shorter.

    This is a function that swaps places of adjacent elements in a list.
    It is easy to see that it is an involution, which means that applying
    it twice gives us the original list. Let's try to prove that. *)

Theorem swap_blocks_involutive :
  forall (A : Type) (l : list A),
    swap_blocks (swap_blocks l) = l.
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct t; cbn in *.
      trivial.
Abort.

(** We see that we have the same problem we had with [div2]. If we have [t]
    in the induction hypothesis, then it's going to appear inside a [match]
    in the goal. We could prove this theorem by writing a custom induction
    principle for lists, but what if we are too lazy to do that?

    Don't worry, there's a solution called [functional induction]. It is a
    tactic which performs induction that fits the recursive structure of our
    function perfectly. We can use it like this: *)

Functional Scheme swap_blocks_ind :=
  Induction for swap_blocks Sort Prop.

Check swap_blocks_ind.
(* ===> swap_blocks_ind :
        forall (A : Type) (P : list A -> list A -> Prop),
          (forall l : list A, l = [] -> P [[]] [[]]) ->
          (forall (l : list A) (x : A) (l0 : list A),
            l = x :: l0 -> l0 = [] -> P [[x]] [[x]]) ->
          (forall (l : list A) (x : A) (l0 : list A),
            l = x :: l0 -> forall (y : A) (t : list A),
            l0 = y :: t -> P t (swap_blocks t) ->
              P (x :: y :: t) (y :: x :: swap_blocks t)) ->
          forall l : list A, P l (swap_blocks l) *)

(** The command [Functional Scheme] generates an induction principle that
    fits the shape of our function's recursion. The principle may look
    intimidating, but if you take a closer look, it just repeats the cases
    found in the [match] in [swap_blocks]' definition. We can use it like
    this (but first we have to import the [Recdef] module): *)

Require Import Recdef.

Theorem swap_blocks_involutive :
  forall (A : Type) (l : list A),
    swap_blocks (swap_blocks l) = l.
Proof.
  intros. functional induction @swap_blocks A l; cbn.
    trivial.
    trivial.
    rewrite IHl0. trivial.
Qed.

(** A piece of cake, wasn't it? But we can be even more lazy: *)

Function swap_blocks' {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [x] => [x]
    | x :: y :: t => y :: x :: swap_blocks' t
end.

Theorem swap_blocks'_involutive :
  forall (A : Type) (l : list A),
    swap_blocks' (swap_blocks' l) = l.
Proof.
  intros. functional induction @swap_blocks' A l; cbn.
    trivial.
    trivial.
    rewrite IHl0. trivial.
Qed.

(** We can replace the command [Fixpoint] with [Function] to make Coq
    generate us the same principle that the [Functional Scheme] command
    (and many other things, too). *)

(** **** Exercise (easy) *)

(** Prove the following nonstandard induction principles for lists. What
    do they mean? Give an informal description. *)

Theorem list_ind_rev :
  forall (A : Type) (P : list A -> Prop) (Hnil : P [])
  (Hsnoc : forall (x : A) (l : list A), P l -> P (l ++ [x]))
    (l : list A), P l.
(* begin hide *)
Proof.
  intros. cut (forall l : list A, P (rev l)); intros.
    rewrite <- rev_involutive. apply H.
    induction l0 as [| h t]; cbn.
      apply Hnil.
      apply Hsnoc. assumption.
Qed.
(* end hide *)

Theorem list_ind_app :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (IH : forall l l' : list A, P l -> P l' -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    assumption.
    apply (IH [h] t); auto.
Qed.
(* end hide *)

(** **** Exercise (easy) *)

Function take {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

(** [take n l] takes at most [n] initial elements from the list [l].
    Prove some of its properties using standard induction principles
    and then reprove them using functional induction. Which method is
    easier?

    If you are not lazy, write a custom induction principle that would
    fit [take]'s recursion structure. Which method requires least work
    to get things done? *)

Theorem take_length' :
  forall (A : Type) (n : nat) (l : list A),
    length l <= n -> take n l = l.
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    simpl. destruct l; inversion H; trivial.
    destruct l as [| h t]; simpl.
      trivial.
      rewrite IHn'.
        trivial.
        simpl in H. apply le_S_n in H. assumption.
Restart.
  intros. functional induction (@take A n l); cbn.
    destruct _x; inversion H. trivial.
    trivial.
    rewrite IHl0.
      trivial.
      cbn in H. apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem length_take :
  forall (A : Type) (n : nat) (l : list A),
    n <= length l -> length (take n l) = n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t];
  simpl; inversion 1; subst; trivial;
  f_equal; apply IHn'; apply le_S_n in H; assumption.
Restart.
  intros. functional induction @take A n l; cbn in *;
  try rewrite IHl0; trivial.
    inversion H. trivial.
    apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem length_take' :
  forall (A : Type) (n : nat) (l : list A),
    length (take n l) <= n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    trivial.
    destruct l as [| h t]; cbn.
      apply le_0_n.
      apply le_n_S. apply IHn'.
Restart.
  intros. functional induction @take A n l; cbn.
    trivial.
    apply le_0_n.
    apply le_n_S. assumption.
Qed.
(* end hide *)

(* begin hide *)
(** As for the second part of the exercise, I'm too lazy to even try.
    It is thus proven that [functional induction] is the best. *)
(* end hide *)

(** * Case analysis on non-inductive types *)

(** Two subchapters ago we have said the we can prove that all elements of
    a finite type have some property by using case analysis, but actually
    we only did this for an inductive type.

    In this subchapter, we will see that we can do case analysis on a finite
    type even when it is not defined inductively (we won't define "finite"
    formally here). But before we do that, we have to discuss the equality
    of functions. *)

Theorem S_plus_1_l_eq :
  S = fun n : nat => 1 + n.
Proof.
  cbn. reflexivity.
Qed.

(** By default, [x = y] holds only when [x] and [y] are convertible, meaning
    both reduce to the same thing when computed. This is a very weak notion
    of equality that is often not satisfying. *)

Theorem S_plus_1_r_eq :
  S = fun n : nat => n + 1.
Proof.
  cbn. Fail reflexivity.
Abort.

Theorem S_plus_1_r_ext_eq :
  forall n : nat, S n = n + 1.
Proof.
  intros. rewrite <- plus_n_Sm, <- plus_n_O. trivial.
Qed.

(** When trying to prove that [S] equals [fun n : nat => n + 1], Coq tells
    us it is 'Unable to unify "n + 1" with "S n"'. These terms are not
    not convertible terms and thus the two functions can't be proven equal.
    This is very disappointing because we can easily show that they compute
    they very same thing.

    Here comes our saviour: the Axiom of Functional Extensionality. *)

Require Import FunctionalExtensionality.

Check @functional_extensionality.
(* ===> @functional_extensionality :
        forall (A B : Type) (f g : A -> B),
          (forall x : A, f x = g x) -> f = g *)

(** This axiom asserts that if two functions compute the same value for
    each argument, then they are equal. This axiom has been proven
    consistent with Coq's logic, so we can use it safely. Note: there
    also is a version of this axiom for dependent functions. *)

Theorem S_plus_1_r_eq :
  S = fun n : nat => n + 1.
Proof.
  extensionality n. apply S_plus_1_r_ext_eq.
Qed.

(** If we need to prove two functions equal, we can use the [extensionality]
    tactic, which applies the axiom for us. We are then left to prove that
    both functions compute the same thing.

    One last thing we need is to define the constant function: *)

Definition const {A B : Type} (b : B) (_ : A) : B := b.

(** Armed with the axiom and this definition, we can proceed to the clou
    of this subchapter: we will establish a case analysis principle for
    boolean functions.

    How many ways are there to assign two values to two arguments? *)

Lemma bool_fun_char :
  forall f : bool -> bool,
    f = @id bool \/ f = negb \/ f = const true \/ f = const false.
Proof.
  intros. case_eq (f true); case_eq (f false); intros.
    right; right; left. extensionality x. destruct x; auto.
    left. extensionality x. destruct x; auto.
    right; left. extensionality x. destruct x; auto.
    do 3 right. extensionality x. destruct x; auto.
Qed.

(** Well, you guessed it right — there are only four: identity, negation
    and two constant ones. We can prove this easily by looking at the
    values of [f true] and [f false]. *)

Theorem bool_fun_ind :
  forall P : (bool -> bool) -> Prop,
    P (@id bool) -> P negb -> P (const true) -> P (const false) ->
      forall f : bool -> bool, P f.
Proof.
  intros. destruct (bool_fun_char f) as [H' | [H' | [H' | H']]];
  subst; assumption.
Qed.

(** The last thing left is to pack the above lemma into a case analysis
    principle. We will call it [bool_fun_ind], even though it has nothing
    to do with induction.

    This is it! We can now do case analysis when proving properties of
    boolean functions. But there's a problem: I can't think of any useful
    property of boolean functions that can be proved by case analysis but
    not with some other method. *)

(** **** Exercise (medium) *)

(** Try to come up with such a property. *)

(** * Functions and functional relations *)

(** After you have learned about the commands [Function] and [Functional
    Scheme], you may be left wondering, how they work. We will try to
    answer this question now, but it will be easier if we first see how
    we can use inductive families to represent functions.

    First we have to explicitly spell out what a function is. There are two
    widely used definitions:
    - the computer scientist's one, which equates functions with algorithms.
      They are always computable, which means we can implement and run them
      on a computer to get the result. Coq functions are of this kind.
    - the mathematician's one, which equates functions with functional
      relations, which are relations with additional properties. These need
      not be computable. *)

(** The second meaning of "function" stems from set theory and is widely
    used in mathematics. Here a function is synonyomous with its graph.
    A graph of a function is a relation that relates the function's inputs
    to its output.

    Let's see an example underlining the difference between these two. *)

Function div2 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => S (div2 n')
end.

(** Note: we use [Function] only to get the functional induction principle
    so that we will later be able to compare it to our own.

    [div2] is an ordinary structurally recursive function. Nothing fancy. *)

Inductive div2_rel : nat -> nat -> Prop :=
    | div2_rel_even : forall n : nat, div2_rel (2 * n) n
    | div2_rel_odd : forall n : nat, div2_rel (2 * n + 1) n.

(** [div2_rel] is an inductive relation defined like this:
    - the result of dividing [2 * n] by [2] is [n]
    - the result of dividing [2 * n + 1] by [2] is [n] *)

(** The difference is quite stark: the recursive one ([div2]) tells us how
    to divide a number by two (how to compute the result). The inductive one
    ([div2_rel]) tells us what is the relation between inputs and outputs of
    a function that divide its argument by two. Nonetheless these two
    formulations of division are somehow equivalent. *)

Lemma div2_rel_SS :
  forall n m : nat, div2_rel n m -> div2_rel (S (S n)) (S m).
(* begin hide *)
Proof.
  induction 1.
    replace (S (S (2 * n))) with (2 * (S n)).
      constructor.
      omega.
    replace (div2_rel _ _) with (div2_rel (2 * (S n) + 1) (S n)).
      constructor.
      cbn. f_equal. omega.
Qed.
(* end hide *)

(** This is just a lemma for the proper proof. *)

Theorem div2_rel_correct :
  forall n m : nat, div2 n = m -> div2_rel n m.
(* begin hide *)
Proof.
  induction n using nat_ind_2; cbn; intros; subst.
    change 0 with (2 * 0) at 1. constructor.
    change 1 with (2 * 0 + 1) at 1. constructor.
    apply div2_rel_SS. apply IHn. trivial.
Qed.
(* end hide *)

(** This theorem states that [div2_rel] contains the graph of [div2]. *)

Theorem div2_rel_complete :
  forall n m : nat, div2_rel n m -> div2 n = m.
(* begin hide *)
Proof.
  induction 1.
    induction n using nat_ind_2; trivial.
      cbn in *. rewrite plus_comm. cbn. do 2 f_equal.
        rewrite <- IHn at 3. f_equal. omega.
    rewrite plus_comm. induction n using nat_ind_2; cbn in *; trivial.
      rewrite <- plus_n_O in *. rewrite plus_comm. cbn in *. rewrite IHn.
      trivial.
Qed.
(* end hide *)

(** And this one says that the graph of [div2] contains [div2_rel]. Thus
    [div2_rel] really is the graph of [div2]. [div2_rel] may also be
    thought of as a specification for [div2], but specifying functions
    isn't everything we can achieve using inductive relations. Another
    thing is specifying partial functions. *)

Module Zfact.

Require Import ZArith.

Open Scope Z.

Inductive Zfact : Z -> Z -> Prop :=
    | Zfact_0 : Zfact 0 1
    | Zfact_S : forall (k r : Z),
        Zfact k r -> Zfact (k + 1) ((k + 1) * r).

(** This looks like a specification for the factorial function. *)

Theorem Zfact_nonneg :
  forall n : nat, Zfact (Z.of_nat n) (Z.of_nat (fact n)).
(* begin hide *)
Proof.
  induction n as [| n'].
    cbn. constructor.
    change (fact (S n')) with (S n' * fact n')%nat.
      rewrite Nat2Z.inj_mul, Nat2Z.inj_succ. constructor. apply IHn'.
Qed.
(* end hide *)

(** And indeed, for nonnegative integers it is exactly the factorial
    function. But what about the negative ones? *)

Theorem Zfact_neg :
  forall n k : Z, n < 0 -> ~ Zfact n k.
(* begin hide *)
Proof.
  induction 2.
    inversion H.
    apply IHZfact. omega.
Qed.
(* end hide *)

(** It turns out that if [n < 0], then it isn't related to any result at
    all and therefore this relation can't be a graph of any function that
    is definable in Coq. We may call this the "programming newbie's
    factorial".

    This example clearly shows that definitions by recursion and induction
    differ. The latter can describe more things than the former (another
    example would be nonterminating functions — something that's not there
    in Coq, but is very frequent in other programming languages), but this
    comes at the cost of computability — we can't compute with [Zfact]. *)

End Zfact.

(** **** Exercise (easy) *)

(** Consider the following function on natural numbers:
    - f(0) = 1
    - f(1) = 1
    - f(n) = f(n/2) if n is even
    - f(n) = f(3n + 1) if n is odd *)

(** Is this function definable in Coq? Implement it using recursion or
    induction, whichever is easier. Then show that f(42) = 1. Can you
    prove that f(n) = 1 for all n? *)

(* begin hide *)
Inductive collatz : nat -> nat -> Prop :=
    | collatz_0 : collatz 0 1
    | collatz_1 : collatz 1 1
    | collatz_even : forall n r : nat,
        even n -> collatz (div2 n) r -> collatz n r
    | collatz_odd : forall n r : nat,
        odd n -> collatz (3 * n + 1) r -> collatz n r.

Hint Constructors collatz.

Theorem collatz_42 : collatz 42 1.
Proof.
  apply collatz_even; cbn.
    repeat constructor.
  apply collatz_odd; cbn.
    repeat constructor.
  apply collatz_even; cbn.
    repeat constructor.
  apply collatz_even; cbn.
    repeat constructor.
  apply collatz_even; cbn.
    repeat constructor.
  apply collatz_even; cbn.
    repeat constructor.
  apply collatz_even; cbn.
    repeat constructor.
  apply collatz_even; cbn.
    repeat constructor.
  apply collatz_1.
Qed.
(* end hide *)

(** Now that we know inductive relations can represent graphs of functions,
    we can ask ourselves: what's the point of it? And what does it have to
    do with functional induction? Well, it turns out that quite a lot...

    Consider this alternative definition of [div2]'s graph. *)

Inductive R_div2' : nat -> nat -> Prop :=
    | R_div2'_0 : R_div2' 0 0
    | R_div2'_1 : R_div2' 1 0
    | R_div2'_2 :
        forall n r : nat,
          R_div2' n r -> R_div2' (S (S n)) (S r).

(** Note: in the names of the following functions we utilize the naming
    conventions of [Function] and [Functional Scheme], but add a ['] at
    the end.

    No doubt this is the graph of [div2], because this definition follows
    precisely [div2]'s definition: there's one constructor for each case
    in its pattern match. Therefore, unlike the original [div2_rel], it is
    not well suited for a specification of [div2].

    So, what's the point? *)

Check R_div2'_ind.
(* ===> R_div2'_ind :
        forall P : nat -> nat -> Prop,
          P 0 0 ->
          P 1 0 ->
          (forall n r : nat, R_div2' n r ->
            P n r -> P (S (S n)) (S r)) ->
              forall n n0 : nat, R_div2' n n0 -> P n n0 *)

Check div2_ind.
(* ===> div2_ind :
        forall P : nat -> nat -> Prop,
          (forall n : nat, n = 0 -> P 0 0) ->
          (forall n n0 : nat, n = S n0 -> n0 = 0 -> P 1 0) ->
          (forall n n0 : nat,
            n = S n0 -> forall n' : nat, n0 = S n' ->
              P n' (Init.Nat.div2 n') ->
              P (S (S n')) (S (Init.Nat.div2 n'))) ->
               forall n : nat, P n (Init.Nat.div2 n) *)

(** The point is that [R_div2'_ind], the induction principle for the graph
    of [div2] is very much like [div2_ind], the functional induction principle
    for [div2]. This fact is overshadowed by weirdness of [div2_ind] (it was,
    after all, generated automagically). There's something very deep going on
    here.

    Let's ask ourselves a related question: how to prove a property of a given
    function f by induction?

    The simple answer is: we have to apply the right induction principle and
    then finish the proof. But which induction principle is the right one?
    A philosophical answer would be: the one that best matches the function's
    recursion shape. But which one is it?

    Recall that every induction principle tells us how to use a value of some
    inductively defined type (or type family) to define dependent functions.
    Therefore, every induction principle is associated to some type or type
    family. So the question boils down to this: which inductive type has the
    most similar shape to that of f's recursion shape?

    The ultimate answer is: the graph of f (using the definition that follows
    exactly f's recursion's shape). Now that you know this illuminating fact,
    let's see how to derive the functional induction principle for [div2] by
    hand. *)

Print R_div2.
(* ===> Inductive R_div2 : nat -> nat -> Set :=
            | R_div2_0 : forall n : nat,
                n = 0 -> R_div2 0 0
            | R_div2_1 : forall n n0 : nat,
                n = S n0 -> n0 = 0 -> R_div2 1 0
            | R_div2_2 : forall n n0 : nat,
                n = S n0 -> forall n' : nat,
                n0 = S n' -> forall _res : nat,
                R_div2 n' _res -> R_div2 (S (S n')) (S _res) *)

(** The first thing the commands [Function] and [Functional Scheme] do is
    define the graph of the function in question. [R_div2] is the graph
    of [div2] as generated by [Functional Scheme]. It's a bit clumsier than
    our definition (note that, for example, the quantified variable [n : nat]
    in the constructor [R_div2_0] is not used), but also more general (note
    that its sort is [Set]). *)

Theorem R_div2'_correct :
  forall n m : nat, div2 n = m -> R_div2' n m.
Proof.
  induction n as [| | n'] using nat_ind_2; cbn; intros; subst;
  constructor; auto.
Qed.

Theorem R_div2'_complete :
  forall n m : nat, R_div2' n m -> div2 n = m.
Proof.
  induction 1; cbn; auto.
Qed.

(** Then we prove that [R_div2'] really is a graph of [div2]. *)

Check R_div2_correct.
(* ===> R_div2_correct :
        forall n _res : nat, _res = div2 n -> R_div2 n _res *)

Check R_div2_complete.
(* ===> R_div2_complete :
        forall n _res : nat, R_div2 n _res -> _res = div2 n *)

(** [Functional Scheme] doesn't do it, but [Function] does. *)

Theorem div2_ind' :
  forall P : nat -> nat -> Prop,
    P 0 0 ->
    P 1 0 ->
    (forall n : nat, P n (div2 n) -> P (S (S n)) (S (div2 n))) ->
      forall n : nat, P n (div2 n).
Proof.
  intros. apply R_div2'_ind.
    assumption.
    assumption.
    intros. apply R_div2'_complete in H2. subst. apply H1. assumption.
    apply R_div2'_correct. trivial.
Qed.

(** We can prove the induction principle for [div2] by using the induction
    principle for [R_div2'] and the fact that [R_div2'] is the graph of
    [div2]. *)

Theorem div2_equation' :
  forall n : nat,
    div2 n = match n with
                 | 0 => 0
                 | 1 => 0
                 | S (S n') => S (div2 n')
             end.
Proof.
  destruct n; reflexivity.
Qed.

(** In general to prove [div2_ind'] we could need [div2_equation'], which is
    called a fixed point equation for [div2]. Here it wasn't needed, because
    it can be obtained by just unfolding [div2], but in general, when defining
    stuff by well-founded recursion, we wouldn't get that equation for free.
    We would have to prove it. *)

Theorem lt_div2'' :
  forall n : nat, 0 < n -> div2 n < n.
Proof.
  intro. apply div2_ind'.
    omega.
    omega.
    intros. destruct n0 as [| [| n']]; cbn in *.
      omega.
      omega.
      apply lt_n_S. apply lt_trans with (S (S n')); omega.
Restart.
  intro. functional induction @div2 n.
    omega.
    omega.
    intros. destruct n' as [| [| n]]; cbn in *.
      omega.
      omega.
      apply lt_n_S. apply lt_trans with (S (S n)); omega.
Qed.

(** Here is an example use of the induction principle we crafted for
    ourselves. Applying it works exactly like using the tactic [functional
    induction]. *)

(** **** Exercise (easy) *)

Fixpoint div2l {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [_] => []
    | h :: _ :: t => h :: div2l t
end.

(** Here's a function [div2l], that divides a list by 2 (whatever that means).
    Define its graph by induction, prove it really is its graph. Derive the
    fixed point equation and functional induction principle for [div2l] by
    hand. Then prove the theorem. *)

(* begin hide *)
Inductive R_div2l' {A : Type} : list A -> list A -> Prop :=
    | R_div2l'_0 : R_div2l' [] []
    | R_div2l'_1 : forall x : A, R_div2l' [x] []
    | R_div2l'_2 : forall (x y : A) (l r : list A),
        R_div2l' l r -> R_div2l' (x :: y :: l) (x :: r).

Inductive R_div2l'' {A : Type} : list A -> list A -> Prop :=
    | R_div2l''_0 : R_div2l'' [] []
    | R_div2l''_1 : forall x : A, R_div2l'' [x] []
    | R_div2l''_2 : forall (x y : A) (l : list A),
        R_div2l'' l (div2l l) -> R_div2l'' (x :: y :: l) (x :: div2l l).

Fixpoint R_div2l'_correct
  (A : Type) (l l' : list A) : div2l l = l' -> R_div2l' l l'.
Proof.
  destruct l as [| x [| y t]]; cbn; intros; subst; constructor.
    apply R_div2l'_correct. trivial.
Qed.

Theorem R_div2l'_complete :
  forall (A : Type) (l l' : list A),
    R_div2l' l l' -> div2l l = l'.
Proof.
  induction 1; cbn; subst; trivial.
Qed.

Fixpoint div2l_ind'
  (A : Type)
  (P : list A -> list A -> Prop)
  (H0 : P [] [])
  (H1 : forall x : A, P [x] [])
  (H2 : forall (x y : A) (l : list A),
    P l (div2l l) -> P (x :: y :: l) (x :: div2l l))
      (l : list A) : P l (div2l l).
Proof.
  destruct l as [| x [| y l]]; cbn.
    apply H0.
    apply H1.
    apply H2. apply div2l_ind'; auto.
Qed.

Theorem div2l_equation' :
  forall (A : Type) (l : list A),
    div2l l = match l with
                | [] => []
                | [x] => []
                | x :: y :: t => x :: div2l t
             end.
Proof.
  destruct l as [| x [| y t]]; cbn; trivial.
Qed.
(* end hide *)

Theorem div2l_length :
  forall (A : Type) (l : list A),
    l <> [] -> length (div2l l) < length l.
(* begin hide *)
Proof.
  intros A l. apply div2l_ind'; cbn; intros; auto.
    contradiction.
    destruct l0 as [| h1 [| h2 t]]; cbn in *; auto.
      apply lt_n_S. apply lt_trans with (S (S (length t))); auto.
        apply H. inversion 1.
Qed.
(* end hide *)

(** * Generalizing the induction hypothesis *)

(** Proof by induction is not always straightforward. An often encountered
    obstacle is the induction hypothesis' lack of generality. This lack of
    generality can actually arise in two independent ways:
    - bad use of tactics
    - too weak theorem statement *)

(** This subchapter will be about dealing with them. Let's start with
    the first possibility. *)

Fixpoint plus' (n m : nat) : nat :=
match m with
    | 0 => n
    | S m' => plus' (S n) m'
end.

(** This is a tail recursive version of [+]. Let's try to prove something
    about it. *)

Theorem plus'_S :
  forall n m : nat, plus' (S n) m = S (plus' n m).
Proof.
  induction m as [| m']; cbn; intros.
    trivial.
    rewrite IHm'.
Abort.

(** We failed, but what happened? We tried to prove the theorem by induction
    on [m], because it is the main argument of [plus']. The base case was
    trivial, but we got stuck in the inductive step case. We can in no way
    help ourselves by applying or rewriting the induction hypothesis.

    This is because [n] is fixed in the induction hypothesis and it is so
    because when we did [induction m], all the things being quantified over
    before [m] got introduced into the context. We can solve this problem
    easily by using the tactic [generalize dependent]. *)

Theorem plus'_S :
  forall n m : nat, plus' (S n) m = S (plus' n m).
Proof.
  intros. generalize dependent n. generalize dependent m.
  induction m as [| m']; cbn; intros.
    trivial.
    specialize (IHm' (S n)). assumption.
Qed.

(** The first line of the proof script has the effect of swapping [n] and
    [m] in the theorem statement. Because of this, when we do [induction m],
    the induction hypothesis quantifies over [n], so we can instantiate it
    with [S n] and finish the proof. Last time we weren't able to do that,
    because [n] was fixed. *)

Theorem plus'_S_v2 :
  forall m n : nat, plus' (S n) m = S (plus' n m).
Proof.
  induction m as [| m']; cbn; auto.
Qed.

(** A different way of solving the same problem is to simply change the
    theorem statement. It is easier and quicker than trying to achieve
    the same effect through [intros] and [generalize dependent], but I
    don't consider it to be a good one. I recommend that the order of
    quantification over the arguments follow the order of the arguments
    in the function's definition. *)

(** **** Exercise (easy) *)

(** Prove [plus'_assoc_1] without generalizing the induction hypothesis.
    Prove [plus'_assoc_2] by generalizing the induction hypothesis.
    Prove [plus'_assoc_3], which quantifies over [c] first.

    Which proof was the easiest one? *)

Theorem plus'_assoc_1 :
  forall a b c : nat, plus' a (plus' b c) = plus' (plus' a b) c.
(* begin hide *)
Proof.
  induction c as [| c']; cbn.
    trivial.
    rewrite plus'_S. cbn. rewrite !plus'_S, IHc'. trivial.
Qed.
(* end hide *)

Theorem plus'_assoc_2 :
  forall a b c : nat, plus' a (plus' b c) = plus' (plus' a b) c.
(* begin hide *)
Proof.
  intros a b c. generalize dependent a. generalize dependent b.
  induction c as [| c']; cbn; intros; trivial.
    rewrite !IHc'. cbn. rewrite plus'_S. trivial.
Qed.
(* end hide *)

Theorem plus'_assoc_3 :
  forall c a b : nat, plus' a (plus' b c) = plus' (plus' a b) c.
(* begin hide *)
Proof.
  induction c as [| c']; cbn; intros.
    trivial.
    rewrite plus'_S. cbn. rewrite !plus'_S, IHc'. trivial.
Qed.
(* end hide *)

(** **** Exercise (hard) *)

(** Write a tactic [gen_ind] that performs induction on its argument after
    having generalized the induction hypothesis. Make sure you can prove
    the theorem [plus'_S_v3] with it. *)

(* begin hide *)
Ltac term_contains t x :=
match t with
    | x => idtac
    | ?f x => idtac
    | ?f _ => term_contains f x
    | _ => fail
end.

Ltac generalize_IH H :=
match reverse goal with
    | H : _ |- _ => fail
    | x : ?Tx |- _ =>
        match type of H with
            | ?TH => term_contains TH x
            | _ => generalize dependent x
        end
end.

Ltac gen_ind H :=
  try intros until H; generalize_IH H; induction H; cbn; auto.
(* end hide *)

Theorem plus'_S_v3 :
  forall n m : nat, plus' (S n) m = S (plus' n m).
Proof.
  gen_ind m.
Qed.

(** The first kind of situation in which our induction hypothesis was
    not general enough arised from careless use of [intros] and [induction].
    It was neither deep nor fundamental and we easily mitigated it by simple
    tactic manipulation.

    The second kind of lack of generality is more fundamental and arises when
    we are trying to prove too weak a theorem. It may appear paradoxical at
    first, but sometimes proving a stronger theorem is easier than proving
    a weaker one. Let's see this in an example. *)

Print rev.
(* ===> rev = fun A : Type =>
        fix rev (l : list A) : list A :=
        match l with
            | [[]] => [[]]
            | x :: l' => rev l' ++ [[x]]
        end
        : forall A : Type, list A -> list A *)

(** Recall that [rev] is a function that reverses its argument. It is very
    inefficient: it's running time is O(n^2). Let's try to improve on that
    by writing a tail recursive version. *)

Fixpoint rev_acc {A : Type} (l acc : list A) : list A :=
match l with
    | [] => acc
    | h :: t => rev_acc t (h :: acc)
end.

(** [rev_acc] works by putting its argument's head to the accumulator until
    its argument is empty, in which case it returns the accumulator. It's
    clear that if we call it with an empty accumulator, then in result we
    will get its argument reversed. Let's try to prove that. *)

Theorem rev_acc_spec_weak :
  forall (A : Type) (l : list A), rev_acc l [] = rev l.
Proof.
  induction l as [| h t]; cbn.
    trivial.
Abort.

(** The proof failed miserably. Our goal mentions [rev_acc t [h]], but
    the induction hypothesis is about [rev_acc t []]. There is no way
    to solve this problem the way we did before: by rearranging the
    order of quantifications or by using [generalize dependent].

    This is a problem of fundamentally different nature — the induction
    hypothesis is too weak because the theorem itself is too weak. To
    go around this, we have to devise a stronger version of the theorem,
    but how to do this?

    Let's take a glance at the arguments of [rev_acc]: the second one is [[]].
    Let's try to generalize the theorem to an arbitrary [acc : list A].
    If we run [rev_acc] with an arbitrary accumulator, it will prepend its
    reversed argument to the accumulator and then return it. Let's try this
    as our theorem. *)

Theorem rev_acc_spec_strong :
  forall (A : Type) (l acc : list A),
    rev_acc l acc = rev l ++ acc.
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. rewrite <- app_assoc. cbn. trivial.
Qed.

(** This time our induction hypothesis talks about a general [acc] and not
    just [[]], so we can easily use it with [rewrite]. Now we can derive the
    weaker version of the theorem we first tried to prove. *)

Theorem rev_acc_spec_weak :
  forall (A : Type) (l : list A), rev_acc l [] = rev l.
Proof.
  intros. rewrite rev_acc_spec_strong. rewrite app_nil_r. trivial.
Qed.

(** The technique presented above allows us to explain the paradoxical fact
    that proving a stronger theorem may be easier than proving a weaker one,
    at least in the case of proofs by induction.

    The explanation is: the stronger the theorem, the stronger the induction
    hypothesis. Sometimes the increase in the induction hypothesis' strength
    will be greater than the increase in the theorem's difficulty and thus
    the proof will be easier. Other times, the stronger theorem will actually
    be harder to prove. *)

(** **** Exercise (easy) *)

(** [app'] is a tail recursive version of [app]. Prove that they are equal. *)

Fixpoint revapp {A : Type} (l1 l2 : list A) : list A :=
match l1 with
    | [] => l2
    | h :: t => revapp t (h :: l2)
end.

Definition app' {A : Type} (l1 l2 : list A) : list A :=
  revapp (revapp l1 []) l2.

(* begin hide *)
Theorem revapp_spec :
  forall (A : Type) (l1 l2 : list A),
    revapp l1 l2 = rev l1 ++ l2.
Proof.
  induction l1 as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. rewrite <- app_assoc. cbn. trivial.
Qed.
(* end hide *)

Theorem app'_spec :
  forall (A : Type) (l1 l2 : list A),
    app' l1 l2 = app l1 l2.
(* begin hide *)
Proof.
  unfold app'. intros.
  rewrite !revapp_spec, app_nil_r, rev_involutive. trivial.
Qed.
(* end hide *)

(** * Technical shortcomings of [induction] *)

(** [induction] is a very smart tactic: it can introduce quantified
    variables into the context, infer the predicate we're trying to
    prove and many more. But there is one situation in which its
    behaviour is really stupid and unexpected.

    Let's see a somewhat complicated example, taken from Coq'Art.
    We will define a simple imperative programming language and
    then try to prove a fact by induction. *)

Section little_semantics.

Axioms Var aExp bExp : Set.

(** Note: there's a reason for using [Axioms] instead of, say, [Variables],
    that will be explained later.

    We will use [Var] to represent variables, [aExp] for arithmetic
    expressions and [bExp] for boolean expressions.*)

Inductive instr : Set :=
    | Skip : instr
    | Assign : Var -> aExp -> instr
    | Seq : instr -> instr -> instr
    | While : bExp -> instr -> instr.

(** There are three kinds of instructions: the empty instruction [Skip],
    assignment [Assign] and the while loop [While]. They can be sequenced
    using [Seq]. *)

Axiom
  (state : Set)
  (update : state -> Var -> Z -> option state)
  (evalA : state -> aExp -> option Z)
  (evalB : state -> bExp -> option bool).

(** We also assume [state] for representing the state of programs. This state
    will be updated with [update]. We can "evaluate" arithmetic expressions
    using [evalA] and boolean expressions using [evalB]. *)

Inductive exec : state -> instr -> state -> Prop :=
    | execSkip :
        forall s : state, exec s Skip s
    | execAssign :
        forall (s1 s2 : state) (v : Var) (a : aExp) (k : Z),
          evalA s1 a = Some k -> update s1 v k = Some s2 ->
            exec s1 (Assign v a) s2
    | execSeq :
        forall (s1 s2 s3 : state) (i1 i2 : instr),
          exec s1 i1 s2 -> exec s2 i2 s3 ->
            exec s1 (Seq i1 i2) s3
    | execWhileTrue :
        forall (s1 s2 s3 : state) (i : instr) (be : bExp),
          evalB s1 be = Some true ->
          exec s1 i s2 ->
          exec s2 (While be i) s3 ->
            exec s1 (While be i) s3
    | execWhileFalse :
        forall (s : state) (i : instr) (be : bExp),
          evalB s be = Some false -> exec s (While be i) s.

(** This is the relation that describes how to execute programs. [Skip] does
    nothing, [Assign] and [While] work as expected. [Seq i1 i2] means "execute
    i1 and then i2". *)

Hint Constructors instr exec.

(** We want to prove a rule for while from Hoare logic. It says, roughly,
    that if we execute a while loop and if a loop invariant [P] holds
    before the loop and after each iteration, then after the last iteration
    [P] also holds and moreover the condition of the while loop is false
    (for otherwise the loop wouldn't have terminated). *)

Theorem HoareWhileRule :
  forall (P : state -> Prop) (b : bExp) (i : instr) (s s' : state),
    (forall s1 s2 : state, P s1 -> evalB s1 b = Some true ->
      exec s1 i s2 -> P s2) -> P s -> exec s (While b i) s' ->
        P s' /\ evalB s' b = Some false.
Proof.
  intros. induction H1.
Restart.
  intros. destruct H1.
Restart.
  intros. inversion H1; subst.
Restart.
  intros. remember (While b i) as w.
  induction H1; intros; inversion Heqw; subst; eauto.
Qed.

(** We attempt to prove the theorem by induction on the hypothesis
    [H1 : exec s (While b i) s'] as this seems to be the only reasonable
    option. However, we fail miserably: [induction H1] gives us 5 subgoals
    that we can't solve.

    Clearly [H1] could have been created only with the constructors
    [execWhileTrue] and [execWhileFalse], but [induction] wants us to
    consider all 5 constructors. If we try [destruct], the same happens,
    but when we use [inversion], we get only 2 subgoals as expected. Why
    is this so?

    It's all very simple: if we do induction on a term whose type contains
    non-variables, [induction] and [destruct] both mess up and "forget"
    the form of this particular term, leaving us with unprovable subgoals.

    In our case, the type of [H1] is [exec s (While b i) s']. The arguments
    of [exec] are [s], [While b i] and [s'], of which [s] and [s'] are
    variables and [While b i] is not. So, both [induction] and [destruct]
    forget all information regarding the term [While b i].

    The situation is easy to deal with: we have to replace the problematic
    term [While b i] with a fresh variable [w], keeping an equality saying
    that [w = While b i]. This little bookkeeping saves us from losing
    the desired information.

    Two questions remain: why [inversion] succeeds, when [induction] and
    [destruct] fail? The answer is: [inversion] was crafted specially for
    not losing information in such cases. So, why doesn't [destruct] and
    [induction] work that way?

    As for [destruct], if you want it not to lose information, you can
    use [inversion] anyway. As for [induction]: it is supposed to be a
    basic and simple tactic, whereas [inversion] tends to generate very
    large proofterms. For example, in the above proofscript, after [intros]
    the proofterm is only 4 lines long, but after [intros. inversion H1] it
    is 214 lines long (you can check this yourself with the command [Show
    Proof]). This is the price of [inversion]. *)

(** **** Exercise (hard) *)

(** Write a tactic [replace_nonvars H] that replaces all nonvariables with
    variables in the hypothesis [H] and adds appropriate equalities to the
    context. Combine this tactic with the tactic [generalize_IH] that you
    implemented in one of the earlier exercises and some more tinkering to
    get a tactic [ind H], which:
    - generalizes the inductive hypothesis
    - replaces nonvariables with variables in the inductive hypothesis
    - does induction
    - inverses and substitutes all necessary equalities
    - cleans the mess it may have created in the context
    - finishes off easy subgoals with some basic automation *)

(** Your tactic should be able to solve [HoareWhilRule'] as shown below.
    How big is the proofterm it generates? Measure it in lines (mine is
    314 lines). *)

(* begin hide *)
Ltac gen x := generalize dependent x.

Ltac inv H := inversion H; subst.

Ltac invs := repeat
match goal with
    | H : ?f ?x1 ?x2 ?x3 = ?f ?x1' ?x2' ?x3' |- _ => inv H
    | H : ?f ?x1 ?x2 = ?f ?x1' ?x2' |- _ => inv H
    | H : ?f ?x1 = ?f ?x1' |- _ => inv H
end.

Ltac replace_nonvars H :=
match H with
    | ?f ?x1 => is_var x1; replace_nonvars f
    | ?f ?x1 =>
        let x1' := fresh "x1" in
        let H1 := fresh "H1" in remember x1 as x1' eqn: H1; replace_nonvars f
    | _ => idtac
end.

Ltac clean_eqs := repeat
match goal with
    | H : ?x = ?x |- _ => clear H
    | H : ?x = ?x -> _ |- _ => specialize (H eq_refl)
    | H : forall x, ?y = ?y -> ?P |- _ =>
        assert (H' := fun x => H x eq_refl); clear H; rename H' into H
end.

Ltac ind' H :=
match type of H with
    | ?T => replace_nonvars T; induction H; subst; try congruence;
        invs; clean_eqs; eauto
end.

Ltac ind H := try intros until H; generalize_IH H; ind' H.
(* end hide *)

Theorem HoareWhileRule' :
  forall (P : state -> Prop) (b : bExp) (i : instr) (s s' : state),
    (forall s1 s2 : state, P s1 -> evalB s1 b = Some true ->
      exec s1 i s2 -> P s2) -> P s -> exec s (While b i) s' ->
        P s' /\ evalB s' b = Some false.
Proof.
(* begin hide *)
  Require Import Equality.
  intros P b i s s' H H0 H1.
  gen H; gen H0.
  dependent induction H1; eauto.
Restart.
(* end hide *)
  intros. ind H1.
Qed.

End little_semantics.

(** * Grading *)

(** To get a 3 you need to prove all theorems that are stated, but whose
    proofs are omitted, and solve all exercises which are marked as easy.

    To get a 4 you need to get a 3 and additionally solve all exercises
    which are marked as medium.

    To get a 5 you need to get a 4 and additionally solve all exercises
    which are marked as hard. *)