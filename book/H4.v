(** * H4: Wincyj relacji *)

Require Import H3.

(** W tym rozdziale dalej będziemy zajmować się relacjami (a konkretnie relacjami
    binarnymi i homogenicznymi), ale nudniejszymi i mniej ważnymi niż w poprzednim
    rozdziale. *)

(*  left_unique           : forall (a a' : A) (b : B), R a b -> R a' b -> a = a'
    right_unique          : forall (a : A) (b b' : B), R a b -> R a b' -> b = b'

    left_total            : forall a : A, exists b : B, R a b
    right_total           : forall b : B, exists a : A, R a b

    reflexive             : forall x : A, R x x
    antireflexive         : forall x : A, ~ R x x
    irreflexive           : exists x : A, ~ R x x
(*  not_antireflexive     : exists x : A, R x x *)
    coreflexive           : forall x y : A, R x y -> x = y

    left_quasireflexive   : forall x y : A, R x y -> R x x
    right_quasireflexive  : forall x y : A, R x y -> R y y
    quasireflexive        : forall x y : A, R x y -> R x x /\ R y y

    symmetric             : forall x y : A, R x y -> R y x
    antisymmetric         : forall x y : A, R x y -> R y x -> False
    weakly_antisymmetric  : forall x y : A, R x y -> R y x -> x = y
    asymmetric            : exists x y : A, R x y /\ ~ R y x
(*  not_antisymmetric     : exists x y : A, R x y /\ R y x *)

    transitive            : forall x y z : A, R x y -> R y z -> R x z
    antitransitive        : forall x y z : A, R x y -> R y z -> R x z -> False
(*  weakly_antitransitive : forall x y z : A, R x y -> R y z -> R x z -> x = y /\ y = z *)
    cotransitive          : forall {x z : A}, R x z -> forall y : A, R x y \/ R y z
    quasitransitive       : Transitive (AsymmetricPart R)
(*  trans. of incomp.     : TOOD *)
(*  intransitive          : exists x y z : A, R x y /\ R y z /\ ~ R x z *)

    circular              : forall x y z : A, R x y -> R y z -> R z x
    right_euclidean       : forall x y z : A, R x y -> R x z -> R y z
    left_euclidean        : forall x y z : A, R y x -> R z x -> R y z
    confluent             : forall x y z : A, R x y -> R x z -> exists w : A, R y w /\ R z w

    dense                 : forall x y : A, R x y -> exists z : A, R x z /\ R z y

    total                 : forall x y : A, R x y \/ R y x
    weakly_total          : forall x y : A, ~ R x y -> R y x

    trichotomous          : forall x y : A, R x y \/ x = y \/ R y x
    weakly_trichotomous   : forall x y : A, x <> y -> R x y \/ R y x
    connected             : forall x y : A, ~ R x y /\ ~ R y x -> x = y

    weakly_extensional    : forall x y : A, (forall t : A, R t x <-> R t y) -> x = y

    well_founded          : forall x : A, Acc R x
    ill_founded           : exists x : A, Inaccessible R x *)