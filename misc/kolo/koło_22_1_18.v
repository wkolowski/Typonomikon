Inductive wesołe_zdanie : Prop :=
    | cokolwiek : wesołe_zdanie
    | cokolwiek' : wesołe_zdanie.

Theorem wesołe_zdanie_true : wesołe_zdanie.
Proof.
  exact cokolwiek.
Qed.

Goal wesołe_zdanie <-> True.
Proof.
  split; intro.
    trivial.
    exact cokolwiek'.
Qed.

Inductive Z : Prop :=
  | c0 : Z -> Z.

Inductive Z' : Prop :=
  | c1 : Z'
  | c2 : Z' -> Z'.

(*
Print nat.

Inductive N : Type :=
    | zero : N
    | succ : N -> N.
*)

Inductive F : Prop.

Print F.

Goal F <-> True.
Proof.
  split; intro.
    exact I.
    constructor.
Qed.

Locate "\/".