(* H Represents 1, O k represent 2k, I k represents 2k + 1 *)
Inductive positive : Set :=
    | H : positive
    | O : positive -> positive
    | I : positive -> positive.

Inductive Z : Set :=
    | Z0 : Z
    | Zpos : positive -> Z
    | Zneg : positive -> Z.

Fixpoint Psucc (p : positive) : positive := match p with
    | H => O H
    | O k => I k
    | I k => O (Psucc k)
end.

Eval compute in I (I (O H)).

Fixpoint pos_even_bool (p : positive) : bool := match p with
    | H => false
    | I _ => false
    | O k => true
end.

Definition pos_25 := I (O (O (I H))).
Definition pos_24 := O (O (O (I H))).

Eval compute in pos_even_bool pos_25.
Eval compute in pos_even_bool pos_24.
Eval compute in pos_even_bool (O H).

(*Fixpoint pos_div4 (p : positive) : Z := match p with
    | H => Z0
    | I k*)

Inductive Rat : Set :=
    | One : Rat
    | N : Rat -> Rat
    | D : Rat -> Rat.

