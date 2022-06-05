Require Import Recdef Nat.

Require Import List.
Import ListNotations.

From Equations Require Import Equations.

Unset Guard Checking.
Function euclid_mod (p q : nat) {struct p} : nat :=
match p with
| 0 => q
| _ => euclid_mod (modulo q p) p
end.
Set Guard Checking.

Compute euclid_mod 0 0.

Inductive euclid_mod_graph : nat -> nat -> nat -> Prop :=
| emg_0 : forall q : nat, euclid_mod_graph 0 q q
| emg_S : forall p q r : nat, euclid_mod_graph (modulo q p) p r -> euclid_mod_graph p q r.

Inductive euclid_mod_graph' : Type :=
| emg_0' : forall q : nat, euclid_mod_graph'
| emg_S' : forall p q r : nat, euclid_mod_graph (modulo q p) p r -> euclid_mod_graph p q r.

Inductive Qmod : Type :=
| 

