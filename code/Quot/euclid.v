Require Import Recdef Nat Lia.

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
| emg_S' : forall p q r : nat, euclid_mod_graph' -> euclid_mod_graph'.

From Equations Require Import Equations.

(* Equations? euclid_sub (p q : nat) {_ : p <> 0} {_ : q <> 0} : nat by wf (p + q) lt :=
| p, q with (PeanoNat.Nat.compare_spec p q) => {
  | CompLt H => euclid_sub p (q - p)
  | @CompEq H => p
  | CompGt H => euclid_sub (p - q) q }.
Next Obligation. *)

Fixpoint euclid_sub (pq : nat * nat) {Hp : fst pq <> 0} {Hq : snd pq <> 0} {struct pq} : nat.
Proof.
refine (
match Compare_dec.lt_eq_lt_dec (fst pq) (snd pq) with
| inleft (left H) => @euclid_sub (fst pq, snd pq - fst pq) Hp ltac:(cbn; lia)
| inleft (right _) => fst pq
| inright H => @euclid_sub (fst pq - snd pq, snd pq) ltac:(cbn; lia) Hq
end).
Abort.

Function euclid_sub (pq : nat * nat) {Hp : fst pq <> 0} {Hq : snd pq <> 0}
  {measure (fun '(p, q) => p + q) pq} : nat :=
match Compare_dec.lt_eq_lt_dec (fst pq) (snd pq) with
| inleft (left H) => @euclid_sub (fst pq, snd pq - fst pq) Hp ltac:(cbn; lia)
| inleft (right _) => fst pq
| inright H => @euclid_sub (fst pq - snd pq, snd pq) ltac:(cbn; lia) Hq
end.
Proof.
  - intros [p q] **; simpl in *; lia.
  - intros [p q] **; simpl in *; lia.
Defined.