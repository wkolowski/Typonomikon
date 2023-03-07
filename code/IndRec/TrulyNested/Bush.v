(** Wzięte
    #<a class='link' href='https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-hosc09.pdf'
    stąd.</a>#. *)

Set Universe Polymorphism.

Unset Positivity Checking.
Inductive Bush (A : Type) : Type :=
| Leaf : Bush A
| Node : A -> Bush (Bush A) -> Bush A.
Set Positivity Checking.

Arguments Leaf {A}.
Arguments Node {A} _ _.



Unset Guard Checking.
Fixpoint map {A B : Type} (f : A -> B) (b : Bush A) {struct b} : Bush B :=
match b with
| Leaf      => Leaf
| Node v bs => Node (f v) (map (map f) bs)
end.

Fixpoint sum (b : Bush nat) : nat :=
match b with
| Leaf => 0
| Node n bs => n + sum (map sum bs)
end.

Fixpoint size {A : Type} (b : Bush A) {struct b} : nat :=
match b with
| Leaf => 0
| Node v bs => 1 + sum (map size bs)
end.

(*
From Typonomikon Require Import D5.

Fixpoint toList {A : Type} (b : Bush A) {struct b} : list A :=
match b with
| Leaf      => []
| Node v bs => v :: join (toList (map toList bs))
end.
*)

Fixpoint replicate (h : nat) {A : Type} (x : A) : Bush A :=
match h with
| 0    => Leaf
| S h' => Node x (replicate h' (replicate h' x))
end.

Fixpoint count {A : Type} (p : A -> nat) (b : Bush A) {struct b} : nat :=
match b with
| Leaf => 0
| Node x b' => p x + count (count p) b'
end.

(* Fixpoint app {A : Type} (b1 b2 : Bush A) : Bush A :=
match b1 with
| Leaf     => b2
| Node h t => Node h (
 *)

(* Fixpoint join {A : Type} (b : Bush (Bush A)) {struct b} : Bush A :=
match b with
| Leaf => Leaf
| Node v bs => Node (join v) (join (map join bs))
end.
 *)

Compute (replicate 3 (Node 5 Leaf)).

Fixpoint nums (n : nat) : Bush nat :=
match n with
| 0 => Node 0 Leaf
| S n' => Node n (map nums (nums n'))
end.

Compute size (nums 4).
(* Compute count (fun n => if even n then 1 else 0) (nums 10). *)

Set Guard Checking.

Require Import FunctionalExtensionality.

Unset Positivity Checking.
Inductive Bush' {A : Type} (P : A -> Type) : Bush A -> Type :=
| Leaf' : Bush' P Leaf
| Node' :
    forall (x : A) (b : Bush (Bush A)),
      P x -> Bush' (Bush' P) b -> Bush' P (Node x b).
Set Positivity Checking.

Fixpoint Bush_ind_deep
  (P : forall (A : Type) (Q : A -> Type), Bush A -> Type)
  (leaf : forall (A : Type) (Q : A -> Type), P A Q Leaf)
  (node : forall (A : Type) (Q : A -> Type) (x : A) (b : Bush (Bush A)),
            Q x -> P (Bush A) (Bush' Q) b -> P A Q (Node x b))
  {A : Type} (Q : A -> Type)
  {b : Bush A} (b' : Bush' Q b) {struct b'} : P A Q b.
Proof.
  destruct b' as [| x b Qx Pb].
  - apply leaf.
  - apply node.
    + exact Qx.
    + apply Bush_ind_deep; try assumption.
Defined.

Fixpoint Bush'_True {A : Type} {Q : A -> Type} (b : Bush A) {struct b} :
  (forall x : A, Q x) -> Bush' Q b.
Proof.
  destruct b as [| x b']; intros H.
  - now constructor.
  - constructor; [easy |].
    apply Bush'_True.
    intros b''.
    now apply Bush'_True.
Defined.

Fixpoint Bush_ind
  (P : forall (A : Type), Bush A -> Type)
  (leaf : forall (A : Type), P A Leaf)
  (node : forall (A : Type) (x : A) (b : Bush (Bush A)),
            P (Bush A) b -> P A (Node x b))
  {A : Type}
  {b : Bush A} {struct b} : P A b.
Proof.
  refine (@Bush_ind_deep (fun A _ => P A) _ _ A (fun _ => True) b _); intros.
  - apply leaf.
  - apply node; assumption.
  - now apply Bush'_True.
Defined.

(*
Fixpoint Bush_ind_deep'
  (P : forall (A : Type) (Q : A -> Type), Bush A -> Type)
  (leaf : forall (A : Type) (Q : A -> Type), P A Q Leaf)
  (node : forall (A : Type) (Q : A -> Type) (x : A) (b : Bush (Bush A)),
            Q x -> P (Bush A) (P A Q) b -> P A Q (Node x b))
  {A : Type} (Q : A -> Type)
  {b : Bush A} (b' : Bush' Q b) {struct b'} : P A Q b.
Proof.
  destruct b' as [| x b Qx Pb].
    apply leaf.
    apply node.
      exact Qx.
      apply Bush_ind_deep'; try assumption. revert P Q leaf node Qx b Pb. fix IH 6.
        destruct 4; constructor.
          apply Bush_ind_deep'; assumption. Check Bush'.
          specialize (IH (fun A Q => Bush' (P A Q))). assumption.
Defined.
*)

Fixpoint Bush_ind_deep''
  {A : Type} (Q : A -> Type) (P : Bush A -> Type)
  (leaf : P Leaf)
  (node : forall (x : A) (b : Bush (Bush A)),
            Q x -> Bush' P b -> P (Node x b))
  {b : Bush A} (b' : Bush' Q b) {struct b'} : P b.
Proof.
  destruct b' as [| x b Qx Pb].
    apply leaf.
    apply node.
      exact Qx.
      revert P Q leaf node Qx b Pb. fix IH 6; intros.
        destruct Pb; constructor.
          apply (Bush_ind_deep'' A Q P); assumption.
Abort.










Lemma map_map :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (b : Bush A),
    map g (map f b) = map (fun x => g (f x)) b.
Proof.
  intro.
  pose (P := (fun (A : Type) (b : Bush A) => forall (B C : Type) (f : A -> B) (g : B -> C)
    (b : Bush A), map g (map f b) = map (fun x => g (f x)) b)).
  refine (Bush_ind P _ _).
  - unfold P; cbn; intros.
Abort.

Unset Guard Checking.
Lemma map_map :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (b : Bush A),
    map g (map f b) = map (fun x => g (f x)) b.
Proof.
  fix IH 6.
  destruct b as [| h t]; cbn.
  - reflexivity.
  - rewrite IH.
    do 2 f_equal.
    extensionality bb.
    now rewrite IH.
Qed.
Set Guard Checking.