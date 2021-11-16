(* Wzięte stąd: https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-hosc09.pdf *)


Inductive BushF (F : Type -> Type) (A : Type) : Type :=
    | LeafF : BushF F A
    | NodeF : A -> F (F A) -> BushF F A.

Fail Inductive Bush (A : Type) : Type :=
    | In : BushF Bush A -> Bush A.

Definition ListC (A : Type) : Type :=
  forall (R : Type) (nil : R) (cons : A -> R -> R), R.

Definition BushC (A : Type) : Type :=
  forall (F : Type -> Type) (R : Type) (leaf : R) (node : A -> F R -> R), R.

Definition leaf {A : Type} : BushC A :=
  fun F R leaf node => leaf.

Definition node {A : Type} (x : A) (b : BushC (BushC A)) : BushC A.
Proof.
  unfold BushC.
  intros F R leaf node.
  apply (node x).
  unfold BushC in b.
Abort.

Definition mapC {A B : Type} (f : A -> B) (b : BushC A) : BushC B.
Proof.
  unfold BushC in *.
  intros F R leaf node.
  specialize (b F R).
  apply b.
    exact leaf.
    intros a ffr. apply node.
      apply f. exact a.
      exact ffr.
Defined.

Unset Positivity Checking.
Inductive Bush (A : Type) : Type :=
    | Leaf : Bush A
    | Node : A -> Bush (Bush A) -> Bush A.
Set Positivity Checking.

Arguments Leaf {A}.
Arguments Node {A} _ _.

Require Import D5.

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

Fixpoint toList {A : Type} (b : Bush A) {struct b} : list A :=
match b with
    | Leaf      => []
    | Node v bs => v :: join (toList (map toList bs))
end.

Fixpoint replicate (h : nat) {A : Type} (x : A) : Bush A :=
match h with
    | 0    => Leaf
    | S h' => Node x (replicate h' (replicate h' x))
end.




(* Fixpoint join {A : Type} (b : Bush (Bush A)) {struct b} : Bush A :=
match b with
    | Leaf => Leaf
    | Node v bs => Node (join v) (join (map join bs))
end.
 *)

Compute  (replicate 3 (Node 5 Leaf)).

Set Guard Checking.

Require Import FunctionalExtensionality.

Print Bush.
Unset Positivity Checking.
Inductive Bush' {A : Type} (P : A -> Type) : Bush A -> Type :=
    | Leaf' : Bush' P Leaf
    | Node' : forall (x : A) (b : Bush (Bush A)),
                P x -> Bush' (Bush' P) b -> Bush' P (Node x b).
Set Positivity Checking.

Fixpoint Bush_ind_deep
  (P : forall (A : Type) (Q : A -> Type), Bush A -> Type)
  (leaf : forall (A : Type) (Q : A -> Type), P A Q Leaf)
  (node : forall (A : Type) (Q : A -> Type) (x : A) (b : Bush (Bush A)),
            Q x -> P (Bush A) (Bush' Q (*P A Q*)) b -> P A Q (Node x b))
  {A : Type} (Q : A -> Type)
  {b : Bush A} (b' : Bush' Q b) {struct b'} : P A Q b.
Proof.
  destruct b' as [| x b Qx Pb].
    apply leaf.
    apply node.
      exact Qx.
      apply Bush_ind_deep; try assumption.
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
    apply leaf.
    apply node. assumption.
    admit.
Admitted.

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
          apply Bush_ind_deep'; assumption.
          apply (IH (fun A Q => . assumption.
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
  pose (P := (fun (A : Type) (b : Bush A) => forall (B C : Type) (f : A -> B) (g : B -> C), map g (map f b) = map (fun x => g (f x)) b)).
  intros B C f g b. revert B C f g.
  refine (Bush_ind P _ _).
    unfold P; cbn; intros. reflexivity.
    unfold P; cbn; intros. f_equal. rewrite !H. f_equal.
      extensionality bb. rewrite H.
  
  fix IH 6.
  destruct b as [| v bs]; cbn.
    reflexivity.
    f_equal. rewrite IH. f_equal.
      extensionality x. rewrite IH. reflexivity.
Qed.