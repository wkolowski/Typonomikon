Require Import List.
Import ListNotations.

Require Export Coq.Classes.SetoidClass.

Set Implicit Arguments.

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    | perm_nil : Permutation [] []
    | perm_skip : forall (x : A) (l l' : list A),
        Permutation l l' -> Permutation (x :: l) (x :: l')
    | perm_swap : forall (x y : A) (l : list A),
        Permutation (y :: x :: l) (x :: y :: l)
    | perm_trans : forall l l' l'' : list A,
        Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Hint Constructors Permutation.

Theorem Permutation_length :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> length l1 = length l2.
(* begin hide *)
Proof.
  induction 1; simpl; congruence.
Qed.
(* end hide *)

Theorem Permutation_nil :
  forall (A : Type) (l : list A), Permutation [] l -> l = [].
(* begin hide *)
Proof.
  intros. apply Permutation_length in H. simpl in H.
  destruct l; inversion H. trivial.
Qed.
(* end hide *)

Theorem Permutation_nil_cons :
  forall (A : Type) (l : list A) (x : A), ~ Permutation [] (x :: l).
(* begin hide *)
Proof.
  intros; intro. apply Permutation_nil in H. inversion H.
Qed.
(* end hide *)

Theorem Permutation_refl :
  forall (A : Type) (l : list A), Permutation l l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; auto.
Qed.
(* end hide *)

Theorem Permutation_trans :
  forall (A : Type) (l l' l'' : list A),
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.
(* begin hide *)
Proof.
  intros. eapply perm_trans; eauto.
Qed.
(* end hide *)

Theorem Permutation_sym :
  forall (A : Type) (l l' : list A), Permutation l l' -> Permutation l' l.
(* begin hide *)
Proof.
  induction 1; auto. eapply Permutation_trans; eauto.
Qed.
(* end hide *)

Theorem Permutation_Equivalence:
  forall A : Type, RelationClasses.Equivalence (Permutation (A := A)).
(* begin hide *)
Proof.
  split; red.
    apply Permutation_refl.
    apply Permutation_sym.
    apply Permutation_trans.
Qed.
(* end hide *)

Instance Permutation_cons :
  forall A : Type,
    Proper (eq ==> @Permutation A ==> @Permutation A) (@cons A).
(* begin hide *)
Proof.
  unfold Proper, respectful. intros; subst; auto.
Defined.
(* end hide *)

Theorem Permutation_in :
  forall (A : Type) (l l' : list A) (x : A),
    Permutation l l' -> In x l -> In x l'.
(* begin hide *)
Proof.
  induction 1; intros; simpl; auto.
    inversion H0; auto.
    inversion H; auto. inversion H0; auto.
Qed.
(* end hide *)

(*Permutation_in':
  forall A : Type,
  Morphisms.Proper
    (Morphisms.respectful eq (Morphisms.respectful (Permutation (A:=A)) iff))
    (List.In (A:=A))*)

Theorem Permutation_app_head :
  forall (A : Type) (l tl tl' : list A),
    Permutation tl tl' -> Permutation (l ++ tl) (l ++ tl').
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros; auto.
Qed.
(* end hide *)

Hint Resolve Permutation_refl.

Theorem Permutation_app_tail :
  forall (A : Type) (l l' tl : list A),
    Permutation l l' -> Permutation (l ++ tl) (l' ++ tl).
(* begin hide *)
Proof.
  induction 1; simpl; intros; eauto.
Qed.
(* end hide *)

Theorem Permutation_app :
  forall (A : Type) (l m l' m' : list A),
    Permutation l l' -> Permutation m m' -> Permutation (l ++ m) (l' ++ m').
(* begin hide *)
Proof.
  unfold Proper, respectful.
  intros A l m l' m' H. generalize dependent m'; generalize dependent m.
  induction H; simpl; intros; eauto.
  eapply perm_trans.
    apply perm_swap.
    do 2 constructor. apply Permutation_app_head. assumption.
Qed.
(* end hide *)

Instance Permutation_app':
  forall A : Type,
    Proper (@Permutation A ==> @Permutation A ==> @Permutation A) (@app A).
(* begin hide *)
Proof.
  unfold Proper, respectful.
  intros. apply Permutation_app; assumption.
Defined.
(* end hide *)

Theorem Permutation_add_inside :
  forall (A : Type) (x : A) (l1 l2 l1' l2' : list A),
    Permutation l1 l1' -> Permutation l2 l2' ->
    Permutation (l1 ++ x :: l2) (l1' ++ x :: l2').
(* begin hide *)
Proof.
  intros. (* rewrite H. *) apply Permutation_app'; eauto.
Qed.
(* end hide *)


Theorem Permutation_cons_append :
  forall (A : Type) (l : list A) (x : A),
    Permutation (x :: l) (l ++ [x]).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros; auto.
  eapply perm_trans.
    apply perm_swap.
    constructor. apply IHt.
Qed.
(* end hide *)

Theorem Permutation_app_comm :
  forall (A : Type) (l l' : list A), Permutation (l ++ l') (l' ++ l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros; rewrite ?app_nil_r; auto.
  induction l' as [| h' t']; simpl; rewrite ?app_nil_r; auto.
Restart.
  induction l as [| h t]; destruct l' as [| h' t'];
  simpl; rewrite ?app_nil_r; auto.
  specialize (IHt (h' :: t')). eapply Permutation_trans.
    apply Permutation_cons_append.
  rewrite app_comm_cons.
Permutation_cons_app:
  forall (A : Type) (l l1 l2 : list A) (a : A),
  Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2)
Permutation_Add:
  forall (A : Type) (a : A) (l l' : list A),
  List.Add a l l' -> Permutation (a :: l) l'
Permutation_middle:
  forall (A : Type) (l1 l2 : list A) (a : A),
  Permutation (a :: (l1 ++ l2)%list) (l1 ++ a :: l2)
Permutation_rev: forall (A : Type) (l : list A), Permutation l (List.rev l)
Permutation_rev':
  forall A : Type,
  Morphisms.Proper
    (Morphisms.respectful (Permutation (A:=A)) (Permutation (A:=A)))
    (List.rev (A:=A))
Permutation_length:
  forall (A : Type) (l l' : list A), Permutation l l' -> length l = length l'
Permutation_length':
  forall A : Type,
  Morphisms.Proper (Morphisms.respectful (Permutation (A:=A)) eq)
    (length (A:=A))
Permutation_ind_bis:
  forall (A : Type) (P : list A -> list A -> Prop),
  P nil nil ->
  (forall (x : A) (l l' : list A),
   Permutation l l' -> P l l' -> P (x :: l)%list (x :: l')%list) ->
  (forall (x y : A) (l l' : list A),
   Permutation l l' -> P l l' -> P (y :: x :: l)%list (x :: y :: l')%list) ->
  (forall l l' l'' : list A,
   Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
  forall l l' : list A, Permutation l l' -> P l l'
Permutation_nil_app_cons:
  forall (A : Type) (l l' : list A) (x : A), ~ Permutation nil (l ++ x :: l')
Permutation_Add_inv:
  forall (A : Type) (a : A) (l1 l2 : list A),
  Permutation l1 l2 ->
  forall l1' l2' : list A,
  List.Add a l1' l1 -> List.Add a l2' l2 -> Permutation l1' l2'
Permutation_app_inv:
  forall (A : Type) (l1 l2 l3 l4 : list A) (a : A),
  Permutation (l1 ++ a :: l2) (l3 ++ a :: l4) ->
  Permutation (l1 ++ l2) (l3 ++ l4)
Permutation_cons_inv:
  forall (A : Type) (l l' : list A) (a : A),
  Permutation (a :: l) (a :: l') -> Permutation l l'
Permutation_cons_app_inv:
  forall (A : Type) (l l1 l2 : list A) (a : A),
  Permutation (a :: l) (l1 ++ a :: l2) -> Permutation l (l1 ++ l2)
Permutation_app_inv_l:
  forall (A : Type) (l l1 l2 : list A),
  Permutation (l ++ l1) (l ++ l2) -> Permutation l1 l2
Permutation_app_inv_r:
  forall (A : Type) (l l1 l2 : list A),
  Permutation (l1 ++ l) (l2 ++ l) -> Permutation l1 l2
Permutation_length_1_inv:
  forall (A : Type) (a : A) (l : list A),
  Permutation (a :: nil) l -> l = (a :: nil)%list
Permutation_length_1:
  forall (A : Type) (a b : A), Permutation (a :: nil) (b :: nil) -> a = b
Permutation_length_2_inv:
  forall (A : Type) (a1 a2 : A) (l : list A),
  Permutation (a1 :: (a2 :: nil)%list) l ->
  l = (a1 :: a2 :: nil)%list \/ l = (a2 :: a1 :: nil)%list
Permutation_length_2:
  forall (A : Type) (a1 a2 b1 b2 : A),
  Permutation (a1 :: (a2 :: nil)%list) (b1 :: (b2 :: nil)%list) ->
  a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1
NoDup_Permutation:
  forall (A : Type) (l l' : list A),
  List.NoDup l ->
  List.NoDup l' ->
  (forall x : A, List.In x l <-> List.In x l') -> Permutation l l'
NoDup_Permutation_bis:
  forall (A : Type) (l l' : list A),
  List.NoDup l ->
  List.NoDup l' ->
  length l' <= length l -> List.incl l l' -> Permutation l l'
Permutation_NoDup:
  forall (A : Type) (l l' : list A),
  Permutation l l' -> List.NoDup l -> List.NoDup l'
Permutation_NoDup':
  forall A : Type,
  Morphisms.Proper (Morphisms.respectful (Permutation (A:=A)) iff)
    (List.NoDup (A:=A))
Permutation_map:
  forall (A B : Type) (f : A -> B) (l l' : list A),
  Permutation l l' -> Permutation (List.map f l) (List.map f l')
Permutation_map':
  forall (A B : Type) (f : A -> B),
  Morphisms.Proper
    (Morphisms.respectful (Permutation (A:=A)) (Permutation (A:=B)))
    (List.map f)
nat_bijection_Permutation:
  forall (n : nat) (f : nat -> nat),
  FinFun.bFun n f ->
  FinFun.Injective f -> let l := List.seq 0 n in Permutation (List.map f l) l
Permutation_nth_error:
  forall (A : Type) (l l' : list A),
  Permutation l l' <->
  length l = length l' /\
  (exists f : nat -> nat,
     FinFun.Injective f /\
     (forall n : nat, List.nth_error l' n = List.nth_error l (f n)))
Permutation_nth_error_bis:
  forall (A : Type) (l l' : list A),
  Permutation l l' <->
  (exists f : nat -> nat,
     FinFun.Injective f /\
     FinFun.bFun (length l) f /\
     (forall n : nat, List.nth_error l' n = List.nth_error l (f n)))
Permutation_nth:
  forall (A : Type) (l l' : list A) (d : A),
  Permutation l l' <->
  (let n := length l in
   length l' = n /\
   (exists f : nat -> nat,
      FinFun.bFun n f /\
      FinFun.bInjective n f /\
      (forall x : nat, x < n -> List.nth x l' d = List.nth (f x) l d)))
