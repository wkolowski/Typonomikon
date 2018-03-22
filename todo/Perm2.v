Require Import List.
Import ListNotations.

Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

Inductive Swap {A : Type} : list A -> list A -> Prop :=
    | swap_nil : Swap [] []
    | swap_skip : forall (x : A) (l l' : list A),
        Swap l l' -> Swap (x :: l) (x :: l')
    | swap_swap : forall (x y : A) (l : list A),
        Swap (y :: x :: l) (x :: y :: l).

Inductive Perm {A : Type} : list A -> list A -> Prop :=
    | perm_step :
        forall l1 l2 : list A,
          Swap l1 l2 -> Perm l1 l2
    | perm_trans_l :
        forall l1 l2 l3 : list A,
          Swap l1 l2 -> Perm l2 l3 -> Perm l1 l3.

Hint Constructors Swap Perm.

Lemma Swap_length :
  forall (A : Type) (l1 l2 : list A),
    Swap l1 l2 -> length l1 = length l2.
(* begin hide *)
Proof.
  induction 1; cbn; rewrite ?IHSwap; reflexivity.
Qed.
(* end hide *)

Lemma Swap_refl :
  forall (A : Type) (l : list A),
    Swap l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Instance Swap_refl' :
  forall A : Type, Reflexive (@Swap A).
(* begin hide *)
Proof.
  red. apply Swap_refl.
Defined.
(* end hide *)

Lemma Swap_sym :
  forall (A : Type) (l1 l2 : list A),
    Swap l1 l2 -> Swap l2 l1.
(* begin hide *)
Proof.
  induction 1; constructor; assumption.
Qed.
(* end hide *)

Instance Swap_sym' :
  forall A : Type, Symmetric (@Swap A).
(* begin hide *)
Proof.
  red. apply Swap_sym.
Defined.
(* end hide *)

Lemma Swap_nil_l :
  forall (A : Type) (l : list A),
    Swap [] l -> l = [].
(* begin hide *)
Proof.
  inversion 1. reflexivity.
Qed.
(* end hide *)

Lemma Swap_nil_r :
  forall (A : Type) (l : list A),
    Swap l [] -> l = [].
(* begin hide *)
Proof.
  inversion 1. reflexivity.
Qed.
(* end hide *)

Lemma Swap_length_1 :
  forall (A : Type) (l1 l2 : list A),
    length l1 = 1 -> Swap l1 l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction 2.
    reflexivity.
    destruct l; inversion H. apply Swap_nil_l in H0. subst. reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma Swap_singl :
  forall (A : Type) (x : A) (l : list A),
    Swap [x] l -> l = [x].
(* begin hide *)
Proof.
  inversion 1; subst. inversion H3. reflexivity.
Qed.
(* end hide *)

Lemma Swap_app_l :
  forall (A : Type) (l1 l1' l2 : list A),
    Swap l1 l1' -> Swap (l1 ++ l2) (l1' ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Swap_refl.
    constructor. assumption.
    constructor.
Qed.
(* end hide *)

Lemma Swap_app_r :
  forall (A : Type) (l1 l2 l2' : list A),
    Swap l2 l2' -> Swap (l1 ++ l2) (l1 ++ l2').
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    constructor. apply IHt1, H.
Qed.
(* end hide *)

Lemma Swap_in :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Swap l1 l2 -> In x l1 -> In x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    assumption.
    destruct H0; subst; [left | right].
      reflexivity.
      apply IHSwap, H0.
    decompose [or] H; clear H; subst.
      right; left. reflexivity.
      left. reflexivity.
      right; right. assumption.
Qed.
(* end hide *)

Lemma Swap_cons :
  forall (A : Type) (h : A) (t l : list A),
    Swap (h :: t) l ->
      exists l1 l2 : list A, l = l1 ++ h :: l2.
(* begin hide *)
Proof.
  inversion 1; subst.
    exists [], l'. cbn. reflexivity.
    exists [x], l0. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Swap_cons_inv :
  forall (A : Type) (h : A) (t1 t2 : list A),
    Swap (h :: t1) (h :: t2) -> Swap t1 t2.
(* begin hide *)
Proof.
  inversion 1; subst.
    assumption.
    reflexivity.
Qed.
(* end hide *)

Lemma Perm_length :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> length l1 = length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Swap_length. assumption.
    rewrite <- IHPerm. apply Swap_length. assumption.
Qed.
(* end hide *)

Lemma Perm_nil :
  forall (A : Type) (l : list A),
    Perm [] l -> l = [].
(* begin hide *)
Proof.
  intros. remember [] as l'. generalize dependent Heql'.
  induction H; intros; subst.
    apply Swap_nil_l. assumption.
    apply Swap_nil_l in H. subst. apply IHPerm. reflexivity.
Qed.
(* end hide *)

Lemma Perm_length_1:
  forall (A : Type) (l1 l2 : list A),
    length l1 = 1 -> Perm l1 l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction 2; cbn in *.
    destruct l1 as [| h1 t1]; cbn in *.
      inversion H.
      destruct l2 as [| h2 t2].
        symmetry in H0. apply Swap_nil_l in H0. inversion H0.
        destruct t1.
          apply Swap_singl in H0. inversion H0; subst. reflexivity.
          cbn in H. inversion H.
    apply Swap_length_1 in H0; subst.
      apply IHPerm, H.
      assumption.
Qed.
(* end hide *)

Lemma Perm_singl :
  forall (A : Type) (a b : A),
    Perm [a] [b] -> a = b.
(* begin hide *)
Proof.
  intros. apply Perm_length_1 in H.
    inversion H. reflexivity.
    cbn. reflexivity.
Qed.
(* end hide *)

Lemma Perm_nil_cons :
  forall (A : Type) (l : list A) (x : A),
    ~ Perm [] (x :: l).
(* begin hide *)
Proof.
  intros; intro. apply Perm_nil in H. inversion H.
Qed.
(* end hide *)

Lemma Perm_refl :
  forall (A : Type) (l : list A),
    Perm l l.
(* begin hide *)
Proof.
  intros. constructor. reflexivity.
Qed.
(* end hide *)

Lemma perm_trans_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Perm l1 l2 -> Swap l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  induction 1; intros.
    apply perm_trans_l with l2.
      assumption.
      constructor. assumption.
    apply perm_trans_l with l2.
      assumption.
      apply IHPerm, H1.
Qed.
(* end hide *)

Lemma Perm_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  induction 1; intros.
    apply perm_trans_l with l2; assumption.
    apply perm_trans_l with l2.
      assumption.
      apply IHPerm, H1.
Qed.
(* end hide *)

Lemma Perm_sym :
  forall (A : Type) (l l' : list A),
    Perm l l' -> Perm l' l.
(* begin hide *)
Proof.
  induction 1.
    constructor. symmetry. assumption.
    generalize dependent l1. induction H0; intros.
      apply perm_trans_r with l1.
        assumption.
        symmetry. assumption.
      apply perm_trans_r with l1.
        assumption.
        symmetry. assumption.
Qed.
(* end hide *)

Instance Perm_Equivalence:
  forall A : Type, RelationClasses.Equivalence (Perm (A := A)).
(* begin hide *)
Proof.
  split; red.
    apply Perm_refl.
    apply Perm_sym.
    apply Perm_trans.
Qed.
(* end hide *)

Lemma Perm_skip :
  forall (A : Type) (h : A) (t1 t2 : list A),
    Perm t1 t2 -> Perm (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  induction 1.
    do 2 constructor. assumption.
    apply Perm_trans with (h :: l2).
      do 2 constructor. assumption.
      assumption.
Qed.
(* end hide *)

Instance Perm_cons :
  forall A : Type,
    Proper (eq ==> @Perm A ==> @Perm A) (@cons A).
(* begin hide *)
Proof.
  unfold Proper, respectful. intros; subst.
  apply Perm_skip. assumption.
Defined.
(* end hide *)

Lemma Perm_in :
  forall (A : Type) (l l' : list A) (x : A),
    Perm l l' -> In x l -> In x l'.
(* begin hide *)
Proof.
  induction 1; intros.
    apply Swap_in with l1; assumption.
    apply IHPerm, Swap_in with l1; assumption.
Qed.
(* end hide *)

Lemma Perm_in' :
  forall A : Type,
    Proper (eq ==> @Perm A ==> iff) (@In A).
(* begin hide*)
Proof.
  unfold Proper, respectful; intros.
  subst. split; intro H; eapply Perm_in; eauto.
  symmetry. assumption.
Qed.
(* end hide *)

Lemma Perm_app_l :
  forall (A : Type) (l1 l2 l2' : list A),
    Perm l2 l2' -> Perm (l1 ++ l2) (l1 ++ l2').
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    apply Perm_skip. apply IHt1, H.
Qed.
(* end hide *)

Lemma Perm_app_r :
  forall (A : Type) (l1 l1' l2 : list A),
    Perm l1 l1' -> Perm (l1 ++ l2) (l1' ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. apply Swap_app_l. assumption.
    apply Perm_trans with (l0 ++ l2).
      constructor. apply Swap_app_l. assumption.
      assumption.
Qed.
(* end hide *)

Lemma Perm_app :
  forall (A : Type) (l1 l1' l2 l2' : list A),
    Perm l1 l1' -> Perm l2 l2' -> Perm (l1 ++ l2) (l1' ++ l2').
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    apply Perm_trans with (l0 ++ l2).
      constructor. apply Swap_app_l. assumption.
      apply Perm_app_l. assumption.
    apply Perm_trans with (l0 ++ l2).
      constructor. apply Swap_app_l. assumption.
      apply IHPerm, H1.
Qed.
(* end hide *)

Instance Perm_app':
  forall A : Type,
    Proper (@Perm A ==> @Perm A ==> @Perm A) (@app A).
(* begin hide *)
Proof.
  unfold Proper, respectful.
  intros. apply Perm_app; assumption.
Defined.
(* end hide *)

Lemma Perm_add_inside :
  forall (A : Type) (x : A) (l1 l2 l1' l2' : list A),
    Perm l1 l1' -> Perm l2 l2' ->
    Perm (l1 ++ x :: l2) (l1' ++ x :: l2').
(* begin hide *)
Proof.
  intros. rewrite H, H0. reflexivity.
Qed.
(* end hide *)

Lemma Perm_cons_append :
  forall (A : Type) (l : list A) (x : A),
    Perm (x :: l) (l ++ [x]).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    apply Perm_trans with (h :: x :: t).
      do 2 constructor.
      apply Perm_skip, IHt.
Qed.
(* end hide *)

Lemma Perm_swap :
  forall (A : Type) (x y : A) (l : list A),
    Perm (x :: y :: l) (y :: x :: l).
(* begin hide *)
Proof. do 2 constructor. Qed.
(* end hide *)

Lemma Perm_app_com :
  forall (A : Type) (l1 l2 : list A),
    Perm (l1 ++ l2) (l2 ++ l1).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2];
  cbn; rewrite ?app_nil_r; try reflexivity.
  rewrite IHt1. cbn. rewrite Perm_swap. apply Perm_skip.
  rewrite app_comm_cons. replace (t2 ++ h1 :: t1) with ((t2 ++ [h1]) ++ t1).
    apply Perm_app_r. apply Perm_cons_append.
    rewrite <- app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Perm_cons_app :
  forall (A : Type) (l l1 l2 : list A) (x : A),
    Perm l (l1 ++ l2) -> Perm (x :: l) (l1 ++ x :: l2).
(* begin hide *)
Proof.
  intros. rewrite H, <- (Perm_app_comm (x :: l2)). cbn.
  apply Perm_skip, Perm_app_comm.
Qed.
(* end hide *)

Lemma Perm_middle :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Perm (l1 ++ x :: l2) (x :: (l1 ++ l2)).
(* begin hide *)
Proof.
  intros. symmetry. apply Perm_cons_app. reflexivity.
Qed.
(* end hide *)

Lemma Perm_rev :
  forall (A : Type) (l : list A),
    Perm (rev l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite Perm_app_com. cbn. apply Perm_skip. assumption.
Qed.
(* end hide *)

Instance Perm_rev' :
  forall A : Type,
    Proper (@Perm A ==> @Perm A) (@rev A).
(* begin hide *)
Proof.
  unfold Proper, respectful; intros.
  rewrite ?Perm_rev. assumption.
Qed.
(* end hide *)

Lemma Perm_length' :
  forall A : Type,
    Proper (@Perm A ==> eq) (@length A).
(* begin hide *)
Proof.
  unfold Proper, respectful; intros.
  apply Perm_length. assumption.
Qed.
(* end hide *)

Lemma Perm_nil_app_cons :
  forall (A : Type) (l l' : list A) (x : A),
    ~ Perm [] (l ++ x :: l').
(* begin hide *)
Proof.
  intros; intro.
  rewrite Perm_middle in H.
  apply Perm_nil_cons in H. assumption.
Qed.
(* end hide *)

Lemma Perm_cons_split :
  forall (A : Type) (h : A) (t l : list A),
    Perm (h :: t) l ->
      exists l1 l2 : list A,
        l = l1 ++ h :: l2 /\ Perm (l1 ++ l2) t.
(* begin hide *)
Proof.
  inversion 1; subst.
    apply Swap_cons in H0. destruct H0 as (l1 & l2 & H0); subst.
      exists l1, l2. cbn.
    apply Swap_cons in H0. destruct H0 as [l1 [l3 H0]]; subst.
      inversion H1; subst.
      

  intros. remember (h :: t) as l'.
  generalize dependent t; generalize dependent h.
  induction H; intros; inversion Heql'; subst.
    inversion H; subst; clear H.
      exists [], l'. cbn. reflexivity.
      exists [x], l. cbn. reflexivity.
    apply Swap_cons in H. destruct H as [l1' [l3' H]]. subst.
      destruct l1' as [| h' t']; cbn in *.
        destruct (IHPerm _ _ eq_refl) as (l1 & l2 & IH); subst.
          exists l1, l2. reflexivity.
        destruct (IHPerm _ _ eq_refl) as (l1 & l2 & IH); subst.
      
Admitted.

Lemma Perm_cons_inv :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Perm (x :: l1) (x :: l2) -> Perm l1 l2.
(* begin hide *)
Proof.
  intros.
  pose (H' := H).
  apply Perm_cons_split in H'. destruct H' as [l1'' [l3'' H'']].
  apply Perm_cons_split in H. destruct H as [l1' [l3' H']].
  destruct l1' as [| h1' t1']; inversion H'; subst; clear H'.
    destruct l1'' as [| h1'' t1'']; inversion H''; subst; clear H''.

  inversion 1; subst.
    apply Swap_cons_inv in H0. constructor. assumption.
    apply Perm_trans with l3.
      assert (Perm (x :: l1) (x :: l2)).
        apply perm_trans_l with l3; assumption.
Restart.
  intros. remember (x :: l1) as l1'. remember (x :: l2) as l2'.
  generalize dependent l1; generalize dependent l2.
  generalize dependent x.
  induction H; intros; subst.
    apply Swap_cons_inv in H. constructor. assumption.
    inversion H; subst; clear H.
      eapply IHPerm; eauto.
Restart.
  induction l1 as [| h1 t1].
    destruct l2 as [| h2 t2]; intros.
      reflexivity.
      apply Perm_length in H. inversion H.
    destruct l2 as [| h2 t2]; intros.
      apply Perm_length in H. inversion H.
      

; destruct l' as [| h' t']; cbn; intros.
    trivial.
    apply Perm_length in H. inversion H.
    apply Perm_length in H. inversion H.
Admitted.

Lemma Perm_app_inv :
  forall (A : Type) (l1 l2 l3 l4 : list A) (x : A),
    Perm (l1 ++ x :: l2) (l3 ++ x :: l4) ->
    Perm (l1 ++ l2) (l3 ++ l4).
(* begin hide *)
Proof.
  intros. rewrite <- ?Perm_middle in H.
  apply Perm_cons_inv in H. assumption.
Qed.
(* end hide *)

Lemma Perm_cons_app_inv :
  forall (A : Type) (l l1 l2 : list A) (x : A),
    Perm (x :: l) (l1 ++ x :: l2) -> Perm l (l1 ++ l2).
(* begin hide *)
Proof.
  intros. rewrite <- Perm_middle in H.
  apply Perm_cons_inv in H. assumption.
Qed.
(* end hide *)

Lemma Perm_app_inv_l :
  forall (A : Type) (l l1 l2 : list A),
    Perm (l ++ l1) (l ++ l2) -> Perm l1 l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    apply IHt. eapply Perm_cons_inv. eassumption.
Qed.
(* end hide *)

Lemma Perm_app_inv_r :
  forall (A : Type) (l l1 l2 : list A),
    Perm (l1 ++ l) (l2 ++ l) -> Perm l1 l2.
(* begin hide *)
Proof.
  intros.
  rewrite (Perm_app_comm l1 l) in H.
  rewrite (Perm_app_comm l2 l) in H.
  eapply Perm_app_inv_l. eassumption.
Qed.
(* end hide *)

Perm_length_1_inv:
  forall (A : Type) (a : A) (l : list A),
  Perm (a :: nil) l -> l = (a :: nil)%list
Perm_length_2_inv:
  forall (A : Type) (a1 a2 : A) (l : list A),
  Perm (a1 :: (a2 :: nil)%list) l ->
  l = (a1 :: a2 :: nil)%list \/ l = (a2 :: a1 :: nil)%list
Perm_length_2:
  forall (A : Type) (a1 a2 b1 b2 : A),
  Perm (a1 :: (a2 :: nil)%list) (b1 :: (b2 :: nil)%list) ->
  a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1
NoDup_Perm:
  forall (A : Type) (l l' : list A),
  List.NoDup l ->
  List.NoDup l' ->
  (forall x : A, List.In x l <-> List.In x l') -> Perm l l'
NoDup_Perm_bis:
  forall (A : Type) (l l' : list A),
  List.NoDup l ->
  List.NoDup l' ->
  length l' <= length l -> List.incl l l' -> Perm l l'
Perm_NoDup:
  forall (A : Type) (l l' : list A),
  Perm l l' -> List.NoDup l -> List.NoDup l'
Perm_NoDup':
  forall A : Type,
  Morphisms.Proper (Morphisms.respectful (Perm (A:=A)) iff)
    (List.NoDup (A:=A))
Perm_map:
  forall (A B : Type) (f : A -> B) (l l' : list A),
  Perm l l' -> Perm (List.map f l) (List.map f l')
Perm_map':
  forall (A B : Type) (f : A -> B),
  Morphisms.Proper
    (Morphisms.respectful (Perm (A:=A)) (Perm (A:=B)))
    (List.map f)
nat_bijection_Perm:
  forall (n : nat) (f : nat -> nat),
  FinFun.bFun n f ->
  FinFun.Injective f -> let l := List.seq 0 n in Perm (List.map f l) l
Perm_nth_error:
  forall (A : Type) (l l' : list A),
  Perm l l' <->
  length l = length l' /\
  (exists f : nat -> nat,
     FinFun.Injective f /\
     (forall n : nat, List.nth_error l' n = List.nth_error l (f n)))
Perm_nth_error_bis:
  forall (A : Type) (l l' : list A),
  Perm l l' <->
  (exists f : nat -> nat,
     FinFun.Injective f /\
     FinFun.bFun (length l) f /\
     (forall n : nat, List.nth_error l' n = List.nth_error l (f n)))
Perm_nth:
  forall (A : Type) (l l' : list A) (d : A),
  Perm l l' <->
  (let n := length l in
   length l' = n /\
   (exists f : nat -> nat,
      FinFun.bFun n f /\
      FinFun.bInjective n f /\
      (forall x : nat, x < n -> List.nth x l' d = List.nth (f x) l d)))

Lemma Swap_spec :
  forall (A : Type) (l1 l2 : list A),
    Swap l1 l2 ->
      length l1 <= 1 /\ length l2 <= 1 \/
      exists (x y : A) (l1' l2' : list A),
        l1 = l1' ++ x :: y :: l2' /\
        l2 = l1' ++ y :: x :: l2'.
(* begin hide *)
Proof.
  induction 1; cbn.
    left. split; apply le_0_n.
    decompose [and or] IHSwap; clear IHSwap; subst.
      destruct l, l'; cbn. Require Import Omega.
        left; omega.
        
    




