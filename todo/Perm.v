Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.

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

Lemma Permutation_length :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> length l1 = length l2.
(* begin hide *)
Proof.
  induction 1; cbn; congruence.
Qed.
(* end hide *)

Lemma Permutation_nil :
  forall (A : Type) (l : list A),
    Permutation [] l -> l = [].
(* begin hide *)
Proof.
  intros. apply Permutation_length in H. cbn in H.
  destruct l; inversion H. trivial.
Qed.
(* end hide *)

Lemma Permutation_length_1:
  forall (A : Type) (l1 l2 : list A),
    length l1 = 1 -> Permutation l1 l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction 2; cbn in *.
    reflexivity.
    destruct l, l'; cbn in *.
      reflexivity.
      apply Permutation_nil in H0. inversion H0.
      inversion H.
      inversion H.
    inversion H.
    rewrite IHPermutation1, IHPermutation2.
      reflexivity.
      apply Permutation_length in H0_. rewrite <- H0_. assumption.
      assumption.
Qed.
(* end hide *)

Lemma Permutation_singl :
  forall (A : Type) (a b : A),
    Permutation [a] [b] -> a = b.
(* begin hide *)
Proof.
  intros. apply Permutation_length_1 in H.
    inversion H. reflexivity.
    cbn. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_nil_cons :
  forall (A : Type) (l : list A) (x : A),
    ~ Permutation [] (x :: l).
(* begin hide *)
Proof.
  intros; intro. apply Permutation_nil in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_refl :
  forall (A : Type) (l : list A),
    Permutation l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; auto.
Defined.
(* end hide *)

Lemma Permutation_trans :
  forall (A : Type) (l l' l'' : list A),
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.
(* begin hide *)
Proof.
  intros. eapply perm_trans; eauto.
Qed.
(* end hide *)

Lemma Permutation_sym :
  forall (A : Type) (l l' : list A), Permutation l l' -> Permutation l' l.
(* begin hide *)
Proof.
  induction 1; auto. eapply Permutation_trans; eauto.
Qed.
(* end hide *)

Instance Permutation_Equivalence:
  forall A : Type, RelationClasses.Equivalence (Permutation (A := A)).
(* begin hide *)
Proof.
  split; red.
    apply Permutation_refl.
    apply Permutation_sym.
    apply Permutation_trans.
Defined.
(* end hide *)

Instance Permutation_cons :
  forall A : Type,
    Proper (eq ==> @Permutation A ==> @Permutation A) (@cons A).
(* begin hide *)
Proof.
  unfold Proper, respectful. intros; subst; auto.
Defined.
(* end hide *)

Lemma Permutation_in :
  forall (A : Type) (l l' : list A) (x : A),
    Permutation l l' -> In x l -> In x l'.
(* begin hide *)
Proof.
  induction 1; intros; cbn; auto.
    inversion H0; auto.
    inversion H; auto. inversion H0; auto.
Qed.
(* end hide *)

Lemma Permutation_in' :
  forall A : Type,
    Proper (eq ==> @Permutation A ==> iff) (@In A).
(* begin hide*)
Proof.
  unfold Proper, respectful; intros.
  subst. split; intro H; eapply Permutation_in; eauto.
  symmetry. assumption.
Qed.
(* end hide *)

Lemma Permutation_app_head :
  forall (A : Type) (l tl tl' : list A),
    Permutation tl tl' -> Permutation (l ++ tl) (l ++ tl').
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; auto.
Qed.
(* end hide *)

Hint Resolve Permutation_refl.

Lemma Permutation_app_tail :
  forall (A : Type) (l l' tl : list A),
    Permutation l l' -> Permutation (l ++ tl) (l' ++ tl).
(* begin hide *)
Proof.
  induction 1; cbn; intros; eauto.
Qed.
(* end hide *)

Lemma Permutation_app :
  forall (A : Type) (l m l' m' : list A),
    Permutation l l' -> Permutation m m' -> Permutation (l ++ m) (l' ++ m').
(* begin hide *)
Proof.
  unfold Proper, respectful.
  intros A l m l' m' H. generalize dependent m'; generalize dependent m.
  induction H; cbn; intros; eauto.
  eapply perm_trans.
    apply perm_swap.
    do 2 constructor. apply Permutation_app_head. trivial.
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

Lemma Permutation_add_inside :
  forall (A : Type) (x : A) (l1 l2 l1' l2' : list A),
    Permutation l1 l1' -> Permutation l2 l2' ->
    Permutation (l1 ++ x :: l2) (l1' ++ x :: l2').
(* begin hide *)
Proof.
  intros. rewrite H, H0. trivial.
Qed.
(* end hide *)

Lemma Permutation_cons_append :
  forall (A : Type) (l : list A) (x : A),
    Permutation (x :: l) (l ++ [x]).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; auto.
  eapply perm_trans.
    apply perm_swap.
    constructor. apply IHt.
Qed.
(* end hide *)

Lemma Permutation_app_comm :
  forall (A : Type) (l l' : list A),
    Permutation (l ++ l') (l' ++ l).
(* begin hide *)
Proof.
  induction l as [| h t]; destruct l' as [| h' t'];
  cbn; rewrite ?app_nil_r; auto.
  rewrite IHt. cbn. rewrite perm_swap. constructor.
  change (h :: t' ++ t) with ((h :: t') ++ t).
    replace (t' ++ h :: t) with ((t' ++ [h]) ++ t).
      apply Permutation_app_tail. apply Permutation_cons_append.
      rewrite <- app_assoc. cbn. trivial.
Qed.
(* end hide *)

Lemma Permutation_cons_app :
  forall (A : Type) (l l1 l2 : list A) (x : A),
    Permutation l (l1 ++ l2) -> Permutation (x :: l) (l1 ++ x :: l2).
(* begin hide *)
Proof.
  intros. rewrite H, <- (Permutation_app_comm (x :: l2)). cbn.
  constructor. apply Permutation_app_comm.
Qed.
(* end hide *)

Lemma Permutation_middle :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Permutation (l1 ++ x :: l2) (x :: (l1 ++ l2)).
(* begin hide *)
Proof.
  intros. symmetry. apply Permutation_cons_app. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_rev :
  forall (A : Type) (l : list A),
    Permutation (rev l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; trivial.
  rewrite <- Permutation_cons_app.
    reflexivity.
    rewrite app_nil_r, IHt. reflexivity.
Qed.
(* end hide *)

Instance Permutation_rev' :
  forall A : Type,
    Proper (@Permutation A ==> @Permutation A) (@rev A).
(* begin hide *)
Proof.
  unfold Proper, respectful; intros.
  rewrite ?Permutation_rev. assumption.
Qed.
(* end hide *)

Lemma Permutation_length' :
  forall A : Type,
    Proper (@Permutation A ==> eq) (@length A).
(* begin hide *)
Proof.
  unfold Proper, respectful; intros.
  apply Permutation_length. assumption.
Qed.
(* end hide *)

(*Fixpoint Permutation_ind_bis
  (A : Type) (P : list A -> list A -> Prop)
  (Hnil : P [] [])
  (Hskip : forall (x : A) (l l' : list A),
   Permutation l l' -> P l l' -> P (x :: l) (x :: l'))
  (Hswap : forall (x y : A) (l l' : list A),
   Permutation l l' -> P l l' -> P (y :: x :: l) (x :: y :: l'))
  (Htrans : forall l l' l'' : list A,
   Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'')
  (l l' : list A) (H : Permutation l l') : P l l'.
(* begin hide *)
Proof.
  destruct H.
    apply Hnil.
    apply Hskip.
      assumption.
      apply Permutation_ind_bis; auto.
    Focus 2. apply Htrans with l'; try assumption.
      apply Permutation_ind_bis; auto.
      apply Permutation_ind_bis; auto.
    apply Hswap.
      reflexivity.
      apply Permutation_ind_bis. 1-4: auto. reflexivity.
Defined.*)

Lemma Permutation_nil_app_cons :
  forall (A : Type) (l l' : list A) (x : A),
    ~ Permutation [] (l ++ x :: l').
(* begin hide *)
Proof.
  intros; intro.
  rewrite Permutation_middle in H.
  apply Permutation_nil_cons in H. assumption.
Qed.
(* end hide *)

Ltac inv H := inversion H; subst; clear H.

Lemma Permutation_cons_split :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
    l1 = [] /\ l2 = [] \/
    exists (h1 h2 : A) (t1 t2 l11 l12 l21 l22 : list A),
      l1 = h1 :: t1 /\
      l2 = h2 :: t2 /\
      l1 = l11 ++ h1 :: l12 /\
      l2 = l21 ++ h2 :: l22 /\
      Permutation t1 (l11 ++ l12) /\
      Permutation t2 (l21 ++ l22).
(* begin hide *)
Proof.
  induction 1.
    left. split; trivial.
    destruct IHPermutation as
        [[] | (h1 & h2 & t1 & t2 & l11 & l12 & l21 & l22 &
               H1 & H2 & H3 & H4 & H5 & H6)]; subst.
      right. exists x, x, [], [], [], [], [], []. firstorder.
      right. exists x, x, (h1 :: t1), (h2 :: t2), [], (h1 :: t1), [], (h2 :: t2).
        cbn. firstorder.
    right. exists y, x, (x :: l), (y :: l), [], (x :: l), [], (y :: l).
      cbn. firstorder.
    destruct
      IHPermutation1 as
        [[] | (h1 & h2 & t1 & t2 & l11 & l12 & l21 & l22 &
               H1 & H2 & H3 & H4 & H5 & H6)],
      IHPermutation2 as
        [[] | (h1' & h2' & t1' & t2' & l11' & l12' & l21' & l22' &
               H1' & H2' & H3' & H4' & H5' & H6')];
    subst.
      left. split; trivial.
      inversion H1'.
      inversion H7.
      inv H1'. right.
        exists h1, h2', t1, t2', [], t1, [], t2'. cbn. firstorder.
Qed.
(* end hide *)

Lemma app_lemma :
  forall (A : Type) (x y : A) (l11 l12 l21 l22 : list A),
    l11 ++ x :: l12 = l21 ++ y :: l22 ->
      l11 = l21 /\ x = y /\ l12 = l22 \/
      exists l1 l2 l3 : list A,
        (l11 ++ x :: l12 = l1 ++ x :: l2 ++ y :: l3 /\
         l21 ++ y :: l22 = l1 ++ x :: l2 ++ y :: l3)
        \/
        (l11 ++ x :: l12 = l1 ++ y :: l2 ++ x :: l3 /\
         l21 ++ y :: l22 = l1 ++ y :: l2 ++ x :: l3).
(* begin hide *)
Proof.
  induction l11 as [| h t]; cbn.
    destruct l21 as [| h' t']; cbn; intros; inv H.
      left. repeat constructor.
      right. exists [], t', l22; cbn. left. split; reflexivity.
    destruct l21 as [| h' t']; cbn; intros; inv H.
      right. exists [], t, l12; cbn. right. split; reflexivity.
      decompose [and or ex] (IHt _ _ _ H2); clear IHt; subst.
        left. repeat constructor.
        right. rewrite ?H0, ?H1, ?IH2 in *.
          exists (h' :: x0), x1, x2; cbn. left. split; reflexivity.
        right. rewrite ?H0, ?H1, ?IH2 in *.
          exists (h' :: x0), x1, x2; cbn. right. split; reflexivity.
Qed.
(* end hide *)

Lemma app_lemma' :
  forall (A : Type) (x y : A) (l11 l12 l21 l22 : list A),
    l11 ++ x :: l12 = l21 ++ y :: l22 ->
      l11 = l21 /\ x = y /\ l12 = l22 \/
      exists l1 l2 l3 : list A,
        (l11 = l1 /\ l12 = l2 ++ y :: l3 /\
         l21 = l1 ++ x :: l2 /\ l22 = l3)
        \/
        (l11 = l1 ++ y :: l2 /\ l12 = l3 /\
         l21 = l1 /\ l22 = l2 ++ x :: l3).
(* begin hide *)
Proof.
  induction l11 as [| h t]; cbn.
    destruct l21 as [| h' t']; cbn; intros; inv H.
      left. firstorder.
      right. exists [], t', l22. left. firstorder.
    destruct l21 as [| h' t']; cbn; intros; inv H.
      right. exists [], t, l12. right. firstorder.
      destruct (IHt _ _ _ H2) as
        [(IH1 & IH2 & IH3) | (l1 & l2 & l3 &
          [(IH1 & IH2 & IH3 & IH4) | (IH1 & IH2 & IH3 & IH4)])];
      clear IHt; subst.
        left. firstorder.
        right. exists (h' :: l1), l2, l3. left. firstorder.
        right. exists (h' :: l1), l2, l3. right. firstorder.
Qed.
(* end hide *)


Lemma app_lemma'' :
  forall (A : Type) (x y : A) (l11 l12 l21 l22 : list A),
    l11 ++ x :: l12 = l21 ++ y :: l22 ->
      l11 = l21 /\ x = y /\ l12 = l22 \/
      exists l1 l2 l3 : list A,
        (l11 ++ x :: l12 = l1 ++ x :: l2 ++ y :: l3 /\
         l21 ++ y :: l22 = l1 ++ x :: l2 ++ y :: l3
        /\
         l11 = l1 /\ l12 = l2 ++ y :: l3 /\
         l21 = l1 ++ x :: l2 /\ l22 = l3)
        \/
        (l11 ++ x :: l12 = l1 ++ y :: l2 ++ x :: l3 /\
         l21 ++ y :: l22 = l1 ++ y :: l2 ++ x :: l3
        /\
         l11 = l1 ++ y :: l2 /\ l12 = l3 /\
         l21 = l1 /\ l22 = l2 ++ x :: l3).
(* begin hide *)
Proof.
  induction l11 as [| h t]; cbn.
    destruct l21 as [| h' t']; cbn; intros; inv H.
      left. firstorder.
      right. exists [], t', l22. left. firstorder.
    destruct l21 as [| h' t']; cbn; intros; inv H.
      right. exists [], t, l12. right. firstorder.
      destruct (IHt _ _ _ H2) as
        [(IH1 & IH2 & IH3) | (l1 & l2 & l3 &
          [(IH1 & IH2 & IH3 & IH4) | (IH1 & IH2 & IH3 & IH4)])];
      clear IHt; subst.
        left. firstorder.
        right. rewrite ?IH1, ?IH2, ?IH4 in *.
          eexists (h' :: l1), l2, l3. left. firstorder.
            subst. reflexivity.
        right. rewrite ?IH1, ?IH2, ?IH4 in *.
          eexists (h' :: l1), l2, l3. right. firstorder.
            subst. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_cons_split' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
    l1 = [] /\ l2 = [] \/
    exists (x : A) (l11 l12 l21 l22 : list A),
      l1 = l11 ++ x :: l12 /\
      l2 = l21 ++ x :: l22 /\
      Permutation (l11 ++ l12) (l21 ++ l22).
(* begin hide *)
Proof.
  induction 1.
    left. split; reflexivity.
    destruct IHPermutation as
        [[] | (h & l11 & l12 & l21 & l22 & IH1 & IH2 & IH3)].
      right. subst. exists x, [], [], [], []. cbn. firstorder.
      right. exists h, (x :: l11), l12, (x :: l21), l22. cbn.
        rewrite IH1, IH2. firstorder.
    right. exists x, [y], l, [], (y :: l). cbn. firstorder.
    destruct
      IHPermutation1 as
        [[] | (x & l11 & l12 & l21 & l22 & IH1 & IH2 & IH3)],
      IHPermutation2 as
        [[] | (x' & l11' & l12' & l21' & l22' & IH1' & IH2' & IH3')];
    subst.
      left. split; reflexivity.
      apply (f_equal length) in IH1'. rewrite length_app in IH1'.
        cbn in *. rewrite <- plus_n_Sm in IH1'. inversion IH1'.
      apply (f_equal length) in H1. rewrite length_app in H1.
        cbn in *. rewrite <- plus_n_Sm in H1. inversion H1.
Admitted.
(* end hide *)


Lemma Permutation_cons_inv :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Permutation (x :: l1) (x :: l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros. pose (H' := H).
  apply Permutation_cons_split in H'.
  destruct H' as [[] | (h1 & h2 & t1 & t2 & l11 & l12 & l21 & l22
      & H1 & H2 & H3 & H4 & H5 & H6)].
    inv H0.
    inv H1; inv H2. rewrite H3, H4 in *.
Restart.
  intros. remember (x :: l1) as l1'; remember (x :: l2) as l2'.
  revert x l1 l2 Heql1' Heql2'.
  induction H; intros; try inv Heql1'; try inv Heql2'.
    assumption.
    reflexivity.
    destruct l as [| h1 t1].
      inv Heql1'.
      destruct l'' as [| h3 t3].
        inv Heql2'.
        inv Heql1'. inv Heql2'. destruct l' as [| h2 t2].
          symmetry in H. apply Permutation_nil_cons in H. contradiction.
Restart.
  intros.
    
  
Admitted.



Lemma Permutation_In :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 <-> (forall x : A, In x l1 <-> In x l2).
(* begin hide *)
Proof.
  split; intros.
    induction H; cbn; firstorder.
    revert l2 H.
    induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; intros.
      reflexivity.
      specialize (H h2). firstorder.
      specialize (H h1). firstorder.
      rewrite <- ?In_elem in *. assert (h1 = h1 \/ In h1 t1).
        left. reflexivity.
        rewrite H in H0. destruct H0.
          subst. constructor. apply IHt1. split; intro.
            rewrite In_elem in H0. induction H0.
              specialize (H x).
      
Qed.
(* end hide *)

Lemma Permutation_app_inv :
  forall (A : Type) (l1 l2 l3 l4 : list A) (x : A),
    Permutation (l1 ++ x :: l2) (l3 ++ x :: l4) ->
    Permutation (l1 ++ l2) (l3 ++ l4).
(* begin hide *)
Proof.
  intros. rewrite <- ?Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
(* end hide *)

Lemma Permutation_cons_app_inv :
  forall (A : Type) (l l1 l2 : list A) (x : A),
    Permutation (x :: l) (l1 ++ x :: l2) -> Permutation l (l1 ++ l2).
(* begin hide *)
Proof.
  intros. rewrite <- Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
(* end hide *)

Lemma Permutation_app_inv_l :
  forall (A : Type) (l l1 l2 : list A),
    Permutation (l ++ l1) (l ++ l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    apply IHt. eapply Permutation_cons_inv. eassumption.
Qed.
(* end hide *)

Lemma Permutation_app_inv_r :
  forall (A : Type) (l l1 l2 : list A),
    Permutation (l1 ++ l) (l2 ++ l) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros.
  rewrite (Permutation_app_comm l1 l) in H.
  rewrite (Permutation_app_comm l2 l) in H.
  eapply Permutation_app_inv_l. eassumption.
Qed.
(* end hide *)

Permutation_length_1_inv:
  forall (A : Type) (a : A) (l : list A),
  Permutation (a :: nil) l -> l = (a :: nil)%list
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