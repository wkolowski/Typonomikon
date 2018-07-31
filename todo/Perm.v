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
    Permutation l l' -> Permutation m m' ->
      Permutation (l ++ m) (l' ++ m').
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

Lemma Permutation_In :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> (forall x : A, In x l1 <-> In x l2).
(* begin hide *)
Proof.
  induction 1; cbn; firstorder.
Qed.
(* end hide *)

Lemma Permutation_ind' :
  forall (A : Type) (P : list A -> list A -> Prop),
    P [] [] ->
    (forall x l l', Permutation l l' -> P l l' -> P (x :: l) (x :: l')) ->
    (forall x y l l', Permutation l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
    (forall l l' l'', Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
    forall l l', Permutation l l' -> P l l'.
Proof.
  intros A P Hnil Hskip Hswap Htrans.
  induction 1; auto.
    apply Hswap.
      reflexivity.
      induction l; auto.
    apply Htrans with l'; assumption.
Defined.

Inductive Elem {A : Type} (x : A) : list A -> list A -> Prop :=
    | es_here :
        forall l : list A, Elem x l (x :: l)
    | es_there :
        forall (y : A) (l1 l2 : list A),
          Elem x l1 l2 -> Elem x (y :: l1) (y :: l2).

Lemma Elem_spec :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Elem x l1 l2 -> exists l21 l22 : list A,
      l2 = l21 ++ x :: l22 /\ l1 = l21 ++ l22.
(* begin hide *)
Proof.
  induction 1.
    exists [], l. split; reflexivity.
    destruct IHElem as (l21 & l22 & IH1 & IH2); subst.
      exists (y :: l21), l22. split; reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Elem :
  forall (A : Type) (x : A) (l l' : list A),
    Elem x l l' -> Permutation l' (x :: l).
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    apply perm_trans with (y :: x :: l1); constructor; assumption.
Qed.
(* end hide *)

Lemma Elem_Permutation :
  forall (A : Type) (x : A) (l1 l1' : list A),
    Elem x l1 l1' -> forall l2' : list A,
      Permutation l1' l2' -> exists l2 : list A, Elem x l2 l2'.
(* begin hide *)
Proof.
  intros. revert x l1 H. induction H0; intros.
    inv H.
    inv H.
      eexists. constructor.
      destruct (IHPermutation _ _ H3) as (l2 & IH).
        exists (x :: l2). constructor. assumption.
    inv H.
      eexists. do 2 constructor.
      inv H2.
        eexists. constructor.
        eexists. do 2 constructor. eassumption.
    destruct (IHPermutation1 _ _ H) as (l2 & IH1).
      destruct (IHPermutation2 _ _ IH1) as (l2' & IH2).
        exists l2'. assumption.
Qed.
(* end hide *)

Lemma Permutation_Elems :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> forall (x : A) (l1' l2' : list A),
      Elem x l1' l1 -> Elem x l2' l2 ->
        Permutation l1' l2'.
(* begin hide *)
Proof.
  intro.
  apply (@Permutation_ind' _
    (fun l1 l2 => forall x l1' l2',
      Elem x l1' l1 -> Elem x l2' l2 -> Permutation l1' l2'));
  intros.
    inv H0.
    inv H1; inv H2.
      assumption.
      rewrite H. eapply Permutation_Elem. assumption.
      rewrite <- H. symmetry. apply Permutation_Elem. assumption.
      constructor. eapply H0; eassumption.
    repeat match goal with
        | H : Elem _ _ (_ :: _) |- _ => inv H
        | |- Permutation (?x :: _) (?x :: _) => constructor
        | H : ?G |- ?G => assumption
    end.
      rewrite <- H. symmetry. apply Permutation_Elem. assumption.
      rewrite perm_swap, <- H. constructor. symmetry.
        apply Permutation_Elem. assumption.
      rewrite H. apply Permutation_Elem. assumption.
      rewrite perm_swap, H. constructor. apply Permutation_Elem. assumption.
      rewrite perm_swap. do 2 constructor. eapply H0; eassumption.
    destruct (@Elem_Permutation _ _ _ _ H3 _ H) as (l3 & IH).
      specialize (H0 _ _ _ H3 IH). specialize (H2 _ _ _ IH H4).
      rewrite H0, <- H2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_cons_aux :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation (x :: l1) l2 ->
      exists l21 l22 : list A, l2 = l21 ++ x :: l22.
(* begin hide *)
Proof.
  intros. pose (@Permutation_In _ _ _ H x).
  assert (In x (x :: l1)).
    left. reflexivity.
    rewrite i in H0. apply In_spec. assumption.
Qed.
(* end hide *)

Lemma Permutation_cons_inv :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Permutation (x :: l1) (x :: l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros.
  apply Permutation_Elems with (x := x) (l1 := x :: l1) (l2 := x :: l2).
    assumption.
    1-2: constructor.
Qed.
(* end hide *)

Lemma Permutation_app_inv :
  forall (A : Type) (l1 l2 l3 l4 : list A) (x : A),
    Permutation (l1 ++ x :: l2) (l3 ++ x :: l4) ->
    Permutation (l1 ++ l2) (l3 ++ l4).
(* begin hide *)
Proof.
  intros. rewrite ?Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
(* end hide *)

Lemma Permutation_cons_app_inv :
  forall (A : Type) (l l1 l2 : list A) (x : A),
    Permutation (x :: l) (l1 ++ x :: l2) -> Permutation l (l1 ++ l2).
(* begin hide *)
Proof.
  intros. rewrite Permutation_middle in H.
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

(*Permutation_length_1_inv:
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
*)