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

(*Lemma Permutation_cons_split :
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
      right. exists x, x, (h1 :: t1), (h2 :: t2), [], (h1 :: t1), [],
(h2 :: t2).
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
*)

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
    (forall x y l l', Permutation l l' -> P l l' ->
      P (y :: x :: l) (x :: y :: l')) ->
    (forall l l' l'', Permutation l l' -> P l l' -> Permutation l' l'' ->
      P l' l'' -> P l l'') ->
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

Lemma Permutation_antispec :
  ~ forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 <->
    (forall P : A -> Prop, Exists P l1 <-> Exists P l2).
(* begin hide *)
Proof.
  intro. specialize (H unit [tt] [tt; tt]).
  assert (forall P : unit -> Prop, Exists P [tt] <-> Exists P [tt; tt]).
    split; intro.
      inversion H0; subst.
        repeat constructor. assumption.
        inversion H2.
      inversion H0; subst.
        constructor. assumption.
        assumption.
    rewrite <- H in H0. apply Permutation_length in H0.
      cbn in H0. inversion H0.
Qed.
(* end hide *)

Lemma Permutation_length_1_inv:
  forall (A : Type) (x : A) (l : list A),
    Permutation [x] l -> l = [x].
(* begin hide *)
Proof.
  destruct l as [| y [| z t]]; intros.
    symmetry in H. apply Permutation_nil in H. inversion H.
    apply Permutation_singl in H. rewrite H. reflexivity.
    apply Permutation_length in H. cbn in H. inversion H.
Qed.
(* end hide *)

(*Lemma Elem_Permutation' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation l1 l2 -> elem x l1 ->
      exists l21 l22 : list A, l2 = l21 ++ x :: l22.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inversion H.
    inversion H0; subst.
      exists [], l'. reflexivity.
      destruct (IHPermutation H3) as (l21 & l22 & IH); subst.
        exists (x0 :: l21), l22. cbn. reflexivity.
      inversion H; subst.
        exists [x0], l. reflexivity.
        inversion H2; subst.
          exists [], (y :: l). reflexivity.
          clear H H2. induction H3.
            exists [x0; y], l. reflexivity.
            destruct IHelem as (l21 & l22 & IH).
              destruct l21 as [| a [| b l21']]; inversion IH; subst.
                exists [], (y :: h :: t). reflexivity.
                exists [a], (h :: l22). reflexivity.
                exists (a :: b :: h :: l21'), l22. reflexivity.
      destruct (IHPermutation1 H1) as (l21 & l22 & IH1). subst.
        destruct l''.
          admit.
*)

Lemma Permutation_length_2_inv:
  forall (A : Type) (x y : A) (l : list A),
    Permutation [x; y] l -> l = [x; y] \/ l = [y; x].
(* begin hide *)
Proof.
  intros.
  pose (H' := @Permutation_length _ _ _ H).
  destruct l as [| a [| b [| c t]]]; inversion H'.
    inversion H; subst.
      admit.
      admit.
Admitted.
(* end hide *)

Lemma Permutation_length_2:
  forall (A : Type) (x1 x2 y1 y2 : A),
    Permutation [x1; x2] [y1; y2] ->
      x1 = y1 /\ x2 = y2 \/ x1 = y2 /\ x2 = y1.
(* begin hide *)
Proof.
  intros. apply Permutation_length_2_inv in H.
  destruct H; inversion H; subst.
    left. split; reflexivity.
    right. split; reflexivity.
Qed.
(* end hide *)

Lemma NoDup_Permutation:
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 -> NoDup l2 ->
      (forall x : A, In x l1 <-> In x l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    inversion H0; subst.
      reflexivity.
      assert False.
        rewrite (H1 h). left. reflexivity.
        contradiction.
    destruct l2 as [| h2 t2]; cbn; intros.
      specialize (H1 h1). destruct H1. destruct H1. left. reflexivity.
      inversion H; inversion H0; subst; clear H H0.
        destruct (H1 h1). destruct H.
          left. reflexivity.
          subst. constructor. apply IHt1.
            1-2: assumption.
            split; intro.
              assert (In x (h2 :: t2)).
                rewrite <- H1. right. assumption.
                destruct H2.
                  subst. rewrite In_elem in *. contradiction.
                  assumption.
              assert (In x (h2 :: t1)).
                cbn. rewrite H1. right. assumption.
                destruct H2; subst.
                  rewrite In_elem in *. contradiction.
                  assumption.
          apply In_spec in H. destruct H as (l1 & l2 & HIn); subst.
            rewrite Permutation_middle. rewrite perm_swap. constructor.
            apply IHt1.
              assumption.
              constructor.
                intro. apply H8. apply elem_app_or in H.
                  apply elem_or_app. destruct H.
                    left. assumption.
                    do 2 right. assumption.
                rewrite NoDup_app_comm in H9. inversion H9.
                  rewrite NoDup_app_comm. assumption.
              split; intro.
                assert (In x (h2 :: l1 ++ h1 :: l2)).
                  rewrite <- H1. right. assumption.
                  inversion H2; subst.
                    left. reflexivity.
                    apply In_app_or in H3. destruct H3.
                      right. apply In_or_app. left. assumption.
                      inversion H3; subst.
                        rewrite In_elem in *. contradiction.
                        right. apply In_or_app. right. assumption.
                assert (In x (h2 :: l1 ++ h1 :: l2)).
                  cbn in H. destruct H.
                    subst. left. reflexivity.
                    apply In_app_or in H. destruct H.
                      right. apply In_or_app. left. assumption.
                      right. apply In_or_app. do 2 right. assumption.
                  specialize (H1 x). rewrite <- H1 in H2. destruct H2.
                    subst. destruct H.
                      subst. contradiction H8. apply elem_or_app.
                        right. left.
                      apply In_app_or in H. destruct H.
                        rewrite NoDup_app_comm in H9. inversion H9.
                          subst. contradiction H6. apply elem_or_app.
                            right. rewrite <- In_elem. assumption.
                        rewrite NoDup_app_comm in H9. inversion H9.
                          subst. contradiction H6. apply elem_or_app.
                            left. rewrite <- In_elem. assumption.
                    assumption.
Qed.
(* end hide *)

(*
NoDup_Permutation_bis:
  forall (A : Type) (l l' : list A),
  List.NoDup l ->
  List.NoDup l' ->
  length l' <= length l -> List.incl l l' -> Permutation l l' *)

Lemma Permutation_NoDup:
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> NoDup l1 -> NoDup l2.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    inv H0. constructor.
      rewrite <- In_elem in *. intro. apply H3. eapply Permutation_in.
        symmetry. eassumption.
        assumption.
      apply IHPermutation. assumption.
    inv H. inv H3. constructor.
      intro. inv H.
        apply H2. left.
        contradiction.
      constructor.
        intro. apply H2. right. assumption.
        assumption.
    apply IHPermutation2, IHPermutation1, H1.
Qed.
(* end hide *)

Lemma Permutation_NoDup':
  forall A : Type,
    Morphisms.Proper
      (Morphisms.respectful (Permutation (A:=A)) iff)
      (NoDup (A:=A)).
(* begin hide *)
Proof.
  unfold Proper, respectful. split; intro.
    eapply Permutation_NoDup; eauto.
    eapply Permutation_NoDup.
      symmetry. all: eassumption.
Qed.
(* end hide *)

Lemma Permutation_map:
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; try constructor.
    assumption.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_map':
  forall (A B : Type) (f : A -> B),
  Morphisms.Proper
    (Morphisms.respectful (Permutation (A:=A)) (Permutation (A:=B)))
    (map f).
(* begin hide *)
Proof.
  unfold Proper, respectful. induction 1; cbn; try constructor.
    assumption.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

(** Poważne rzeczy *)

Lemma Permutation_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Permutation l1 l2 -> Permutation (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    apply Permutation_app_head, IHPermutation.
    rewrite Permutation_app_comm, <- app_assoc.
      apply Permutation_app_head, Permutation_app_comm.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_join_rev :
  exists (A : Type) (l1 l2 : list (list A)),
    Permutation (join l1) (join l2) /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [[]]. cbn. split.
    reflexivity.
    intro. apply Permutation_length in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Permutation (replicate n x) (replicate m x) <-> n = m.
(* begin hide *)
Proof.
  split.
    revert m x. induction n as [| n']; cbn; intros.
      apply Permutation_length in H. destruct m; inversion H. reflexivity.
      destruct m as [| m'].
        apply Permutation_length in H; cbn in H. inv H.
        apply f_equal, (IHn' m' x), Permutation_cons_inv with x, H.
    intros ->. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_replicate' :
  forall (A : Type) (n : nat) (x y : A),
    Permutation (replicate n x) (replicate n y) <-> n = 0 \/ x = y.
(* begin hide *)
Proof.
  split.
    revert x y. induction n as [| n']; cbn; intros.
      left. reflexivity.
      right. pose (H' := @Permutation_in A _ _ x H ltac:(left; reflexivity)).
        inv H'. reflexivity.
        apply In_replicate in H0. destruct H0. symmetry. assumption.
    destruct 1; rewrite H; reflexivity.
Qed.
(* end hide *)

Lemma Permutation_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Permutation (iterate f n x) (iterate f m x) <-> n = m.
(* begin hide *)
Proof.
  split.
    revert f m x. induction n as [| n']; cbn; intros.
      apply Permutation_length in H. destruct m; inversion H. reflexivity.
      destruct m as [| m'].
        apply Permutation_length in H; cbn in H. inv H.
        apply f_equal, (IHn' f m' (f x)), Permutation_cons_inv with x, H.
    intros ->. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_iterate' :
  forall (A : Type) (f : A -> A) (n : nat) (x y : A),
    Permutation (iterate f n x) (iterate f n y) <->
    n = 0 \/ x = y \/ exists kx ky : nat,
      y = iter f kx x /\
      x = iter f ky y /\
      S (kx + ky) = n.
(* begin hide *)
Proof.
  split.
    revert f x y. induction n as [| n']; cbn; intros.
      left. reflexivity.
      {
        assert (H' := @Permutation_in A _ _ x H ltac:(left; reflexivity)).
        symmetry in H.
        assert (H'' := @Permutation_in A _ _ y H ltac:(left; reflexivity)).
        inv H'; inv H''; try (right; left; reflexivity).
        apply In_iterate in H0. apply In_iterate in H1.
        destruct H0 as (k1 & H11 & H12), H1 as (k2 & H21 & H22).
        right. right. exists (S k2), (S k1). cbn.
Abort.
(* end hide *)

Lemma Permutation_iterate' :
  forall (A : Type) (f : A -> A) (n : nat) (x y : A),
    Permutation (iterate f n x) (iterate f n y) ->
    n = 0 \/ exists k : nat, k < n /\ iter f k y = x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    left. reflexivity.
    right. pose (H' := @Permutation_in A _ _ x H ltac:(left; reflexivity)).
      inv H'. exists 0. split.
        apply le_n_S, le_0_n.
        cbn. reflexivity.
      apply In_iterate in H0. destruct H0 as (k & H1 & H2).
        exists (S k). split.
          apply lt_n_S. assumption.
          cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Permutation_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    Permutation (insert l n x) (x :: l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite perm_swap. constructor. apply IHt.
Qed.
(* end hide *)

Lemma Permutation_take :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\
      exists n : nat, ~ Permutation (take n l1) (take n l2).
(* begin hide *)
Proof.
  exists bool, [true; false], [false; true]. split.
    constructor.
    exists 1. cbn. intro. apply Permutation_length_1 in H.
      congruence.
      reflexivity.
Qed.
(* end hide *)

Lemma Permutation_drop :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\
      exists n : nat, ~ Permutation (drop n l1) (drop n l2).
(* begin hide *)
Proof.
  exists bool, [true; false], [false; true]. split.
    constructor.
    exists 1. cbn. intro. apply Permutation_length_1 in H.
      congruence.
      reflexivity.
Qed.
(* end hide *)

Lemma Permutation_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Permutation la1 la2 /\ Permutation lb1 lb2 /\
      ~ Permutation (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists bool, bool,
    [true; false], [false; true], [false; true; false], [false; false; true].
  repeat split.
    apply perm_swap.
    do 2 constructor.
    cbn. intro. apply Permutation_length_2 in H. firstorder congruence.
Qed.
(* end hide *)

Lemma zipWith_pair :
  forall (A B : Type) (la : list A) (lb : list B),
    zipWith pair la lb = zip la lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn; intros.
      reflexivity.
      rewrite IHta. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_zipWith :
  exists
    (A B C : Type) (f : A -> B -> C)
    (la1 la2 : list A) (lb1 lb2 : list B),
      Permutation la1 la2 /\
      Permutation lb1 lb2 /\
      ~ Permutation (zipWith f la1 lb1) (zipWith f la2 lb2).
(* begin hide *)
Proof.
  destruct (Permutation_zip)
    as (A & B & la1 & la2 & lb1 & lb2 & H1 & H2 & H3).
  exists A, B, _, pair, la1, la2, lb1, lb2. repeat split.
    1-2: assumption.
    rewrite ?zipWith_pair. assumption.
Qed.
(* end hide *)

Lemma Permutation_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1; cbn; try destruct (p x); try destruct (p y); congruence.
Qed.
(* end hide *)

Lemma Permutation_count_conv :
  forall (A : Type) (l1 l2 : list A),
    (forall p : A -> bool, count p l1 = count p l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  
Admitted.
(* end hide *)

Lemma Permutation_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    destruct (p x); rewrite IHPermutation; reflexivity.
    destruct (p x), (p y); try constructor; reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    destruct (f x); rewrite IHPermutation; reflexivity.
    destruct (f x), (f y); try constructor; reflexivity.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_intersperse :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Permutation l1 l2 -> Permutation (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    destruct (intersperse x l), (intersperse x l').
      reflexivity.
      1-2: apply Permutation_length in IHPermutation; inv IHPermutation.
      do 2 constructor. assumption.
    destruct (intersperse x l).
      rewrite Permutation_cons_append. constructor.
      change _ with
        (Permutation
          ([y; x; x0] ++ (x :: a :: l0))
          ([x0; x; y] ++ (x :: a :: l0))).
        apply Permutation_app_tail.
          rewrite Permutation_cons_append, perm_swap. reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Print unzip.



(* TODO: 

nth

remove

splitAt

unzip

unzipWith
head, tail i uncons
last, init i unsnoc *)