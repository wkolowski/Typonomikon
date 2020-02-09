Require Import D5.

Fixpoint list_eq_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
    | [], [] => true
    | [], _ => false
    | _, [] => false
    | h1 :: t1, h2 :: t2 => eq_dec h1 h2 && list_eq_dec eq_dec t1 t2
end.

Lemma list_eq_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (l1 = l2) (list_eq_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
    1-3: constructor; reflexivity + inversion 1.
    destruct (eq_dec_spec h1 h2); cbn.
      destruct (IHt1 t2); constructor.
        f_equal; assumption.
        intro. inv H. contradiction.
      constructor. intro. inv H. contradiction.
Qed.
(* end hide *)

Definition elem_dec
  {A : Type} (eq_dec : A -> A -> bool) (x : A) (l : list A) : bool :=
    any (eq_dec x) l.

Lemma elem_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (x : A) (l : list A),
      reflect (elem x l) (elem_dec eq_dec x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor. inversion 1.
    destruct (eq_dec_spec x h).
      subst. cbn. constructor. left.
      cbn. unfold elem_dec in IHt. destruct IHt; constructor.
        right. assumption.
        intro. apply n0. inv H.
          contradiction.
          assumption.
Qed.
(* end hide *)

Lemma In_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (x : A) (l : list A),
      reflect (In x l) (elem_dec eq_dec x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor. inversion 1.
    destruct (eq_dec_spec x h); cbn.
      constructor. left. assumption.
      unfold elem_dec in IHt. destruct IHt; constructor.
        right. assumption.
        intro. apply n0. inv H.
          contradiction.
          assumption.
Qed.
(* end hide *)

Fixpoint Dup_dec
  {A : Type} (eq_dec : A -> A -> bool) (l : list A) : bool :=
match l with
    | [] => false
    | h :: t => elem_dec eq_dec h t || Dup_dec eq_dec t
end.

Lemma Dup_dec_spec :
  forall
    (A : Type) (eq_dec : A -> A -> bool)
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l : list A),
      reflect (Dup l) (Dup_dec eq_dec l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor. inversion 1.
    destruct (elem_dec_spec eq_dec_spec h t); cbn.
      constructor. left. assumption.
      destruct IHt; constructor.
        right. assumption.
        intro. apply n0. inv H.
          contradiction.
          assumption.
Qed.
(* end hide *)

Lemma Exists_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A),
      reflect (Exists P l) (any p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor. inversion 1.
    destruct (P_dec_spec h); cbn.
      constructor. left. assumption.
      destruct IHt; constructor.
        right. assumption.
        intro. apply n0. inv H.
          contradiction.
          assumption.
Qed.
(* end hide *)

Lemma Forall_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A),
      reflect (Forall P l) (all p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    do 2 constructor.
    destruct (P_dec_spec h); cbn.
      destruct IHt; constructor.
        constructor; assumption.
        intro. apply n. inv H. assumption.
      constructor. intro. inv H. contradiction.
Qed.
(* end hide *)

Definition Exactly_dec
  {A : Type} (p : A -> bool) (n : nat) (l : list A) : bool :=
    count p l =? n.

Lemma Exactly_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A) (n : nat),
      reflect (Exactly P n l) (Exactly_dec p n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; constructor.
      constructor.
      inversion 1.
    destruct (P_dec_spec h).
      destruct n as [| n']; cbn.
        constructor. intro. inv H. contradiction.
        unfold Exactly_dec in IHt. destruct (IHt n'); constructor.
          constructor; assumption.
          intro. inv H; contradiction.
      unfold Exactly_dec in IHt. destruct (IHt n); constructor.
        constructor; assumption.
        intro. inv H; contradiction.
Qed.
(* end hide *)

Definition AtLeast_dec
  {A : Type} (p : A -> bool) (n : nat) (l : list A) : bool :=
    n <=? count p l.

Lemma AtLeast_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A) (n : nat),
      reflect (AtLeast P n l) (AtLeast_dec p n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; constructor.
      constructor.
      inversion 1.
    unfold AtLeast_dec. cbn. destruct (P_dec_spec h).
      destruct n as [| n']; cbn.
        do 2 constructor.
        unfold AtLeast_dec in IHt. destruct (IHt n'); constructor.
          constructor; assumption.
          intro. inv H.
            contradiction.
            apply (AtLeast_le _ _ (S n') n') in H2.
              contradiction.
              apply le_S, le_n.
      unfold AtLeast_dec in IHt. destruct (IHt n); constructor.
        constructor; assumption.
        intro. inv H.
          apply n1. constructor.
          contradiction.
          contradiction.
Qed.
(* end hide *)

Definition AtMost_dec
  {A : Type} (p : A -> bool) (n : nat) (l : list A) : bool :=
    count p l <=? n.

Lemma AtMost_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A) (n : nat),
      reflect (AtMost P n l) (AtMost_dec p n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor. constructor.
    destruct (P_dec_spec h).
      destruct n as [| n']; cbn.
        constructor. intro. inv H. contradiction.
        unfold AtMost_dec in IHt. destruct (IHt n'); constructor.
          constructor; assumption.
          intro. inv H; contradiction.
      unfold AtMost_dec in IHt. destruct (IHt n); constructor.
        constructor; assumption.
        intro. inv H.
          contradiction.
          apply n1. apply AtMost_le with n2.
            assumption.
            apply le_S, le_n.
Qed.
(* end hide *)

Fixpoint Sublist_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l2 with
    | [] => false
    | h2 :: t2 =>
        list_eq_dec eq_dec l1 t2 || Sublist_dec eq_dec l1 t2
end.

Lemma Sublist_dec_spec :
  forall
    (A : Type) (eq_dec : A -> A -> bool)
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Sublist l1 l2) (Sublist_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    destruct l1; constructor; inversion 1.
    destruct (list_eq_dec_spec eq_dec_spec l1 t2); cbn.
      constructor. subst. constructor.
      destruct (IHt2 l1); constructor.
        constructor. assumption.
        intro. inv H; contradiction.
Qed.
(* end hide *)

Fixpoint Prefix_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
    | [], _ => true
    | _, [] => false
    | h1 :: t1, h2 :: t2 => eq_dec h1 h2 && Prefix_dec eq_dec t1 t2
end.

Lemma Prefix_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Prefix l1 l2) (Prefix_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    do 2 constructor.
    destruct l2 as [| h2 t2].
      constructor. inversion 1.
      destruct (eq_dec_spec h1 h2); cbn.
        destruct (IHt1 t2); constructor.
          subst. constructor. assumption.
          intro. inv H. contradiction.
        constructor. intro. inv H. contradiction.
Qed.
(* end hide *)

Definition Suffix_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
    Prefix_dec eq_dec (rev l1) (rev l2).

Lemma Suffix_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Suffix l1 l2) (Suffix_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. pose (Prefix_Suffix _ (rev l1) (rev l2)). rewrite 2!rev_inv in i.
  unfold Suffix_dec. destruct (Prefix_dec_spec eq_dec_spec (rev l1) (rev l2)).
    constructor. rewrite <- i. assumption.
    constructor. intro. rewrite <-i in H. contradiction.
Qed.
(* end hide *)

Fixpoint Subseq_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
    | [], _ => true
    | _, [] => false
    | h1 :: t1, h2 :: t2 =>
        (eq_dec h1 h2 && Subseq_dec eq_dec t1 t2) ||
        Subseq_dec eq_dec l1 t2
end.

Lemma Subseq_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Subseq l1 l2) (Subseq_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. revert l1.
  induction l2 as [| h2 t2]; cbn; intro.
    destruct l1; constructor.
      constructor.
      inversion 1.
    destruct l1 as [| h1 t1].
      do 2 constructor.
      destruct (IHt2 (h1 :: t1)).
        rewrite Bool.orb_true_r. do 2 constructor. assumption.
        rewrite Bool.orb_false_r. destruct (eq_dec_spec h1 h2); cbn.
          destruct (IHt2 t1); constructor.
            subst. constructor. assumption.
            intro. inv H; contradiction.
          constructor. intro. inv H; contradiction.
Qed.
(* end hide *)

Fixpoint Incl_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1 with
    | [] => true
    | h :: t => elem_dec eq_dec h l2 && Incl_dec eq_dec t l2
end.

Lemma Incl_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Incl l1 l2) (Incl_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intro.
    constructor. unfold Incl. inversion 1.
    destruct (elem_dec_spec eq_dec_spec h l2); cbn.
      destruct (IHt l2); constructor; unfold Incl in *.
        intros. inv H.
          assumption.
          apply i. assumption.
        intro. apply n. intros. apply H. right. assumption.
      constructor. unfold Incl. intro. apply n, H. left.
Qed.
(* end hide *)

Definition SetEquiv_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
    Incl_dec eq_dec l1 l2 && Incl_dec eq_dec l2 l1.

Lemma SetEquiv_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (SetEquiv l1 l2) (SetEquiv_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. unfold SetEquiv_dec.
  destruct (Incl_dec_spec eq_dec_spec l1 l2); cbn.
    destruct (Incl_dec_spec eq_dec_spec l2 l1); constructor.
      rewrite SetEquiv_Incl. split; assumption.
      rewrite SetEquiv_Incl. destruct 1; contradiction.
    constructor. rewrite SetEquiv_Incl. destruct 1; contradiction.
Qed.
(* end hide *)

Fixpoint Permutation_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1 with
    | [] => isEmpty l2
    | h :: t =>
        match removeFirst (eq_dec h) l2 with
            | None => false
            | Some (_, l2') => Permutation_dec eq_dec t l2'
        end
end.

Lemma Permutation_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Permutation l1 l2) (Permutation_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct l2; constructor.
      reflexivity.
      intro. apply Permutation_length in H. inv H.
    destruct (removeFirst (eq_dec h) l2) eqn: Heq.
      destruct p. assert (h = a); subst.
        apply removeFirst_satisfies in Heq. destruct (eq_dec_spec h a).
          assumption.
          congruence.
        apply Permutation_removeFirst in Heq. destruct (IHt l); constructor.
          rewrite Heq, p. reflexivity.
          intro. rewrite Heq in H. apply Permutation_cons_inv in H.
            contradiction.
      constructor. intro. assert (elem h l2).
        rewrite <- Permutation_elem.
          left.
          exact H.
        assert (eq_dec h h = false).
          apply elem_removeFirst_None with l2; assumption.
          destruct (eq_dec_spec h h).
            congruence.
            contradiction.
Qed.
(* end hide *)

Fixpoint Cycle_dec_aux
  {A : Type} (eq_dec : A -> A -> bool) (n : nat) (l1 l2 : list A) : bool :=
match n with
    | 0 => list_eq_dec eq_dec l1 l2
    | S n' =>
        list_eq_dec eq_dec l1 (drop n l2 ++ take n l2) ||
        Cycle_dec_aux eq_dec n' l1 l2
end.

Definition Cycle_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
    Cycle_dec_aux eq_dec (length l1) l1 l2.

Lemma Cycle_dec_aux_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (m : nat) (l1 l2 : list A),
      reflect
        (exists n : nat, n <= m /\ l1 = drop n l2 ++ take n l2)
        (Cycle_dec_aux eq_dec m l1 l2).
(* begin hide *)
Proof.
  induction m as [| m']; cbn; intros.
    destruct (list_eq_dec_spec eq_dec_spec l1 l2); constructor.
      subst. exists 0. split.
        apply le_0_n.
        rewrite drop_0, take_0, app_nil_r. reflexivity.
      destruct 1 as (n' & H1 & H2). inv H1.
        rewrite drop_0, take_0, app_nil_r in n. contradiction.
    destruct (list_eq_dec_spec eq_dec_spec l1
                               (drop (S m') l2 ++ take (S m') l2)); cbn.
      constructor. exists (S m'). split.
        reflexivity.
        assumption.
      destruct (IHm' l1 l2); constructor.
        firstorder.
        destruct 1 as (n' & H1 & H2). apply n0. exists n'. split.
          assert (n' <> S m').
            intro. subst. contradiction.
            lia.
          assumption.
Qed.
(* end hide *)

Lemma Cycle_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (m : nat) (l1 l2 : list A),
      reflect (Cycle l1 l2) (Cycle_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. unfold Cycle_dec.
  destruct (Cycle_dec_aux_spec eq_dec_spec (length l1) l1 l2); constructor.
    rewrite Cycle_spec. assumption.
    intro. apply n. rewrite <- Cycle_spec. assumption.
Qed.
(* end hide *)

Definition Palindrome_dec
  {A : Type} (eq_dec : A -> A -> bool) (l : list A) : bool :=
    list_eq_dec eq_dec l (rev l).

Lemma Palindrome_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l : list A),
      reflect (Palindrome l) (Palindrome_dec eq_dec l).
(* begin hide *)
Proof.
  intros. unfold Palindrome_dec.
  destruct (list_eq_dec_spec eq_dec_spec l (rev l)); constructor.
    rewrite Palindrome_spec. assumption.
    intro. apply n. rewrite <- Palindrome_spec. assumption.
Qed.
(* end hide *)

(** ** Obliczanie wszystkich podstruktur danego rodzaju (permutacji,
       podciągów, cykli etc.) *)

Module cycles.

Fixpoint cycles_aux {A : Type} (n : nat) (l : list A) : list (list A) :=
match n with
    | 0 => []
    | S n' => cycle n l :: cycles_aux n' l
end.

Compute cycles_aux 0 [1; 2; 3; 4; 5].
Compute cycles_aux 5 [1; 2; 3; 4; 5].

Definition cycles {A : Type} (l : list A) : list (list A) :=
  cycles_aux (S (length l)) l.

Compute cycles [1; 2; 3; 4; 5].

Lemma Cycle_cycles_aux :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall n : nat,
      elem l1 (cycles_aux (S (length l2) + n) l2).
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn; intros.
      constructor.
      destruct (IHt n).
Admitted.

End cycles.

Module subseqs.

Fixpoint subseqs {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | h :: t => map (cons h) (subseqs t) ++ subseqs t
end.

Compute subseqs [1; 2; 3; 4; 5].

Check Subseq.

Lemma Subseq_subseqs :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> elem l1 (subseqs l2).
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn.
      constructor.
      apply elem_app_r. assumption.
    apply elem_app_l, elem_map. assumption.
    apply elem_app_r. assumption.
Qed.

Lemma subseqs_Subseq :
  forall (A : Type) (l1 l2 : list A),
    elem l1 (subseqs l2) -> Subseq l1 l2.
Proof.
  intros A l1 l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inversion H; subst.
      constructor.
      inversion H2.
    apply elem_app in H. destruct H.
      rewrite elem_map_conv in H. destruct H as (x & Heq & Hel).
        subst. constructor. apply IHt2. assumption.
      constructor. apply IHt2, H.
Qed.

End subseqs.