(** * D5: Listy *)

From Typonomikon Require Export D5c.

(** * Niestandardowe reguły indukcyjne (TODO) *)

(** Wyjaśnienia nadejdą już wkrótce. *)

Fixpoint list_ind_2
  (A : Type) (P : list A -> Prop)
  (H0 : P [])
  (H1 : forall x : A, P [x])
  (H2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
    (l : list A) : P l.
(* begin hide *)
Proof.
  destruct l as [| x [| y l]]; cbn; auto.
  apply H2. apply list_ind_2; auto.
Qed.
(* end hide *)

Lemma list_ind_rev :
  forall (A : Type) (P : list A -> Prop)
    (Hnil : P [])
    (Hsnoc : forall (h : A) (t : list A), P t -> P (snoc h t))
      (l : list A), P l.
(* begin hide *)
Proof.
  intros. cut (forall l : list A, P (rev l)); intro.
    specialize (H (rev l)). rewrite <- rev_rev. assumption.
    induction l0 as [| h t]; cbn.
      assumption.
      apply Hsnoc. assumption.
Qed.
(* end hide *)

Lemma list_ind_app_l :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l' ++ l))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    assumption.
    apply (IH _ [h]). assumption.
Qed.
(* end hide *)

Lemma list_ind_app_r :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t] using list_ind_rev; cbn.
    assumption.
    rewrite snoc_app_singl. apply (IH t [h]). assumption.
Qed.
(* end hide *)

Lemma list_ind_app :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (IH : forall l l' : list A, P l -> P l' -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    assumption.
    apply (IH [h] t); auto.
Qed.
(* end hide *)

Lemma list_app_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (l l1 l2 : list A), P l -> P (l1 ++ l ++ l2)) ->
      forall l : list A, P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply H.
    specialize (H0 t [h] [] IHt). rewrite app_nil_r in H0.
      cbn in H0. assumption.
Qed.
(* end hide *)

(** ** Palindromy *)

(** Palindrom to słowo, które czyta się tak samo od przodu jak i od tyłu.

    Zdefiniuj induktywny predykat [Palindrome], które odpowiada powyższemu
    pojęciu palindromu, ale dla list elementów dowolnego typu, a nie tylko
    słów. *)

(* begin hide *)
Inductive Palindrome {A : Type} : list A -> Prop :=
| Palindrome_nil : Palindrome []
| Palindrome_singl :
    forall x : A, Palindrome [x]
| Palindrome_1 :
    forall (x : A) (l : list A),
      Palindrome l -> Palindrome (x :: snoc x l).
(* end hide *)

Lemma Palindrome_inv :
  forall (A : Type) (x : A) (l : list A),
    Palindrome (x :: l ++ [x]) -> Palindrome l.
(* begin hide *)
Proof.
  intros. rewrite <- snoc_app_singl in H. inv H.
    destruct l; inv H2.
    apply snoc_inj_r in H2. subst. assumption.
Qed.
(* end hide *)

Lemma Palindrome_inv_2 :
  forall (A : Type) (x y : A),
    Palindrome [x; y] -> x = y.
(* begin hide *)
Proof.
  intros. inv H. apply (f_equal last) in H2.
  rewrite last_snoc in H2. cbn in *. inv H2.
  reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_inv_3 :
  forall (A : Type) (x y : A) (l : list A),
    Palindrome (x :: l ++ [y]) -> x = y.
(* begin hide *)
Proof.
  intros. rewrite <- snoc_app_singl in H. inv H.
    destruct l; inv H2.
    apply snoc_inj in H2. destruct H2. assumption.
Qed.
(* end hide *)

Lemma nat_ind_2 :
  forall P : nat -> Prop,
    P 0 -> P 1 -> (forall n : nat, P n -> P (S (S n))) ->
      forall n : nat, P n.
(* begin hide *)
Proof.
  fix IH 5. destruct n as [| [| n']].
    1-2: assumption.
    apply H1, IH; assumption.
Qed.
(* end hide *)

Lemma Palindrome_length :
  forall (A : Type) (x : A) (n : nat),
    exists l : list A, Palindrome l /\ n <= length l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    exists []. split; constructor.
    destruct IHn' as (l & IH1 & IH2).
      exists (x :: snoc x l). split.
        constructor. assumption.
        cbn. rewrite length_snoc. apply le_n_S, le_S. assumption.
Restart.
  induction n as [| | n'] using nat_ind_2.
    exists []. split; constructor.
    exists [x]. split; constructor.
    destruct IHn' as (l & IH1 & IH2). exists (x :: snoc x l). split.
      constructor. assumption.
      cbn. rewrite length_snoc. do 2 apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma Palindrome_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (x :: snoc x l).
(* begin hide *)
Proof.
  constructor. assumption.
Qed.
(* end hide *)

Lemma Palindrome_app :
  forall (A : Type) (l1 l2 : list A),
    Palindrome l1 -> Palindrome l2 -> Palindrome (l1 ++ l2 ++ rev l1).
(* begin hide *)
Proof.
  intros A l1 l2 H. revert l2.
  induction H; cbn; intros.
    rewrite app_nil_r. assumption.
    rewrite <- snoc_app_singl. constructor. assumption.
    replace _ with
        (Palindrome (x :: (l ++ ([x] ++ l2 ++ [x]) ++ rev l) ++ [x])).
      rewrite <- snoc_app_singl. constructor. apply IHPalindrome.
        cbn. rewrite <- snoc_app_singl. constructor. assumption.
      rewrite !snoc_app_singl, rev_app, !app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_app' :
  forall (A : Type) (l1 l2 : list A),
    Palindrome l2 -> Palindrome (l1 ++ l2 ++ rev l1).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite app_nil_r. assumption.
    replace _ with (Palindrome (h1 :: snoc h1 (t1 ++ l2 ++ rev t1))).
      constructor. apply IHt1. assumption.
      rewrite !snoc_app_singl, !app_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_rev :
  forall (A : Type) (l : list A),
    Palindrome l <-> Palindrome (rev l).
(* begin hide *)
Proof.
  intro. assert (forall l : list A, Palindrome l -> Palindrome (rev l)).
    induction 1; cbn.
      1-2: constructor.
      rewrite rev_snoc. constructor. assumption.
    split; intro.
      apply H, H0.
      rewrite <- rev_rev. apply H, H0.
Qed.
(* end hide *)

(* Palindromowa indukcja *)
Lemma list_palindrome_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall x : A, P [x]) ->
    (forall (x y : A) (l : list A), P l -> P (x :: snoc y l)) ->
      forall l : list A, P l.
(* begin hide *)
Proof.
  fix IH 6. destruct l as [| h t].
    assumption.
    destruct (init_decomposition A t); subst.
      apply H0.
      destruct H2 as (h' & t' & H1' & H2' & H3'). rewrite H3'.
        rewrite <- snoc_app_singl. apply H1. apply IH; assumption.
Admitted.
(* end hide *)

Lemma Palindrome_spec :
  forall (A : Type) (l : list A),
    Palindrome l <-> l = rev l.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      1-2: reflexivity.
      rewrite rev_snoc, <- IHPalindrome; cbn. reflexivity.
    induction l as [| x | x y l'] using list_palindrome_ind; cbn; intros.
      1-2: constructor.
      rewrite rev_snoc in H. cbn in H. inv H.
        constructor. apply IHl'. apply snoc_inj_r in H2. assumption.
Qed.
(* end hide *)

Lemma Palindrome_spec' :
  forall (A : Type) (l : list A),
    Palindrome l -> exists l1 l2 : list A,
      l = l1 ++ l2 ++ rev l1 /\ length l2 <= 1.
(* begin hide *)
Proof.
  induction 1; cbn.
    exists [], []. cbn. split; [reflexivity | apply Nat.le_0_l].
    exists [], [x]. cbn. split; [reflexivity | apply le_n].
    destruct IHPalindrome as (l1 & l2 & IH1 & IH2). subst.
      exists (x :: l1), l2. cbn. split.
        rewrite !snoc_app. reflexivity.
        assumption.
Qed.
(* end hide *)

Lemma Palindrome_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    Palindrome l -> Palindrome (map f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    1-2: constructor.
    rewrite map_snoc. constructor. assumption.
Qed.
(* end hide *)

Lemma replicate_S :
  forall (A : Type) (n : nat) (x : A),
    replicate (S n) x = x :: replicate n x.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma Palindrome_replicate :
  forall (A : Type) (n : nat) (x : A),
    Palindrome (replicate n x).
(* begin hide *)
Proof.
  induction n as [| | n'] using nat_ind_2; intros.
    constructor.
    constructor.
    rewrite replicate_S, <- rev_replicate. cbn. constructor.
      rewrite rev_replicate. apply IHn'.
Qed.
(* end hide *)

Lemma Palindrome_cons_replicate :
  forall (A : Type) (n : nat) (x y : A),
    Palindrome (x :: replicate n y) -> n = 0 \/ x = y.
(* begin hide *)
Proof.
  destruct n as [| n']; intros.
    left. reflexivity.
    right. rewrite <- snoc_replicate, snoc_app_singl in H.
      apply Palindrome_inv_3 in H. assumption.
Qed.
(* end hide *)

Lemma Palindrome_iterate :
  forall (A : Type) (f : A -> A),
    (forall (n : nat) (x : A), Palindrome (iterate f n x)) ->
      forall x : A, f x = x.
(* begin hide *)
Proof.
  intros. specialize (H 2 x). cbn in H. inv H. destruct l; inv H2.
    rewrite <- ?H0. reflexivity.
    apply (f_equal isEmpty) in H3. rewrite isEmpty_snoc in H3.
      destruct l; inv H3.
Qed.
(* end hide *)

Lemma Palindrome_nth :
  forall (A : Type) (l : list A),
    Palindrome l -> forall n : nat,
      n < length l -> nth n l = nth (length l - S n) l.
(* begin hide *)
Proof.
  intros. apply Palindrome_spec in H.
  rewrite H at 1. apply nth_rev. assumption.
Qed.
(* end hide *)

Lemma Palindrome_drop :
  forall (A : Type) (l : list A),
    (forall n : nat, Palindrome (drop n l)) ->
      l = [] \/ exists (n : nat) (x : A), l = replicate n x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. reflexivity.
    right. destruct IHt.
      intro. specialize (H (S n)). cbn in H. assumption.
      subst. exists 1, h. cbn. reflexivity.
      destruct H0 as (n & x & IH). subst. exists (S n), h. cbn.
        specialize (H 0). cbn in H. apply Palindrome_cons_replicate in H.
          destruct H; subst; cbn; reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_take :
  forall (A : Type) (l : list A),
    (forall n : nat, Palindrome (take n l)) ->
      l = [] \/ exists (n : nat) (x : A), l = replicate n x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. reflexivity.
    right. destruct IHt.
      intro. specialize (H n). destruct n as [| n']; cbn in *.
        rewrite take_0. constructor. admit.
        exists 1, h. cbn. subst. reflexivity.
        destruct H0 as (n & x & IH). subst. exists (S n), h. cbn. f_equal.
          specialize (H (S n)). cbn in H. rewrite take_replicate in H.
            rewrite Nat.min_id in H. inversion H; subst.
              destruct n; inversion H2; cbn. reflexivity.
              pose (H2' := H2). apply (f_equal last) in H2'. rewrite last_snoc, last_replicate in H2'.
                destruct n; cbn in *; inversion H2'; subst. assumption.
Admitted.
(* end hide *)

Lemma replace_Palindrome :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> Palindrome l ->
      Palindrome l' <-> length l = 1 /\ n = 0 \/ nth n l = Some x.
(* begin hide *)
Proof.
  split.
    2: {
      destruct 1 as [[H1 H2] | H1].
        subst. destruct l as [| h [| h' t]]; inv H; inv H1. constructor.
        assert (l = l').
          rewrite replace_nth_eq; eassumption.
          subst. assumption.
    }
    intros. apply Palindrome_spec in H0. apply Palindrome_spec in H1.
      rewrite H0, H1 in H. rewrite replace_rev in H.
        unfold omap in H.
Abort.
(* end hide *)

Lemma Palindrome_zip :
  exists (A B : Type) (la : list A) (lb : list B),
    Palindrome la /\ Palindrome lb /\ ~ Palindrome (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool, [true; true], [false; true; false].
  cbn. repeat split.
    apply (Palindrome_1 true []). constructor.
    apply (Palindrome_1 false [true]). constructor.
    intro. apply Palindrome_inv_2 in H. inv H.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Palindrome vs unzip, zipWith, unzipWith *)
(* end hide *)

Lemma Palindrome_findLast_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    Palindrome l -> find p l = findLast p l.
(* begin hide *)
Proof.
  intros.
  apply Palindrome_spec in H.
  rewrite <- findLast_rev, <- H.
  reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    Palindrome l -> Palindrome (pmap f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); constructor.
    destruct (f x) eqn: Heq; cbn.
      rewrite pmap_snoc. rewrite Heq. constructor. assumption.
      rewrite pmap_snoc. rewrite Heq. assumption.
Qed.
(* end hide *)

Lemma Palindrome_intersperse :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (intersperse x l).
(* begin hide *)
Proof.
  intros. rewrite Palindrome_spec in *.
  rewrite <- intersperse_rev, <- H. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Palindrome vs groupBy *)
(* end hide *)

Lemma Palindrome_Dup :
  forall (A : Type) (l : list A),
    Palindrome l -> length l <= 1 \/ Dup l.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    left. apply Nat.le_0_l.
    left. apply le_n.
    right. constructor. rewrite elem_snoc. right. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Palindrome vs Incl, Sublist, subseq *)
(* end hide *)

Lemma Sublist_Palindrome :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Palindrome l1 -> Palindrome l2 -> l1 = [].
(* begin hide *)
Proof.
  induction 1; intros.
Abort.
(* end hide *)

Lemma Prefix_Palindrome :
  forall (A : Type) (l : list A),
    Prefix (rev l) l <-> Palindrome l.
(* begin hide *)
Proof.
  split; intro.
    apply Prefix_rev_l in H. rewrite Palindrome_spec. assumption.
    apply Palindrome_spec in H. rewrite <- H. apply Prefix_refl.
Qed.
(* end hide *)

Lemma Subseq_rev_l :
  forall (A : Type) (l : list A),
    Subseq (rev l) l <-> Palindrome l.
(* begin hide *)
Proof.
  split.
    intro. apply Palindrome_spec. induction l as [| h t]; cbn; intros.
      reflexivity.
Abort.
(* end hide *)

Lemma Subseq_rev_r :
  forall (A : Type) (l : list A),
    Subseq l (rev l) <-> Palindrome l.
(* begin hide *)
Proof.
  split.
Abort.
(* end hide *)