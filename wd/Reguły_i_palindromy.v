Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(** * Niestandardowe reguły indukcyjne *)

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
    (Hsnoc : forall (h : A) (t : list A), P t -> P (t ++ [h]))
      (l : list A), P l.
(* begin hide *)
Proof.
  intros. cut (forall l : list A, P (rev l)); intro.
    specialize (H (rev l)). rewrite <- rev_inv. assumption.
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
    apply (IH t [h]). assumption.
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

(** Palindrom to słowo, które czyta się tak samo od przodu jak i od tyłu.

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
          Palindrome l -> Palindrome (x :: l ++ [x]).
(* end hide *)

(* begin hide *)

Lemma Palindrome_inv :
  forall (A : Type) (x : A) (l : list A),
    Palindrome (x :: l ++ [x]) -> Palindrome l.
(* begin hide *)
Proof.
  intros. inv H.
    apply (f_equal length) in H2. rewrite length_app in H2.
      cbn in H2. rewrite <- plus_n_Sm in H2. inv H2.
    apply app_inv_r in H2. subst. assumption.
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
      exists (x :: l ++ [x]). split.
        constructor. assumption.
        cbn. rewrite length_app. cbn. omega.
Restart.
  induction n as [| | n'] using nat_ind_2.
    exists []. split; constructor.
    exists [x]. split; constructor.
    destruct IHn' as (l & IH1 & IH2). exists (x :: l ++ [x]). split.
      constructor. assumption.
      cbn. rewrite length_app. cbn. omega.
Qed.
(* end hide *)

Lemma Palindrome_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (x :: snoc x l).
(* begin hide *)
Proof.
  intros. rewrite snoc_app_singl. constructor. assumption.
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
    constructor. assumption.
    replace _ with
        (Palindrome (x :: (l ++ ([x] ++ l2 ++ [x]) ++ rev l) ++ [x])).
      constructor. apply IHPalindrome. cbn. constructor. assumption.
      rewrite rev_app, !app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_rev :
  forall (A : Type) (l : list A),
    Palindrome l <-> Palindrome (rev l).
(* begin hide *)
Proof.
  assert (forall (A : Type) (l : list A),
            Palindrome l -> Palindrome (rev l)).
    induction 1; cbn.
      1-2: constructor.
      rewrite rev_app. cbn. constructor. assumption.
    split; intro.
      apply H. assumption.
      rewrite <- rev_inv. apply H. assumption.
Qed.
(* end hide *)

Lemma Palindrome_spec :
  forall (A : Type) (l : list A),
    Palindrome l <-> l = rev l.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      1-2: reflexivity.
      rewrite rev_app, <- IHPalindrome; cbn. reflexivity.
    revert l.
    eapply
    (@well_founded_ind _
      (fun l1 l2 : list A => length l1 < length l2) _
      (fun l : list A => l = rev l -> Palindrome l) _) .
Unshelve.
  unfold well_founded. induction a as [| h t]; cbn.
    constructor. intros. inv H.
    inv IHt. constructor. intros. constructor. intros. apply H.
      cbn in *. omega.
  destruct x as [| h t]; cbn; intros.
    constructor.
    destruct (rev t) eqn: Heq.
      inv H0. constructor.
      rewrite H0. inv H0. constructor. apply H.
        rewrite length_app. apply le_n_S. cbn.
          rewrite <- plus_n_Sm, <- plus_n_O. apply le_S, le_n.
        rewrite rev_app in Heq. cbn in Heq. inv Heq.
          rewrite H1. symmetry. assumption.
Qed.
(* end hide *)

Lemma Palindrome_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    Palindrome l -> Palindrome (map f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    1-2: constructor.
    rewrite map_app. cbn. constructor. assumption.
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

Lemma Palindrome_iterate :
  forall (A : Type) (f : A -> A),
    (forall (n : nat) (x : A), Palindrome (iterate f n x)) ->
      forall x : A, f x = x.
(* begin hide *)
Proof.
  intros. specialize (H 2 x). cbn in H. inv H. destruct l; inv H2.
    rewrite <- ?H0. reflexivity.
    apply (f_equal isEmpty) in H3. rewrite isEmpty_app in H3.
      destruct l; inv H3.
Qed.
(* end hide *)

Lemma nth_rev :
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> nth n (rev l) = nth (length l - S n) l.
(* begin hide *)
Proof.
Admitted.
(* begin hide *)

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

(* TODO *) Lemma Palindrome_take :
  forall (A : Type) (l : list A),
    (forall n : nat, Palindrome (take n l)) ->
      l = [] \/ exists (n : nat) (x : A), l = replicate n x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. reflexivity.
    right.
Admitted.
(* end hide *)

(*
Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

Qed.
(* end hide *)

Lemma Palindrome_ :
  forall (A : Type) (l : list A),
    Palindrome l -> .
(* begin hide *)
Proof.
  induction 1; cbn; intros.

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
      rewrite pmap_app. cbn. rewrite Heq. constructor. assumption.
      rewrite pmap_app. cbn. rewrite Heq, app_nil_r. assumption.
Qed.
(* end hide *)
*)