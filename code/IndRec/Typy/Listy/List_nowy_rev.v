
(* begin hide *)
Inductive Palindrome {A : Type} : list A -> Prop :=
    | Palindrome_nil : Palindrome []
    | Palindrome_singl :
        forall x : A, Palindrome [x]
    | Palindrome_1 :
        forall (x : A) (l : list A),
          Palindrome l -> Palindrome (x :: snoc x l).
(* end hide *)

(* begin hide *)

Lemma Palindrome_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (x :: snoc x l).
(* begin hide *)
Proof.
  constructor. assumption.
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

(* Palindromowa indukcja *)
Lemma list_palindrome_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall x : A, P [x]) ->
    (forall (x y : A) (l : list A), P l -> P (x :: snoc y l)) ->
      forall l : list A, P l.
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
        constructor. apply IHl'. apply snoc_inj in H2. assumption.
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