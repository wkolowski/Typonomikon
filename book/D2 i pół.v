(** * D2 i pół *)

(** W tym rozdziale będą różne formy indukcji/rekursji, których chwilowo nie
    chcę wstawiać do głównego tekstu rozdziałów D2 i D3, bo tam nie pasują.
    Prędzej czy później zostaną one z tymi rozdział zintegrowane (albo i nie -
    nie mamy pańskiego płaszcza i co nam pan zrobi?). *)

(** * Rekursja monotoniczna *)

Require Import X3.

Fixpoint merge
  {A : Type} (cmp : A -> A -> bool) (l1 : list A) : list A -> list A :=
match l1 with
  | [] => fun l2 : list A => l2
  | h1 :: t1 =>
      fix merge' (l2 : list A) : list A :=
        match l2 with
          | [] => l1
          | h2 :: t2 =>
              if cmp h1 h2
              then h1 :: merge cmp t1 l2
              else h2 :: merge' t2
        end
end.

Require Import Arith.

Compute merge leb [1; 4; 6; 9] [2; 3; 5; 8].

(*
Lemma funind_merge :
  forall {A : Type} (P : list A -> list A -> list A -> Prop)
    {f : A -> A -> bool},
      (forall l : list A, P [] l l) ->
      (forall l : list A, P l [] l) ->
      (forall (h1 h2 : A) (t1 t2 r : list A),
        f h1 h2 = true ->
          P t1 (h2 :: t2) r -> P (h1 :: t1) (h2 :: t2) (h1 :: r)) ->
      (forall (h1 h2 : A) (t1 t2 r : list A),
        f h1 h2 = false ->
          P (h1 :: t1) t2 r -> P (h1 :: t1) (h2 :: t2) (h2 :: r)) ->
      forall l1 l2 : list A, P l1 l2 (merge f l1 l2).
Proof.
  intros. unfold merge. destruct (merge' l1 l2). cbn.
  induction m; cbn; auto.
Defined.
*)


Lemma merge_eq :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A},
    merge cmp l1 l2 =
    match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | h1 :: t1, h2 :: t2 =>
            if cmp h1 h2
            then h1 :: merge cmp t1 l2
            else h2 :: merge cmp l1 t2
    end.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      reflexivity.
      destruct (cmp h1 h2); cbn.
        rewrite IHt1. reflexivity.
        rewrite IHt2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_merge :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 : list A},
    Permutation (merge f l1 l2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite app_nil_r. reflexivity.
      destruct (f h1 h2).
        rewrite IHt1. reflexivity.
        rewrite IHt2. rewrite perm_swap.
          constructor. rewrite Permutation_app_comm.
            rewrite (Permutation_app_comm _ t1 (h2 :: t2)). reflexivity.
Qed.
(* end hide *)

Lemma merge_length :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 : list A},
    length (merge f l1 l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite <- plus_n_O. reflexivity.
      destruct (f h1 h2); cbn.
        rewrite IHt1. cbn. reflexivity.
        rewrite IHt2. rewrite plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma merge_map :
  forall {A B : Type} {cmp : B -> B -> bool} {f : A -> B} {l1 l2 : list A},
      merge cmp (map f l1) (map f l2) =
      map f (merge (fun x y : A => cmp (f x) (f y)) l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      reflexivity.
      destruct (cmp (f h1) (f h2)); cbn.
        rewrite <- IHt1. cbn. reflexivity.
        rewrite IHt2. reflexivity.
Qed.
(* end hide *)

Lemma merge_rev :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A},
    merge cmp (rev l1) (rev l2) = rev (merge cmp l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite merge_eq. destruct (rev t1 ++ [h1]); reflexivity.
      destruct (cmp h1 h2); cbn.
        Focus 2. rewrite <- IHt2.
Abort.
(* end hide *)

Lemma Merge_replicate :
  forall {A : Type} {cmp : A -> A -> bool} {x y : A} {n m : nat},
    merge cmp (replicate n x) (replicate m y) =
    if cmp x y
    then replicate n x ++ replicate m y
    else replicate m y ++ replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    destruct (cmp x y); try reflexivity.
      intros. rewrite app_nil_r. reflexivity.
    induction m as [| m']; cbn.
      destruct (cmp x y).
        rewrite app_nil_r. reflexivity.
        reflexivity.
      case_eq (cmp x y); intro eq.
        rewrite merge_eq. destruct n'; cbn.
          reflexivity.
          rewrite eq in *. cbn in *.
Abort.
(* end hide *)

(*
  intros. case_eq (cmp x y); intro.
    revert x y m H. induction n as [| n']; cbn; intros.
      constructor.
      induction m as [| m']; cbn; intros.
        rewrite app_nil_r. constructor.
        rewrite H. f_equal. rewrite <- IHm'. rewrite <- (IHn' _ _ (S m') H). apply IHn'.
          assumption.
          specialize (IHn' _ _ (S m') H). cbn in IHn'. apply IHn'.
    revert x y n H. induction m as [| m']; cbn; intros.
      constructor.
      destruct n as [| n']; cbn; intros.
        rewrite app_nil_r. constructor.
        constructor.
          assumption.
          specialize (IHm' _ _ (S n') H). cbn in IHm'. apply IHm'.
Qed.

Fixpoint ins
  {A : Type} (f : A -> A -> bool) (l : list A) (x : A) : list A :=
match l with
    | [] => [x]
    | h :: t => if f x h then x :: h :: t else h :: ins f t x
end.

Lemma Merge_ins :
  forall {A : Type} {f : A -> A -> bool} {l : list A} {x : A},
    Merge f [x] l (ins f l x).
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    case_eq (f x h); auto.
Qed.

Lemma Merge_ins' :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 r : list A} {x : A},
    Merge f l1 l2 r -> Merge f (ins f l1 x) l2 (ins f r x).
Proof.
  intros until 1.
  induction H; cbn in *; intros.
    apply Merge_ins.
    constructor.
    case_eq (f x h1); constructor; auto. admit. (* transitivity *)
    case_eq (f x h2); intro.
      case_eq (f x h1); intro.
        constructor; auto.
        admit. (* more order properties *)
      case_eq (f x h1); intro.
        constructor; auto. rewrite H2 in IHMerge. apply IHMerge.
        constructor; auto. rewrite H2 in IHMerge. apply IHMerge.
Admitted.

Lemma Merge_all_true :
  forall {A : Type} {p : A -> A -> bool} {l : list A} {x : A},
    all (fun y : A => p x y) l = true ->
      Merge p [x] l (x :: l).
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    case_eq (p x h); intro.
      constructor; auto.
      rewrite H0 in H. cbn in H. inv H.
Qed.

Lemma Merge_filter :
  forall {A : Type} {f : A -> A -> bool} {p : A -> bool} {l1 l2 r : list A},
    Merge f l1 l2 r -> Merge f (filter p l1) (filter p l2) (filter p r).
Proof.
  induction 1; cbn in *.
    1-2: constructor.
    destruct (p h1), (p h2); cbn.
      constructor; auto.
Abort.
*)