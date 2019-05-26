Require Import X3.

(** Tutaj trochę kodu kontynuującego temat rekursji dobrze ufundowanej oraz
    indukcji funkcyjnej. Dotychczas najpierw pisaliśmy sobie funkcje, a potem
    definiowaliśmy ich wykresy, żeby wykrzesać z nich regułę indukcji
    funkcyjnej. Teraz możemy zrobić trochę na odwrót: najpierw zdefiniujemy
    wykres funkcji [merge], która scala dwie listy posortowane według
    porządku wyznaczonego przez funkcję porównującą [f], zaś następnie
    użyjemy wykresu, aby zdefiniować i udowodnić właściwości naszej funkcji.
*)

Inductive Merge
  {A : Type} (f : A -> A -> bool) : list A -> list A -> list A -> Prop :=
    | Merge_nil_l : forall l : list A, Merge f [] l l
    | Merge_nil_r : forall l : list A, Merge f l [] l
    | Merge_cons_l :
        forall (h1 h2 : A) (t1 t2 r : list A),
          f h1 h2 = true -> Merge f t1 (h2 :: t2) r ->
            Merge f (h1 :: t1) (h2 :: t2) (h1 :: r)
    | Merge_cons_r :
        forall (h1 h2 : A) (t1 t2 r : list A),
          f h1 h2 = false -> Merge f (h1 :: t1) t2 r ->
            Merge f (h1 :: t1) (h2 :: t2) (h2 :: r).

Hint Constructors Merge.

Definition merge' :
  forall {A : Type} {f : A -> A -> bool} (l1 l2 : list A),
    {r : list A | Merge f l1 l2 r}.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    exists l2. constructor.
    induction l2 as [| h2 t2]; cbn.
      exists (h1 :: t1). constructor.
      case_eq (f h1 h2); intro.
        destruct (IHt1 (h2 :: t2)) as [r IH].
          exists (h1 :: r). constructor; assumption.
        destruct IHt2 as [r IH'].
          exists (h2 :: r). constructor.
            assumption.
            assumption.
Defined.

Definition merge {A : Type} (f : A -> A -> bool) (l1 l2 : list A) : list A :=
  proj1_sig (@merge' A f l1 l2).

Require Import Arith.

Check leb.

Compute merge leb [1; 2; 3; 4] [2; 2; 0; 5].

Ltac inv H :=
  inversion H; subst; clear H; auto.

Lemma Merge_det :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 r1 r2 : list A},
    Merge f l1 l2 r1 -> Merge f l1 l2 r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; intros.
    inv H.
    inv H.
    inv H1.
      f_equal. apply IHMerge. assumption.
      congruence.
    inv H1.
      congruence.
      f_equal. apply IHMerge. assumption.
Qed.

Lemma merge_correct :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 r : list A},
    merge f l1 l2 = r -> Merge f l1 l2 r.
Proof.
  unfold merge. intros.
  destruct (merge' l1 l2).
  cbn in H. subst. assumption.
Qed.

Lemma merge_complete :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 r : list A},
    Merge f l1 l2 r -> merge f l1 l2 = r.
Proof.
  unfold merge. intros.
  destruct (merge' l1 l2). cbn.
  eapply Merge_det; eassumption.
Qed.

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

Lemma merge_eq :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 : list A},
    merge f l1 l2 =
    match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | h1 :: t1, h2 :: t2 =>
            if f h1 h2 then h1 :: merge f t1 l2 else h2 :: merge f l1 t2
    end.
Proof.
  intros A f.
  apply (funind_merge
    (fun l1 l2 r =>
      r =
      match l1, l2 with
          | [], _ => l2
          | _, [] => l1
          | h1 :: t1, h2 :: t2 =>
              if f h1 h2 then h1 :: merge f t1 l2 else h2 :: merge f l1 t2
      end));
  intros; subst.
    reflexivity.
    destruct l; reflexivity.
    destruct t1; rewrite H.
      cbn. reflexivity.
      f_equal.
Abort.

Lemma Permutation_Merge :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 r : list A},
    Merge f l1 l2 r -> Permutation (l1 ++ l2) r.
Proof.
  induction 1.
    cbn. apply Permutation_refl.
    rewrite app_nil_r. apply Permutation_refl.
    cbn. constructor. assumption.
    rewrite Permutation_app_comm. cbn. constructor.
      rewrite Permutation_app_comm. assumption.
Qed.

Lemma Merge_length :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 r : list A},
    Merge f l1 l2 r -> length r = length l1 + length l2.
Proof.
  intros. apply Permutation_Merge in H. apply Permutation_length in H.
  rewrite <- H. rewrite length_app. reflexivity.
Qed.

Lemma Merge_map :
  forall {A B : Type} {p : B -> B -> bool} {f : A -> B} {l1 l2 r : list A},
    Merge (fun x y : A => p (f x) (f y)) l1 l2 r ->
      Merge p (map f l1) (map f l2) (map f r).
Proof.
  induction 1; cbn in *; constructor; assumption.
Qed.

Lemma Merge_rev :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 r : list A},
    Merge f l1 l2 r -> Merge f (rev l1) (rev l2) (rev r).
Proof.
  induction 1; cbn in *.
    constructor.
    constructor.
Abort.

Lemma Merge_replicate :
  forall {A : Type} {f : A -> A -> bool} {x y : A} {n m : nat},
    Merge f (replicate n x) (replicate m y)
      (if f x y
       then replicate n x ++ replicate m y
       else replicate m y ++ replicate n x).
Proof.
  intros. case_eq (f x y); intro.
    revert x y m H. induction n as [| n']; cbn; intros.
      constructor.
      destruct m as [| m']; cbn; intros.
        rewrite app_nil_r. constructor.
        constructor.
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

(** Tu jakieś guwno. *)

Goal
  forall {A : Type} {R : A -> A -> Prop} {l : list A},
    (forall x : A, R x x) ->
      Merge R l l (concat (map (fun x => [x; x]) l)).
Proof.
  induction l as [| h t IH]; cbn; intros.
    constructor.
    constructor.
      apply H.
      induction t as [| h' t' IH']; cbn.
        constructor.
        constructor.

Goal
  forall {A : Type} {R : A -> A -> Prop} {l l1 l2 r : list A},
    (forall x : A, R x x) ->
      Merge R l1 l2 r ->
        Merge R (l ++ l1) (l ++ l2) (concat (map (fun x => [x; x]) l) ++ r).
Proof.
  induction 2.
    rewrite app_nil_r. induction l as [| h t]; cbn.
      constructor.
      constructor.
        apply H.
        destruct t as [| h' t']; cbn in *.
          constructor.
          inversion IHt; subst; clear IHt.
Abort.

Goal
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 r1 l3 l4 r2 : list A},
    Merge R l1 l2 r1 -> Merge R l3 l4 r2 ->
      Merge R (l1 ++ l3) (l2 ++ l4) (r1 ++ r2).
Proof.
  intros until 1. revert l3 l4 r2.
  induction H; cbn; intros.
    induction H; cbn.
      constructor.
      rewrite app_nil_r. 