(** Zainspirowane przez http://www.weaselhat.com/2020/05/07/smart-constructors-are-smarter-than-you-think/
    Definicje wzięte z https://en.wikipedia.org/wiki/Brzozowski_derivative *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Inductive Regex (A : Type) : Type :=
    | Empty : Regex A
    | Epsilon : Regex A
    | Char : A -> Regex A
    | Seq : Regex A -> Regex A -> Regex A
    | Or : Regex A -> Regex A -> Regex A
    | Star : Regex A -> Regex A.

Arguments Empty {A}.
Arguments Epsilon {A}.

Fixpoint containsEpsilon
  {A : Type} (r : Regex A) : bool :=
match r with
    | Empty => false
    | Epsilon => true
    | Char _ => false
    | Seq r1 r2 => containsEpsilon r1 && containsEpsilon r2
    | Or r1 r2 => containsEpsilon r1 || containsEpsilon r2
    | Star _ => true
end.

Fixpoint aux
  {A : Type} (dec : A -> A -> bool)
  (a : A) (r : Regex A)
  : Regex A :=
match r with
    | Empty   => Empty
    | Epsilon => Epsilon
    | Char x  => if dec a x then Epsilon else Empty
    | Seq r1 r2 =>
        Or (Seq (aux dec a r1) r2)
           (if containsEpsilon r1
            then aux dec a r2
            else Empty)
    | Or r1 r2 => Or (aux dec a r1) (aux dec a r2)
    | Star r' => Seq (aux dec a r') (Star r')
end.

Require Import List.
Import ListNotations.

Fixpoint brzozowski
  {A : Type} (dec : A -> A -> bool)
  (l : list A) (r : Regex A)
  : Regex A :=
match l with
    | [] => r
    | h :: t => aux dec h (brzozowski dec t r)
end.

Definition matches
  {A : Type} (dec : A -> A -> bool)
  (l : list A) (r : Regex A) : bool :=
    containsEpsilon (brzozowski dec (rev l) r).

Fixpoint repeat {A : Type} (n : nat) (l : list A) : list A :=
match n with
    | 0 => []
    | S n' => l ++ repeat n' l
end.

Inductive Matches {A : Type} : list A -> Regex A -> Prop :=
    | MEpsilon : Matches [] Epsilon
    | MChar : forall x : A, Matches [x] (Char x)
    | MSeq :
        forall (l1 l2 : list A) (r1 r2 : Regex A),
          Matches l1 r1 -> Matches l2 r2 ->
            Matches (l1 ++ l2) (Seq r1 r2)
    | MOrL :
        forall (l : list A) (r1 r2 : Regex A),
          Matches l r1 -> Matches l (Or r1 r2)
    | MOrR :
        forall (l : list A) (r1 r2 : Regex A),
          Matches l r2 -> Matches l (Or r1 r2)
    | MStar_Zero :
        forall r : Regex A, Matches [] (Star r)
    | MStar_More :
        forall (l1 l2 : list A) (r : Regex A),
          Matches l1 r -> Matches l2 (Star r) -> Matches (l1 ++ l2) (Star r).

Ltac inv H := inversion H; subst; clear H; auto.

Hint Constructors Matches : core.

Require Import Bool.

Lemma containsEpsilon_Matches_nil :
  forall
    {A : Type} (r : Regex A),
      containsEpsilon r = true
        <->
      Matches [] r.
Proof.
  split.
    induction r; cbn.
      inversion 1.
      constructor.
      inversion 1.
      intro. destruct (containsEpsilon r1), (containsEpsilon r2); inv H.
        change [] with (@nil A ++ []). constructor.
          apply IHr1. reflexivity.
          apply IHr2. reflexivity.
      intros. destruct (containsEpsilon r1); cbn in *; eauto.
      change (@nil A) with (@repeat A 0 []). constructor.
    induction r; cbn; intros.
      inv H.
      reflexivity.
      inv H.
      inv H. rewrite IHr1, IHr2.
        reflexivity.
        destruct l1, l2; inv H0.
        destruct l1, l2; inv H0.
      inv H.
        rewrite IHr1; auto.
        rewrite IHr2.
          apply orb_true_r.
          assumption.
      reflexivity.
Qed.

Lemma repeat_nil :
  forall {A : Type} (n : nat),
    @repeat A n [] = [].
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

Lemma Matches_aux :
  forall
    {A : Type} (dec : A -> A -> bool)
    (l : list A) (r : Regex A),
      Matches l r ->
        forall (h : A) (t : list A),
          l = h :: t -> Matches t (aux dec h r).
Proof.
  induction 1; cbn; intros.
    inv H.
    inv H. cbn. admit.
    destruct l1 as [| h1 t1]; cbn in *.
      subst. specialize (IHMatches2 _ _ eq_refl).
        rewrite <- containsEpsilon_Matches_nil in H. rewrite H. auto.
        inv H1.
    auto.
    auto.
    inv H.
    {
      destruct l1 as [| h1 t1]; inv H1.
      specialize (IHMatches2 _ _ H2).
      inversion IHMatches2; subst.
      constructor.
        assumption.
        assumption.
    }
Admitted.

Lemma Matches_aux' :
  forall
    {A : Type} (dec : A -> A -> bool)
    (h : A) (t : list A) (r : Regex A),
      Matches t (aux dec h r) -> Matches (h :: t) r.
Proof.
  intros until r. revert h t.
  induction r; cbn; intros.
    inv H.
    admit.
    destruct (dec h a) eqn: Hdec.
      inv H. admit.
      inv H.
    inv H.
      inv H2. change (h :: l1 ++ l2) with ((h :: l1) ++ l2). auto.
      destruct (containsEpsilon r1) eqn: H.
        change (h :: t) with ([] ++ (h :: t)). constructor.
          rewrite <- containsEpsilon_Matches_nil. assumption.
          apply IHr2. assumption.
        inv H2.
    inv H.
    inv H.
      change (h :: l1 ++ l2) with ((h :: l1) ++ l2). constructor.
        apply IHr. assumption.
        assumption.
Admitted.

Lemma Matches_brzozowski :
  forall
    {A : Type} (dec : A -> A -> bool)
    (l : list A) (r : Regex A),
      Matches l r ->
        forall l1 l2 : list A, l = rev l1 ++ l2 ->
          Matches l2 (brzozowski dec l1 r).
Proof.
  intros until l1. revert l r H.
  induction l1 as [| h1 t1]; cbn; intros.
    subst. assumption.
    eapply Matches_aux.
      2: reflexivity.
      subst. eapply IHt1.
        2: reflexivity.
        rewrite <- app_assoc in H. cbn in H. assumption.
Qed.

Lemma Matches_brzozowski' :
  forall
    {A : Type} (dec : A -> A -> bool)
    (l1 l2 : list A) (r : Regex A),
      Matches l2 (brzozowski dec l1 r) ->
        Matches (rev l1 ++ l2) r.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    rewrite <- app_assoc. apply IHt1. cbn.
      eapply Matches_aux'. eassumption.
Qed.

Lemma Matches_matches :
  forall
    {A : Type} (dec : A -> A -> bool)
    (l : list A) (r : Regex A),
      Matches l r <-> matches dec l r = true.
Proof.
  split.
    {
      intros. unfold matches.
      rewrite containsEpsilon_Matches_nil.
      eapply Matches_brzozowski.
        exact H.
        rewrite rev_involutive, app_nil_r. reflexivity.
    }
    {
      unfold matches. intros.
      rewrite containsEpsilon_Matches_nil in H.
      apply Matches_brzozowski' in H.
      rewrite rev_involutive, app_nil_r in H.
      assumption.
    }
Qed.