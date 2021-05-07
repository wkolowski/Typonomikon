(** Zainspirowane przez http://www.weaselhat.com/2020/05/07/smart-constructors-are-smarter-than-you-think/
    Definicje wzięte z https://en.wikipedia.org/wiki/Brzozowski_derivative

    Zobacz też: https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Require Import Bool.
Require Import List.
Import ListNotations.

Inductive Regex (A : Type) : Type :=
    | Empty : Regex A
    | Epsilon : Regex A
    | Char : A -> Regex A
    | Seq : Regex A -> Regex A -> Regex A
    | Or : Regex A -> Regex A -> Regex A
    | Star : Regex A -> Regex A.

Arguments Empty {A}.
Arguments Epsilon {A}.

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
    | MStar :
        forall (l : list A) (r : Regex A),
          MatchesStar l r -> Matches l (Star r)

with MatchesStar {A : Type} : list A -> Regex A -> Prop :=
    | MS_Epsilon :
        forall r : Regex A, MatchesStar [] r
    | MS_Seq :
        forall (h : A) (t l : list A) (r : Regex A),
          Matches (h :: t) r -> MatchesStar l r -> MatchesStar ((h :: t) ++ l) r.

Hint Constructors Matches MatchesStar : core.

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

Class EqType : Type :=
{
    carrier : Type;
    dec : carrier -> carrier -> bool;
    dec_spec : forall x y : carrier, reflect (x = y) (dec x y);
}.

Coercion carrier : EqType >-> Sortclass.

Fixpoint diff
  {A : EqType} (a : A) (r : Regex A)
  : Regex A :=
match r with
    | Empty   => Empty
    | Epsilon => Empty
    | Char x  => if dec a x then Epsilon else Empty
    | Seq r1 r2 =>
        Or (Seq (diff a r1) r2)
           (if containsEpsilon r1
            then diff a r2
            else Empty)
    | Or r1 r2 => Or (diff a r1) (diff a r2)
    | Star r' => Seq (diff a r') (Star r')
end.

Fixpoint brzozowski {A : EqType} (l : list A) (r : Regex A) : Regex A :=
match l with
    | [] => r
    | h :: t => diff h (brzozowski t r)
end.

Definition matches {A : EqType} (l : list A) (r : Regex A) : bool :=
  containsEpsilon (brzozowski (rev l) r).

Ltac inv H := inversion H; subst; clear H; auto.

Lemma containsEpsilon_Matches_nil :
  forall
    {A : Type} (r : Regex A),
      containsEpsilon r = true
        <->
      Matches [] r.
Proof.
  split.
    induction r; cbn; intros; inv H.
      destruct (containsEpsilon r1), (containsEpsilon r2); inv H1.
        change [] with (@nil A ++ []). auto.
      destruct (containsEpsilon r1); cbn in *; auto.
    induction r; cbn; intros; inv H.
      destruct l1, l2; inv H0. rewrite IHr1, IHr2; auto.
      rewrite IHr1; auto.
      rewrite IHr2.
          apply orb_true_r.
          assumption.
Qed.

Lemma Matches_diff :
  forall {A : EqType} (l : list A) (r : Regex A),
    Matches l r ->
      forall (h : A) (t : list A),
        l = h :: t -> Matches t (diff h r)

with MatchesStar_diff :
  forall {A : EqType} (l : list A) (r : Regex A),
    MatchesStar l r ->
      forall (h : A) (t : list A),
        l = h :: t -> Matches t (Seq (diff h r) (Star r)).
Proof.
  destruct 1; cbn; intros h t Heq.
    inv Heq.
    inv Heq. destruct (dec_spec h h).
      constructor.
      contradiction.
    destruct l1 as [| h1 t1]; cbn in *.
      subst. rewrite <- containsEpsilon_Matches_nil in H. rewrite H. eauto.
      inv Heq. eauto.
    eauto.
    eauto.
    eauto.
  destruct 1; cbn; intros h' t' Heq; inv Heq. eauto.
Qed.

Lemma Matches_diff' :
  forall {A : EqType} (h : A) (t : list A) (r : Regex A),
    Matches t (diff h r) -> Matches (h :: t) r.
Proof.
  intros until r. revert h t.
  induction r; cbn; intros.
    inv H.
    inv H.
    destruct (dec_spec h a); inv H.
    inv H.
      inv H2. change (h :: l1 ++ l2) with ((h :: l1) ++ l2). auto.
      destruct (containsEpsilon r1) eqn: H.
        change (h :: t) with ([] ++ (h :: t)). constructor.
          rewrite <- containsEpsilon_Matches_nil. assumption.
          apply IHr2. assumption.
        inv H2.
    inv H.
    inv H. do 2 constructor.
      apply IHr. assumption.
      inv H4.
Qed.

Lemma Matches_diff'' :
  forall {A : EqType} (h : A) (t : list A) (r : Regex A),
    Matches t (diff h r) <-> Matches (h :: t) r.
Proof.
Admitted.

Lemma Matches_brzozowski :
  forall {A : EqType} (l : list A) (r : Regex A),
    Matches l r ->
      forall l1 l2 : list A, l = rev l1 ++ l2 ->
        Matches l2 (brzozowski l1 r).
Proof.
  intros until l1. revert l r H.
  induction l1 as [| h1 t1]; cbn; intros.
    subst. assumption.
    eapply Matches_diff.
      2: reflexivity.
      subst. eapply IHt1.
        2: reflexivity.
        rewrite <- app_assoc in H. cbn in H. assumption.
Qed.

Lemma Matches_brzozowski' :
  forall {A : EqType} (l1 l2 : list A) (r : Regex A),
    Matches l2 (brzozowski l1 r) ->
      Matches (rev l1 ++ l2) r.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    rewrite <- app_assoc. apply IHt1. cbn.
      eapply Matches_diff'. eassumption.
Qed.

Lemma Matches_brzozowski'' :
  forall {A : EqType} (l1 l2 : list A) (r : Regex A),
    Matches l2 (brzozowski l1 r)
      <->
    Matches (rev l1 ++ l2) r.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite Matches_diff'', IHt1, <- app_assoc. cbn. reflexivity.
Qed.

Lemma Matches_matches :
  forall {A : EqType} (l : list A) (r : Regex A),
    Matches l r <-> matches l r = true.
Proof.
  intros. unfold matches.
  rewrite containsEpsilon_Matches_nil.
  rewrite Matches_brzozowski''.
  rewrite rev_involutive, app_nil_r.
  reflexivity.
Qed.

Require Import Equality.

Scheme Matches_ind' := Induction for Matches Sort Prop.

(* Not true. *)
Lemma isProp_Matches :
  forall
    {A : Type} (l : list A) (r : Regex A)
    (m1 m2 : Matches l r),
      m1 ~= m2.
Proof.
  induction m1 using @Matches_ind'; intros.
    dependent destruction m2. reflexivity.
    dependent destruction m2. reflexivity.
    dependent destruction m2. rewrite <- x.
Abort.

Fixpoint repeat {A : Type} (n : nat) (x : A) : list A :=
match n with
    | 0    => []
    | S n' => x :: repeat n' x
end.

(* 0.001 sec *)
(* Time Compute matches eqb (repeat 10 true) (Star (Char true)). *)

(* 1.9 sec *)
(* Time Compute matches eqb (repeat 20 true) (Star (Char true)). *)

(* timeout *)
(* Time Compute matches eqb (repeat 30 true) (Star (Char true)). *)

(* * Same thing, but using smart constructors. *)

Definition empty {A : Type} : Regex A := Empty.

Definition epsilon {A : Type} : Regex A := Epsilon.

Definition char {A : Type} (x : A) : Regex A := Char x.

Definition seq {A : Type} (r1 r2 : Regex A) : Regex A :=
match r1, r2 with
    | Empty  , _       => Empty
    | _      , Empty   => Empty
    | Epsilon, _       => r2
    | _      , Epsilon => r1
    | _      , _       => Seq r1 r2
end.

Definition or {A : Type} (r1 r2 : Regex A) : Regex A :=
match r1, r2 with
    | Empty, _ => r2
    | _, Empty => r1
    | Epsilon, _ => if containsEpsilon r2 then r2 else Or r1 r2
    | _, Epsilon => if containsEpsilon r1 then r1 else Or r1 r2
    | _, _ => Or r1 r2
end.

Definition star {A : Type} (r : Regex A) : Regex A :=
match r with
    | Empty => Epsilon
    | Epsilon => Epsilon
    | Star r' => Star r'
    | _ => Star r
end.

Fixpoint diff' {A : EqType} (a : A) (r : Regex A) : Regex A :=
match r with
    | Empty   => empty
    | Epsilon => empty
    | Char x  => if dec a x then epsilon else empty
    | Seq r1 r2 =>
        or (seq (diff' a r1) r2)
           (if containsEpsilon r1
            then diff' a r2
            else empty)
    | Or r1 r2 => or (diff' a r1) (diff' a r2)
    | Star r' => seq (diff' a r') (star r')
end.

Fixpoint brzozowski'
  {A : EqType} (l : list A) (r : Regex A) : Regex A :=
match l with
    | [] => r
    | h :: t => diff' h (brzozowski' t r)
end.

Definition matches' {A : EqType} (l : list A) (r : Regex A) : bool :=
  containsEpsilon (brzozowski' (rev l) r).


(* Time Compute matches' eqb (repeat 10 true) (Star (Char true)). *)
(* ===> Finished transaction in 0. secs (0.u,0.s) (successful) *)

(* Time Compute matches' eqb (repeat 20 true) (Star (Char true)). *)
(* ===> Finished transaction in 0. secs (0.u,0.s) (successful) *)

(* Time Compute matches' eqb (repeat 40 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.001 secs (0.001u,0.s) (successful) *)

(* Time Compute matches' eqb (repeat 80 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.001 secs (0.u,0.001s) (successful) *)

(* Time Compute matches' eqb (repeat 160 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.003 secs (0.002u,0.001s) (successful) *)

(* Time Compute matches' eqb (repeat 320 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.013 secs (0.007u,0.001s) (successful) *)

(* Time Compute matches' eqb (repeat 640 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.046 secs (0.024u,0.002s) (successful) *)

(* Time Compute matches' eqb (repeat 1280 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.125 secs (0.063u,0.002s) (successful) *)

(* Time Compute matches' eqb (repeat 2560 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.305 secs (0.191u,0.001s) (successful) *)

(* Time Compute matches' eqb (repeat 5120 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.984 secs (0.694u,0.004s) (successful) *)

Require Import FunInd.

Function optimize {A : Type} (r : Regex A) : Regex A :=
match r with
    | Empty => Empty
    | Epsilon => Epsilon
    | Char x => Char x
    | Seq r1 r2 =>
        match optimize r1, optimize r2 with
            | Empty, _ => Empty
            | _, Empty => Empty
            | Epsilon, r2' => r2'
            | r1', Epsilon => r1'
            | r1', r2' => Seq r1' r2'
        end
    | Or r1 r2 =>
        match optimize r1, optimize r2 with
            | Empty, r2' => r2'
            | r1', Empty => r1'
            | Epsilon, r2' => if containsEpsilon r2' then r2' else Or Epsilon r2'
            | r1', Epsilon => if containsEpsilon r1' then r1' else Or r1' Epsilon
            | r1', r2' => Or r1' r2'
        end
    | Star r' =>
        match optimize r' with
            | Empty => Epsilon
            | Epsilon => Epsilon
            | Star r'' => Star r''
            | r'' => Star r''
        end
end.

Definition matches'' {A : EqType} (l : list A) (r : Regex A) : bool :=
  containsEpsilon (optimize (brzozowski' (rev l) r)).

(* Time Compute matches'' eqb (repeat 5120 true) (Star (Char true)). *)
(* ===> Finished transaction in 0.733 secs (0.594u,0.001s) (successful) *)

(* Time Compute matches'' eqb (repeat 10240 true) (Star (Char true)). *)
(* ===> Finished transaction in 4.028 secs (2.599u,0.051s) (successful) *)

Lemma optimize_Empty :
  forall {A : Type} (r : Regex A),
    optimize r = Empty -> forall l : list A, ~ Matches l r.
Proof.
  intros A r. unfold not.
  functional induction optimize r; intros H l HM;
  inv H; inv HM; eauto.
    rewrite H1 in y. contradiction.
    rewrite H1 in y. contradiction.
Qed.

Lemma optimize_Epsilon :
  forall {A : Type} (r : Regex A),
    optimize r = Epsilon -> forall l : list A, Matches l r -> l = [].
Proof.
  intros A r.
  functional induction optimize r; intros H l HM;
  inv H; inv HM; eauto.
    rewrite (IHr0 e0 _ H3), (IHr1 H1 _ H4). reflexivity.
    rewrite (IHr0 H1 _ H3), (IHr1 e1 _ H4). reflexivity.
    contradict H2. apply optimize_Empty. assumption.
    contradict H2. apply optimize_Empty. assumption.
    inv H1. apply optimize_Empty in H.
      contradiction.
      assumption.
    inv H1. apply IHr0 in H.
      inv H.
      assumption.
Qed.

Lemma MatchesStar_optimize :
  forall {A : Type} (l : list A) (r : Regex A),
    MatchesStar l r <-> MatchesStar l (optimize r).
Proof.
  intros. revert l.
  functional induction optimize r; cbn; intros.
    1-3: firstorder.
    admit.
    admit.
Abort.

Lemma Matches_optimize :
  forall {A : Type} (l : list A) (r : Regex A),
    Matches l r -> Matches l (optimize r)

with MatchesStar_optimize :
  forall {A : Type} (l : list A) (r : Regex A),
    MatchesStar l r -> MatchesStar l (optimize r).
Proof.
  destruct 1; cbn.
    constructor.
    constructor.
Abort.

Lemma Matches_optimize :
  forall {A : Type} (l : list A) (r : Regex A),
    (Matches l r <-> Matches l (optimize r))
      /\
    (MatchesStar l r <-> MatchesStar l (optimize r)).
Proof.
  intros. revert l.
  functional induction optimize r; intros.
  Focus 18. split.
    split; intro H; inv H.
      inv H2. do 2 constructor.
        
      destruct (IHr0 l). rewrite <- e0, <- H. constructor. rewrite  rewrite H0, e0 in H2. constructor. assumption.
      constructor.
    1-3: firstorder.
    split; intro H; inv H. contradict H3. apply optimize_Empty. assumption.
    split; intro H; inv H. contradict H4. apply optimize_Empty. assumption.
    rewrite <- IHr1. split; intro H.
      inv H. apply optimize_Epsilon in H3; subst; cbn; assumption.
      change l with ([] ++ l). constructor.
        rewrite IHr0, e0. constructor.
        assumption.
    rewrite <- IHr0. split; intro H.
      inv H. apply optimize_Epsilon in H4; subst; cbn.
        rewrite app_nil_r. assumption.
        assumption.
      rewrite <- (@app_nil_r A l). constructor.
        assumption.
        rewrite IHr1, e1. constructor.
    split; intro H; inv H; constructor; rewrite <- ?IHr0, <- ?IHr1 in *; assumption.
    rewrite <- IHr1. split; intro H; inv H. apply optimize_Empty in H2; firstorder.
    rewrite <- IHr0. split; intro H; inv H. apply optimize_Empty in H2; firstorder.
    rewrite <- IHr1. split; intro H; inv H. apply optimize_Epsilon in H2; subst.
      rewrite IHr1, <- containsEpsilon_Matches_nil. assumption.
      assumption.
    split; intro H; inv H.
      constructor. apply optimize_Epsilon in H2; subst; auto.
      constructor 5. rewrite <- IHr1. auto.
      constructor. rewrite IHr0, e0. assumption.
      constructor 5. rewrite IHr1. assumption.
    rewrite <- IHr0. split; intro H.
      inv H. apply optimize_Epsilon in H2; subst; auto.
        rewrite containsEpsilon_Matches_nil, <- IHr0 in e2. assumption.
      constructor. assumption.
    split; intro H; inv H.
      constructor. rewrite <- IHr0. assumption.
      constructor 5. apply optimize_Epsilon in H2; subst; auto.
      constructor. rewrite IHr0. assumption.
      constructor 5. rewrite IHr1, e1. assumption.
    split; intro H; inv H.
      constructor. rewrite <- IHr0. assumption.
      constructor 5. rewrite <- IHr1. assumption.
      constructor. rewrite IHr0. assumption.
      constructor 5. rewrite IHr1. assumption.
    split; intro H; inv H. inv H2. rewrite IHr0, e0 in H. inv H.
    split; intro H; inv H. inv H2. rewrite IHr0, e0 in H. inv H.
    admit.
    split; intro H; inv H.
      constructor.
Abort.