(** Wzięte
    #<a class='link'
        href='http://www.weaselhat.com/2020/05/07/smart-constructors-are-smarter-than-you-think/'>
    stąd</a>#. Definicje wzięte z
    #<a class='link' href='https://en.wikipedia.org/wiki/Brzozowski_derivative'>
    Wikipedii</a>#. Zobacz też
    #<a class='link'
        href='https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html'>
    to</a>#. *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Require Import Recdef Bool.
Require Import List.
Import ListNotations.

Require Import Equality.

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

#[global] Hint Constructors Matches MatchesStar : core.

Scheme Matches_ind' := Induction for Matches Sort Prop.

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
  split.
  - apply Matches_diff'.
  - intro H. eapply Matches_diff; eauto.
Qed.

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

Function seq {A : Type} (r1 r2 : Regex A) : Regex A :=
match r1, r2 with
| Empty  , _       => Empty
| _      , Empty   => Empty
| Epsilon, _       => r2
| _      , Epsilon => r1
| Seq r11 r12, r2  => Seq r11 (Seq r12 r2)
| Or r11 r12, r2   => Or (Seq r11 r2) (Seq r12 r2)
| _      , _       => Seq r1 r2
end.

Function or {A : Type} (r1 r2 : Regex A) : Regex A :=
match r1, r2 with
| Empty, _ => r2
| _, Empty => r1
| Epsilon, _ => if containsEpsilon r2 then r2 else Or r1 r2
| _, Epsilon => if containsEpsilon r1 then r1 else Or r1 r2
| Or r11 r12, r2 => Or r11 (Or r12 r2)
| _, _ => Or r1 r2
end.

Function star {A : Type} (r : Regex A) : Regex A :=
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
  | Seq r11 r12, r2 => Seq r11 (Seq r12 r2)
  | Or r11 r12, r2 => Or (Seq r11 r2) (Seq r12 r2)
  | r1', r2' => Seq r1' r2'
  end
| Or r1 r2 =>
  match optimize r1, optimize r2 with
  | Empty, r2' => r2'
  | r1', Empty => r1'
  | Epsilon, r2' => if containsEpsilon r2' then r2' else Or Epsilon r2'
  | r1', Epsilon => if containsEpsilon r1' then r1' else Or r1' Epsilon
  | Or r11 r12, r2 => Or r11 (Or r12 r2)
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

Lemma optimize_Empty' :
  forall {A : Type} (r : Regex A),
    optimize r = Empty -> forall l : list A, MatchesStar l r -> l = [].
Proof.
  intros A r. unfold not.
  functional induction optimize r; intros H l HM;
  inv H; inv HM;
  repeat match goal with
  | y : match optimize ?r with _ => _ end, H : optimize ?r = Empty |- _ =>
    rewrite H in y; contradiction
  | H : Matches _ ?r, H' : optimize ?r = Empty |- _ =>
    apply optimize_Empty in H; try contradiction; assumption
  | H : Matches _ ?r |- _ => tryif is_var r then idtac else inv H
  end.
Qed.

Lemma optimize_Empty'' :
  forall {A : Type} {r : Regex A},
    optimize r = Empty -> forall l : list A, Matches l r <-> False.
Proof.
  split.
    apply optimize_Empty. assumption.
    destruct 1.
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

Lemma optimize_Epsilon' :
  forall {A : Type} (r : Regex A),
    optimize r = Epsilon -> forall l : list A, MatchesStar l r -> l = [].
Proof.
  intros A r.
  functional induction optimize r; intros H l HM;
  inv H; inv HM;
  repeat match goal with
  | H : Matches _ ?r |- _ =>
    tryif is_var r
    then
      match goal with
      | H' : optimize r = Empty |- _ =>
          apply optimize_Empty in H; [contradiction | assumption]
      | H' : optimize r = Epsilon |- _ =>
          apply optimize_Epsilon in H; [subst; cbn in *; try congruence | assumption]
      end
    else
      inv H
  end.
    apply optimize_Empty' in H3.
      congruence.
      assumption.
    apply IHr0 in H3.
      congruence.
      assumption.
Qed.

Lemma MatchesStar_Empty :
  forall {A : Type} (l : list A) (r : Regex A),
    MatchesStar l Empty -> l = [].
Proof.
  intros. inv H. inv H0.
Qed.

Lemma MatchesStar_app :
  forall {A : Type} (l1 l2 : list A) (r : Regex A),
    MatchesStar l1 r -> MatchesStar l2 r -> MatchesStar (l1 ++ l2) r.
Proof.
  intros until 1. revert l2.
  induction H; cbn; intros.
    assumption.
    rewrite <- app_assoc, app_comm_cons. constructor.
      assumption.
      apply IHMatchesStar. assumption.
Qed.

Lemma MatchesStar_Star :
  forall {A : Type} (l : list A) (r : Regex A),
    MatchesStar l (Star r) <->  MatchesStar l r.
Proof.
  split.
    intro. remember (Star r) as r'. revert r Heqr'. induction H; intros.
      constructor.
      subst. apply MatchesStar_app.
        inv H.
        apply IHMatchesStar. reflexivity.
    induction 1; constructor.
      constructor. replace (h :: t) with ((h :: t) ++ []).
        constructor.
          assumption.
          constructor.
        apply app_nil_r.
      assumption.
Qed.

Lemma Matches_Star :
  forall {A : Type} (l : list A) (r : Regex A),
    Matches l (Star r) <-> MatchesStar l r.
Proof.
  split; intro.
    inv H.
    constructor. assumption.
Qed.

Lemma Matches_Or :
  forall {A : Type} (l : list A) (r1 r2 : Regex A),
    Matches l (Or r1 r2) <-> Matches l r1 \/ Matches l r2.
Proof.
  split; intro H; inv H.
Qed.

Lemma optimize_Epsilon'' :
  forall {A : Type} {r : Regex A},
    optimize r = Epsilon -> forall l : list A, Matches l r <-> l = [].
Proof.
  split.
    apply optimize_Epsilon. assumption.
    intros ->. functional induction optimize r; try inv H; auto.
      change [] with (@nil A ++ []). auto.
      contradiction.
Qed.

Lemma Matches_Epsilon :
  forall {A : Type} (l : list A),
    Matches l Epsilon <-> l = [].
Proof.
  split; intro H.
    inv H.
    subst. constructor.
Qed.

Lemma Matches_optimize :
  forall {A : Type} (l : list A) (r : Regex A),
    (Matches l r <-> Matches l (optimize r))
      /\
    (MatchesStar l r <-> MatchesStar l (optimize r)).
Proof.
  intros. revert l.
  functional induction optimize r; intros.
  1-3: firstorder.
  - split.
    + split; intro H; inv H. contradict H3. apply optimize_Empty. assumption.
    + split; intro H; inv H.
      * inv H0. contradict H4. apply optimize_Empty. assumption.
      * inv H0.
  - split.
    + split; intro H; inv H. contradict H4. apply optimize_Empty. assumption.
    + split; intro H; inv H.
      * inv H0. contradict H5. apply optimize_Empty. assumption.
      * inv H0.
  - destruct (IHr0 l) as [IHr00 IHr01], (IHr1 l) as [IHr10 IHr11]. split.
    + rewrite <- IHr10. split; intro H.
      * inv H. apply optimize_Epsilon in H3; subst; cbn; assumption.
      * change l with ([] ++ l). constructor.
        -- destruct (IHr0 []). rewrite H0, e0. constructor.
        -- assumption.
    + rewrite <- IHr11. split; intro H; inv H.
      * constructor.
        -- inv H0. apply optimize_Epsilon in H4.
            ++ subst. cbn. assumption.
            ++ assumption.
        -- admit.
      * constructor.
        -- admit.
        -- admit.
  - admit.
  - split.
    + split; intro HM; inv HM.
      * destruct (IHr0 l1) as [[] []]. rewrite e0 in *. specialize (H H2). inv H.
        -- rewrite <- app_assoc. constructor.
           ++ assumption.
           ++ constructor.
              ** assumption.
              ** destruct (IHr1 l2). rewrite <- H. assumption.
      * inv H3. rewrite app_assoc. constructor.
        -- destruct (IHr0 (l1 ++ l0)) as [[] []]. apply H0. rewrite e0. constructor; assumption.
        -- destruct (IHr1 l3) as [[] []]. apply H0. assumption.
    + admit. (* nowe *)
  - admit. (* nowe *)
  - split.
    + split; intro H; inv H; constructor.
      * destruct (IHr0 l1). rewrite <- H. assumption.
      * destruct (IHr1 l2). rewrite <- H. assumption.
      * destruct (IHr0 l1). rewrite H. assumption.
      * destruct (IHr1 l2). rewrite H. assumption.
    + admit.
  - split.
    + destruct (IHr0 l), (IHr1 l). rewrite !Matches_Or, <- H1, (optimize_Empty'' e0). firstorder.
    + admit.
  - split.
    + destruct (IHr0 l). rewrite Matches_Or, <- H, (optimize_Empty'' e1). firstorder.
    + admit.
  - split.
    + destruct (IHr1 l). rewrite Matches_Or, <- H, (optimize_Epsilon'' e0). firstorder.
      * subst. apply H2, containsEpsilon_Matches_nil. assumption.
    + admit.
  - split.
    + destruct (IHr1 l). rewrite !Matches_Or, Matches_Epsilon, <- H, (optimize_Epsilon'' e0). reflexivity.
    + admit.
  - split.
		+ destruct (IHr0 l). apply containsEpsilon_Matches_nil in e2.
			* rewrite Matches_Or, (optimize_Epsilon'' e1), H. split; intro; auto.
			  destruct H1; auto. subst. assumption.
		+ admit.
  - split.
		+ destruct (IHr0 l). rewrite !Matches_Or, Matches_Epsilon, <- H, (optimize_Epsilon'' e1). reflexivity.
		+ admit.
  - admit. (* nowe *)
  - split.
		+ destruct (IHr0 l), (IHr1 l). rewrite !Matches_Or, <- H, <- H1. reflexivity.
		+ admit.
  - destruct (IHr0 l) as [IH1 IH2]. split.
		+ rewrite Matches_Star, IH2, e0. split; intro H; inv H. inv H0.
		+ rewrite MatchesStar_Star, IH2, e0. split; intro H; inv H; inv H0.
  - destruct (IHr0 l) as [IH1 IH2]. split.
		+ rewrite Matches_Star, IH2, e0. split; intro H; inv H. inv H0.
		+ rewrite MatchesStar_Star, IH2, e0. reflexivity.
  - destruct (IHr0 l) as [IH1 IH2]. split.
		+ rewrite !Matches_Star, IH2, e0, MatchesStar_Star. reflexivity.
		+ rewrite <- !e0, !MatchesStar_Star, IH2, e0. reflexivity.
  - destruct (IHr0 l) as [IH1 IH2]. split.
		+ rewrite !Matches_Star. assumption.
		+ rewrite !MatchesStar_Star. assumption.
Admitted.

(** Alternatywna implementacja [optimize], tym razem z użyciem smart konstruktorów. *)

Function optimize' {A : Type} (r : Regex A) : Regex A :=
match r with
| Empty => empty
| Epsilon => epsilon
| Char x => char x
| Seq r1 r2 => seq (optimize' r1) (optimize' r2)
| Or r1 r2 => or (optimize' r1) (optimize' r2)
| Star r' => star (optimize' r')
end.

Definition matches''' {A : EqType} (l : list A) (r : Regex A) : bool :=
  containsEpsilon (optimize' (brzozowski' (rev l) r)).

Lemma optimize'_optimize :
  forall {A : EqType} (l : list A) (r : Regex A),
    optimize' r = optimize r.
Proof.
  intros A l r.
  functional induction optimize' r; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHr0, IHr1. destruct (optimize r1), (optimize r2); cbn; reflexivity.
  - rewrite IHr0, IHr1. destruct (optimize r1), (optimize r2); cbn; reflexivity.
  - rewrite IHr0. destruct (optimize r'); cbn; try reflexivity.
Qed.

Lemma Matches_empty :
  forall {A : Type} (l : list A),
    Matches l empty <-> Matches l Empty.
Proof.
  intuition.
Qed.

Lemma Matches_epsilon :
  forall {A : Type} (l : list A),
    Matches l epsilon <-> Matches l Epsilon.
Proof.
  intuition.
Qed.

Lemma Matches_char :
  forall {A : Type} (l : list A) (x : A),
    Matches l (char x) <-> Matches l (Char x).
Proof.
  intuition.
Qed.

Lemma Matches_seq :
  forall {A : Type} (l : list A) (r1 r2 : Regex A),
    Matches l (seq r1 r2) <-> Matches l (Seq r1 r2).
Proof.
  intros.
  functional induction seq r1 r2.
  - split; intro H; inv H. inv H3.
  - split; intro H; inv H. inv H4.
  - split; intro H.
    + change l with ([] ++ l). auto.
    + inv H. inv H3.
  - split; intro H.
    + rewrite <- (app_nil_r l). auto.
    + inv H. inv H4. rewrite app_nil_r. assumption.
  - split; intro H; inv H.
    + inv H4. rewrite app_assoc. auto.
    + inv H3. rewrite <- app_assoc. auto.
  - split; intro H.
    + inv H; inv H2.
    + inv H. inv H3.
  - reflexivity.
Qed.

Lemma Matches_or :
  forall {A : Type} (l : list A) (r1 r2 : Regex A),
    Matches l (or r1 r2) <-> Matches l (Or r1 r2).
Proof.
  intros.
  functional induction or r1 r2.
  - split; intro H; inv H. inv H2.
  - split; intro H; inv H. inv H2.
  - split; intro H.
    + auto.
    + inv H. inv H2. rewrite <- containsEpsilon_Matches_nil. assumption.
  - reflexivity.
  - split; intro H.
    + auto.
    + inv H. inv H2. rewrite <- containsEpsilon_Matches_nil. assumption.
  - reflexivity.
  - split; intro H; inv H; inv H2.
  - reflexivity.
Qed.

Lemma MatchesStar_Star' :
  forall {A : Type} (l : list A) (r : Regex A),
    MatchesStar l (Star r) <-> MatchesStar l r.
Proof.
  split; cycle 1.
  - apply MatchesStar_Star.
Admitted.

Lemma Matches_Star_Star :
  forall {A : Type} (l : list A) (r : Regex A),
    Matches l (Star (Star r)) <-> Matches l (Star r).
Proof.
Admitted.

Lemma Matches_star :
  forall {A : Type} (l : list A) (r : Regex A),
    Matches l (star r) <-> Matches l (Star r).
Proof.
  intros.
  functional induction star r.
  - split; intro H; inv H. inv H2. inv H.
  - split; intro H; inv H. inv H2. inv H.
  - rewrite Matches_Star_Star. reflexivity.
  - reflexivity.
Qed.

Lemma MatchesStar_empty :
  forall {A : Type} (l : list A),
    MatchesStar l empty <-> MatchesStar l Empty.
Proof.
  intuition.
Qed.

Lemma MatchesStar_epsilon :
  forall {A : Type} (l : list A),
    MatchesStar l epsilon <-> MatchesStar l Epsilon.
Proof.
  intuition.
Qed.

Lemma MatchesStar_char :
  forall {A : Type} (l : list A) (x : A),
    MatchesStar l (char x) <-> MatchesStar l (Char x).
Proof.
  intuition.
Qed.

Lemma MatchesStar_seq :
  forall {A : Type} (l : list A) (r1 r2 : Regex A),
    MatchesStar l (seq r1 r2) <-> MatchesStar l (Seq r1 r2).
Proof.
  intros.
  functional induction seq r1 r2.
  - split; intro H; inv H; inv H0. inv H4.
  - split; intro H; inv H; inv H0. inv H5.
  - split; intro H.
    + induction H.
      * auto.
      * constructor.
        -- change (h :: t) with ([] ++ h :: t). auto.
        -- apply IHMatchesStar. destruct r; intuition.
    + admit
    + inv H.
  - admit.
  - split; intro H; inv H.
    + constructor.
Admitted.

Lemma MatchesStar_or :
  forall {A : Type} (l : list A) (r1 r2 : Regex A),
    MatchesStar l (or r1 r2) <-> MatchesStar l (Or r1 r2).
Proof.
  intros.
  functional induction or r1 r2.
  - split; intro H; inv H.
    + constructor. auto.
Admitted.

Lemma MatchesStar_star :
  forall {A : Type} (l : list A) (r : Regex A),
    MatchesStar l (star r) <-> MatchesStar l (Star r).
Proof.
  intros.
  functional induction star r.
  - split; intro H; inv H.
    + inv H0.
    + inv H0. inv H3. inv H2.
  - rewrite MatchesStar_Star. reflexivity.
  - rewrite !MatchesStar_Star. reflexivity.
  - reflexivity.
Qed.

Lemma Matches_optimize' :
  forall {A : Type} (l : list A) (r : Regex A),
    Matches l (optimize' r) <-> Matches l r

with MatchesStar_optimize' :
  forall {A : Type} (l : list A) (r : Regex A),
    MatchesStar l (optimize' r) <-> MatchesStar l r.
Proof.
  intros A l r; revert l.
  functional induction optimize' r; intros l.
  - intuition.
  - intuition.
  - intuition.
  - rewrite Matches_seq. split; intro H.
    + inv H. rewrite IHr0 in H3. rewrite IHr1 in H4. auto.
    + inv H. constructor.
      * rewrite IHr0. assumption.
      * rewrite IHr1. assumption.
  - rewrite Matches_or. split; intro H.
    + inv H.
      * rewrite IHr0 in H2. auto.
      * rewrite IHr1 in H2. auto.
    + inv H.
      * apply MOrL. rewrite IHr0. assumption.
      * apply MOrR. rewrite IHr1. assumption.
  - rewrite Matches_star, !Matches_Star. apply MatchesStar_optimize'.
Abort.

Lemma Matches_optimize' :
  forall {A : Type} (l : list A) (r : Regex A),
    (Matches l (optimize' r) <-> Matches l r)
      /\
    (MatchesStar l (optimize' r) <-> MatchesStar l r).
Proof.
  intros A l r; revert l.
  functional induction optimize' r; intros l.
  - intuition.
  - intuition.
  - intuition.
  - rewrite Matches_seq, MatchesStar_seq. split; split; intro H.
    + inv H. firstorder.
    + inv H. firstorder.
    + admit.
    + inv H. inv H0.
      destruct (IHr0 l1) as [[IH00 IH01] [IH02 IH03]].
      destruct (IHr1 l2) as [[IH10 IH11] [IH12 IH13]].
      firstorder. rewrite H. constructor.
      * rewrite <- H. auto.
      * admit.
  - rewrite Matches_or, MatchesStar_or. split; split; intro H.
    + inv H; firstorder.
    + inv H; firstorder.
    + inv H. constructor.
      * inv H0; firstorder.
      * admit.
    + inv H. constructor.
      * inv H0; firstorder.
      * admit.
  - rewrite Matches_star, MatchesStar_star, !Matches_Star, !MatchesStar_Star; firstorder.
Admitted.

(** Wut? Bardzo podobne do [diff]. *)
Function startsWith {A : Type} (r : Regex A) (a : A) : Prop :=
match r with
| Empty => False
| Epsilon => False
| Char x => a = x
| Seq r1 r2 => startsWith r1 a \/ (containsEpsilon r1 = true /\ startsWith r2 a)
| Or r1 r2 => startsWith r1 a /\ startsWith r2 a
| Star r' => False
end.

Function endsWith {A : Type} (r : Regex A) (b : A) : Prop :=
match r with
| Empty => False
| Epsilon => False
| Char x => x = b
| Seq r1 r2 => endsWith r2 b \/ (containsEpsilon r2 = true /\ endsWith r1 b)
| Or r1 r2 => endsWith r1 b /\ endsWith r2 b
| Star r' => False
end.

Goal
  forall {A : Type} (a b : A) (r : Regex A),
    startsWith r a -> endsWith r b -> a <> b ->
      exists r' : Regex A, forall l : list A,
        Matches l r <-> Matches l (Seq (Char a) (Seq r' (Char b))).
Proof.
  intros A a b r H1 H2 Hneq; revert H2.
  functional induction (startsWith r a); intros.
  - inv H1.
  - inv H1.
  - cbn in H2. congruence.
  - cbn in *. destruct H1, H2.
    + 
Abort.

Goal
  forall {A : Type} (a b : A) (r : Regex A) (l : list A),
    a <> b -> Matches l (Seq (Char a) r) -> Matches l (Seq r (Char b)) -> False.
Proof.
  intros A a b.
  induction r; cbn; intros.
  - inv H0. inv H6.
  - inv H0. inv H6. inv H5. inv H1. inv H4. inv H5. inv H0.
  - inv H0. inv H5. inv H6. inv H1. inv H4. inv H5. inv H0.
  - inv H0; inv H5; inv H6. inv H1; inv H7; inv H6.
    destruct l3; inv H0.
    + destruct l4; inv H2; admit.
    + admit.
  - inv H0; inv H1. inv H5; inv H7. inv H6; inv H4.
    + apply (IHr1 (l0 ++ [b])); [assumption | |].
      * rewrite H0. auto.
      * auto.
    + apply (IHr1 ([a] ++ l2)); [assumption | |].
      * constructor; auto.
      * admit.
    + admit.
    + admit.
  - inv H0. inv H5. inv H6. inv H3.
    + inv H1. inv H5. destruct l1; inv H0. destruct l1; inv H3.
    + inv H1. apply (IHr ([a] ++ (h :: t) ++ l)); [assumption | |].
      * constructor; auto.
Abort.