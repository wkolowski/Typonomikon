(** * D5: Więcej zabaw z listami [TODO] *)

(* begin hide *)
(*
TODO 1: przenieś [intersperse] na sam koniec funkcji i dorzuć jeszcze
TODO 1: kilka dziwnych (z niestandardowym kształtem indukcji)
TODO 2: opisz niestandardowe reguły indukcyjne dla list (najlepiej przed
TODO 2: funkcją [intersperse])
TODO 3: opisz foldy ([fold] i [foldl]), łączac je z regułami indukcji
TODO 4: opisz sumy prefiksowe (`scanr` i `scanl`)
TODO 5: zrób osobno: funkcje na listach dla typów mających jakieś
TODO 6: specjalne rzeczy (np. rozstrzygalną równość)
TODO 7: ćwiczenia z przetwarzania danych, typu znajdź wszystkie liczby
TODO 7: nieparzyste większe od x, których suma cyfr to dupa konia.
TODO 8: niektóre niedokończone funkcje dla list:
  - isZero (przenieść do rozdziału o arytmetyce)
  - isEmpty
  - snoc
  - bind
  - iterate (od removeFirst wzwyż) i iter (join, bind)
  - insert (join, bind, iterate, init)
  - remove
  - take (join, bind, last_take, take_remove),
  - drop (join, bind, remove)
  - removeFirst (removeFirst_zip)
  - findIndex (init, tail)
  - filter (tail, init)
  - findIndices (join, bind, takeWhile, dropWhile)
  - pmap (iterate, nth, last, tail i init, take i drop, takedrop, zip,
    unzip, zipWith, unzipWith, removeFirst i removeLast, findIndex,
    findIndices)
  - intersperse (init, insert, remove, drop, zip, zipWith, unzip)
  - groupBy
  - Rep (join, nth)
  - AtLeast (nth, head, last, init, tail)
  - Exactly (join, nth, head, tail, init, last, zip)
  - AtMost
  - popracować nad `findIndices` (i to w dwóch wersjach - być może jest to
    dobry pretekst dla wprowadzenia stylu programowania z akumulatorem?)
TODO 9: Dokończyć prace nad resztą rzeczy z folderu List/.
TODO 10: opisać encode-decode dla (nie)równości na typach induktywnych.
TODO 11: poszukać ogólnego pojęcia "różnicy" typów.
*)
(* end hide *)

From Typonomikon Require Export D5d.

(** * Permutacje (TODO) *)

(** ** Permutacje jako ciągi transpozycji *)

Module Transpositions.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_refl : forall l : list A, Perm l l
| Perm_transp :
    forall (x y : A) (l1 l2 l3 l4 : list A),
      Perm (l1 ++ x :: l2 ++ y :: l3) l4 ->
        Perm (l1 ++ y :: l2 ++ x :: l3) l4.

Lemma Perm_cons :
  forall {A : Type} (h : A) (t1 t2 : list A),
    Perm t1 t2 -> Perm (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply (Perm_transp x y (h :: l1)). cbn. assumption.
Qed.
(* end hide *)

Lemma Perm_trans :
  forall {A : Type} {l1 l2 l3 : list A},
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  induction 1; intro.
    assumption.
    constructor. apply IHPerm. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_transp x y [] []). cbn. constructor.
    eapply Perm_trans; eassumption.
Qed.
(* end hide *)

Lemma Permutation_transpose :
  forall {A : Type} {x y : A} {l1 l2 l3 : list A},
    Permutation (l1 ++ x :: l2 ++ y :: l3) (l1 ++ y :: l2 ++ x :: l3).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    {
      change (x :: l2 ++ y :: l3) with ((x :: l2) ++ y :: l3).
      change (y :: l2 ++ x :: l3) with ((y :: l2) ++ x :: l3).
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite (Permutation_app_comm _ l3).
      rewrite (Permutation_app_comm _ l2).
      cbn. constructor.
      apply Permutation_app_comm.
    }
    constructor. apply IHt1.
Qed.
(* end hide *)

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite Permutation_transpose. assumption.
Qed.
(* end hide *)

End Transpositions.

(** ** Permutacje jako ciągi transpozycji v2 *)

Module InductiveTranspositions.

Inductive Transposition {A : Type} : list A -> list A -> Prop :=
| Transposition' :
    forall (l1 : list A) (x : A) (l2 : list A) (y : A) (l3 : list A),
      Transposition (l1 ++ x :: l2 ++ y :: l3) (l1 ++ y :: l2 ++ x :: l3).

Inductive Transposition2 {A : Type} : list A -> list A -> Prop :=
| Transposition2' :
    forall (l1 : list A) (x : A) (l2 : list A) (y : A) (l3 r1 r2: list A),
      r1 = l1 ++ x :: l2 ++ y :: l3 ->
      r2 = l1 ++ y :: l2 ++ x :: l3 ->
        Transposition2 r1 r2.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_refl : forall l : list A, Perm l l
| Perm_step_trans :
    forall l1 l2 l3 : list A,
      Transposition l1 l2 -> Perm l2 l3 -> Perm l1 l3.

Lemma Perm_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Perm l1 l2 -> Perm (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    eapply Perm_step_trans.
      2: eassumption.
      destruct H as [l11 y l12 z l13].
        apply (Transposition' (x :: l11) y l12 z l13).
Qed.
(* end hide *)

Lemma Perm_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  intros until 1. revert l3.
  induction H; intros.
    assumption.
    econstructor.
      exact H.
      apply IHPerm. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_step_trans _ (x :: y :: l)).
      apply (Transposition' [] y [] x l).
      constructor.
    eapply Perm_trans; eassumption.
Qed.
(* end hide *)

Lemma Perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite <- IHPerm. destruct H as [l11 x l12 y l13].
      apply Transpositions.Permutation_transpose.
Qed.
(* end hide *)

Lemma Perm_spec :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 <-> Permutation l1 l2.
(* begin hide *)
Proof.
  split.
    apply Perm_Permutation.
    apply Permutation_Perm.
Qed.
(* end hide *)

Lemma Perm_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Perm l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite <- IHPerm. destruct H as [l11 x l12 y l13].
      repeat (rewrite count_app; cbn).
      destruct (p x), (p y); rewrite ?plus_n_Sm; reflexivity.
Qed.
(* end hide *)

End InductiveTranspositions.

(** ** Permutacje jako ciągi transpozycji elementów sąsiednich *)

Module AdjacentTranspositions.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_refl : forall l : list A, Perm l l
| Perm_steptrans :
    forall (x y : A) (l1 l2 l3 : list A),
      Perm (l1 ++ y :: x :: l2) l3 -> Perm (l1 ++ x :: y :: l2) l3.

Lemma Perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    apply Permutation_refl.
    rewrite <- IHPerm. apply Permutation_app.
      reflexivity.
      constructor.
Qed.
(* end hide *)

Lemma Perm_cons :
  forall {A : Type} (x : A) {l1 l2 : list A},
    Perm l1 l2 -> Perm (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply (Perm_steptrans x0 y (x :: l1) l2). cbn. assumption.
Qed.
(* end hide *)

Lemma Perm_trans :
  forall {A : Type} {l1 l2 l3 : list A},
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  induction 1; intro H23.
    assumption.
    apply (Perm_steptrans x y l1 l2), IHPerm, H23.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_steptrans y x [] l). cbn. constructor.
    eapply Perm_trans; eassumption.
Qed.
(* end hide *)

End AdjacentTranspositions.

(** ** Permutacje jako ciągi transpozycji elementów sąsiednich v2 *)

Module Exchange.

Definition exchange {A : Type} (l1 l2 : list A) : Prop :=
  exists (x y : A) (r1 r2 : list A),
    l1 = r1 ++ x :: y :: r2 /\
    l2 = r1 ++ y :: x :: r2.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_refl : forall l : list A, Perm l l
| Perm_step_trans :
    forall l1 l2 l3 : list A,
      exchange l1 l2 -> Perm l2 l3 -> Perm l1 l3.

Lemma Perm_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Perm l1 l2 -> Perm (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    destruct H as (y & z & r1 & r2 & eq1 & eq2); subst.
      apply (Perm_step_trans) with (x :: r1 ++ z :: y :: r2).
        red. exists y, z, (x :: r1), r2. split; reflexivity.
        assumption.
Qed.
(* end hide *)

Lemma Perm_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  intros until 1. revert l3.
  induction H; intros.
    assumption.
    econstructor.
      exact H.
      apply IHPerm. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_step_trans _ (x :: y :: l)).
      red. exists y, x, [], l. cbn. split; trivial.
      apply Perm_refl.
    apply Perm_trans with l'; assumption.
Qed.
(* end hide *)

Lemma Perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite <- IHPerm.
      destruct H as (x & y & r1 & r2 & eq1 & eq2). subst.
      apply Permutation_app_l. constructor.
Qed.
(* end hide *)

Lemma Perm_spec :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 <-> Permutation l1 l2.
(* begin hide *)
Proof.
  split.
    apply Perm_Permutation.
    apply Permutation_Perm.
Qed.
(* end hide *)

Lemma Perm_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Perm l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    destruct H as (x & y & r1 & r2 & eq1 & eq2). subst.
      rewrite <- IHPerm, !count_app. f_equal. cbn.
      destruct (p x), (p y); reflexivity.
Qed.
(* end hide *)

End Exchange.

(** ** Permutacje za pomocą liczenia właściwości *)

Module Exactly.

Ltac inv H := inversion H; subst; clear H.

Definition Perm {A : Type} (l1 l2 : list A) : Prop :=
  forall (P : A -> Prop) (n : nat),
    Exactly P n l1 <-> Exactly P n l2.

Lemma Permutation_Exactly :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat),
        Exactly P n l1 -> Exactly P n l2.
(* begin hide *)
Proof.
  induction 1; intros.
    assumption.
    inv H0.
      constructor.
        assumption.
        apply IHPermutation. assumption.
      constructor 3.
        assumption.
        apply IHPermutation. assumption.
    inv H.
      inv H4; repeat constructor; assumption.
      inv H4; repeat constructor; assumption.
    apply IHPermutation2, IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  split.
    apply Permutation_Exactly. assumption.
    apply Permutation_Exactly. symmetry. assumption.
Qed.
(* end hide *)

Lemma Perm_front_ex :
  forall {A : Type} {h : A} {t l : list A},
    Perm (h :: t) l ->
      exists l1 l2 : list A,
        l = l1 ++ h :: l2 /\ Perm t (l1 ++ l2).
(* begin hide *)
Proof.
  intros until 1.
  revert h t H.
  induction l as [| h' t']; intros.
    admit.
    unfold Perm in H.
Admitted.
(* end hide *)

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; intros.
    destruct l2 as [| h2 t2].
      constructor.
      {
        unfold Perm in H. destruct (H (fun x => x = h2) 0).
        rewrite Exactly_0_cons in *.
        destruct (H0 ltac:(constructor)).
        contradiction.
      }
    {
      apply Perm_front_ex in H.
      destruct H as (l1 & l3 & H1 & H2). subst.
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite Permutation_app_comm.
      apply IHt1.
      assumption.
    }
Qed.
(* end hide *)

End Exactly.

(** ** Permutacje za pomocą liczenia właściwości v2 *)

Module AtLeast.

Ltac inv H := inversion H; subst; clear H.

Definition Perm {A : Type} (l1 l2 : list A) : Prop :=
  forall (P : A -> Prop) (n : nat),
    (AtLeast P n l1 <-> AtLeast P n l2).

#[global] Hint Constructors AtLeast : core.

Lemma Permutation_AtLeast :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat),
        AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; intros.
    assumption.
    inv H0; auto.
    inv H.
      auto.
      inv H4; auto.
      inv H2; auto.
    apply IHPermutation2, IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  split.
    apply Permutation_AtLeast. assumption.
    apply Permutation_AtLeast. symmetry. assumption.
Qed.
(* end hide *)

Lemma AtLeast_1 :
  forall {A : Type} {P : A -> Prop} {l : list A},
    AtLeast P 1 l ->
      exists (x : A) (l1 l2 : list A),
        P x /\ l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  induction l as [| h t]; intros.
    inv H.
    inv H.
      exists h, [], t. auto.
      destruct (IHt H2) as (x & l1 & l2 & IH1 & IH2).
        subst. exists x, (h :: l1), l2. auto.
Qed.
(* end hide *)

Lemma AtLeast_app_comm' :
  forall {A : Type} {P : A -> Prop} {n : nat} {l1 l2 : list A},
    AtLeast P n (l1 ++ l2) <-> AtLeast P n (l2 ++ l1).
(* begin hide *)
Proof.
  split; intro; apply AtLeast_app_comm; assumption.
Qed.
(* end hide *)

Lemma AtLeast_cons_app :
  forall
    {A : Type} {P : A -> Prop} {n : nat}
    (x : A) (l1 l2 : list A),
      AtLeast P n (l1 ++ x :: l2) <->
      AtLeast P n (x :: l1 ++ l2).
(* begin hide *)
Proof.
  intros.
  change (x :: l1 ++ l2) with ((x :: l1) ++ l2).
  rewrite AtLeast_app_comm'. cbn.
  rewrite !AtLeast_cons.
  rewrite !(@AtLeast_app_comm' _ _ _ l1 l2).
  reflexivity.
Qed.
(* end hide *)

Lemma Perm_front_ex :
  forall {A : Type} {h : A} {t l : list A},
    Perm (h :: t) l ->
      exists l1 l2 : list A,
        l = l1 ++ h :: l2 /\ Perm t (l1 ++ l2).
(* begin hide *)
Proof.
  intros.
  unfold Perm in H.
  assert (AtLeast (fun x => x = h) 1 l).
    apply H. auto.
  apply AtLeast_1 in H0.
  destruct H0 as (x & l1 & l2 & H1 & H2); subst.
  exists l1, l2.
  split.
    reflexivity.
    {
      red. intros.
      destruct (H P n).
      destruct (H P (S n)).
      firstorder.
        specialize (H0 ltac:(auto)).
        specialize (H1 H0).
        inv H1.
          auto.
          apply AtLeast_cons' with h.
            apply AtLeast_cons_app. apply H2. auto.
          assert (AtLeast P n (h :: l1 ++ l2)).
            apply AtLeast_cons_app. auto.
            inv H1.
              auto.
              apply AtLeast_cons' with h.
                apply AtLeast_cons_app. apply H2. auto.
              assumption.
          assert (AtLeast P n (h :: t)).
            apply H1. apply AtLeast_cons_app. constructor. assumption.
            inv H5.
              auto.
              apply AtLeast_cons' with h. apply H3.
                apply AtLeast_app_comm. cbn. constructor.
                  assumption.
                  apply AtLeast_app_comm. assumption.
              assumption.
    }
Qed.
(* end hide *)

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; intros.
    destruct l2 as [| h2 t2].
      constructor.
      {
        unfold Perm in H. destruct (H (fun x => x = h2) 1).
        specialize (H1 ltac:(auto)). inv H1.
      }
    { unfold Perm in H.
      apply Perm_front_ex in H.
      destruct H as (l1 & l3 & H1 & H2). subst.
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite Permutation_app_comm.
      apply IHt1.
      assumption.
    }
Qed.
(* end hide *)

#[global] Hint Constructors Exactly : core.

(* TODO *) Lemma AtLeast_Exactly :
  forall {A : Type} (l1 l2 : list A),
    (forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 <-> AtLeast P n l2)
    <->
    (forall (P : A -> Prop) (n : nat),
      Exactly P n l1 <-> Exactly P n l2).
(* begin hide *)
Proof.
  split.
    split; intros.
      induction H0.
        destruct l2.
          auto.
          destruct (H (fun x => x = a) 1).
            specialize (H1 ltac:(auto)). inv H1.
Abort.
(* end hide *)

End AtLeast.

(** ** Permutacje, jeszcze dziwniej *)

Require Import Equality.

Module PermWeird.

(* Import H2z. *)

Inductive Elem {A : Type} (x : A) : list A -> Type :=
| Z : forall l : list A, Elem x (x :: l)
| S : forall {t : list A}, Elem x t -> forall h : A, Elem x (h :: t).

Arguments Z {A x} _.
Arguments S {A x t} _ _.

(** TODO: iso skopiowane z rozdziału o izomorfizmach typów. *)

Class iso (A B : Type) : Type :=
{
  coel : A -> B;
  coer : B -> A;
  coel_coer :
    forall a : A, coer (coel a) = a;
  coer_coel :
    forall b : B, coel (coer b) = b;
}.

Arguments coel {A B} _.
Arguments coer {A B} _.

Definition Perm {A : Type} (l1 l2 : list A) : Type :=
  forall x : A, iso (Elem x l1) (Elem x l2).

(* begin hide *)
(*Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    red. intro. split with (coel := id) (coer := id).
      1-2: reflexivity.
    red. intro y. unfold Perm in *. destruct (IHPermutation y).
      esplit. Unshelve. all: cycle 4. 1-4: intro H'.
        inv H'.
          left.
          right. apply coel. assumption.
        inv H'.
          left.
          right. apply coer. assumption.
        dependent induction H'; cbn; congruence.
        dependent induction H'; cbn; congruence.
    red. intro z. esplit. Unshelve. all: cycle 3. 1-4: intro H'.
        inv H'.
          right. left.
          inv X.
            left.
            right. right. assumption.
        inv H'.
          right. left.
          inv X.
            left.
            right. right. assumption.
        do 2 (dependent induction H'; cbn; try congruence).
        do 2 (dependent induction H'; cbn; try congruence).
    intro H'. eapply iso_trans.
      apply IHPermutation1.
      apply IHPermutation2.
Qed.
 *)

(* Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  unfold Perm.
  induction l1 as [| h1 t1]; intros.
    destruct l2 as [| h2 t2].
      constructor.
      specialize (H h2). destruct H.
        clear -coer. specialize (coer ltac:(left)). inv coer.
    destruct l2 as [| h2 t2].
      specialize (H h1). destruct H.
        clear -coel. specialize (coel ltac:(left)). inv coel.
Admitted.
 *)
(* end hide *)

End PermWeird.

(** ** Permutacje za pomocą liczenia właściwości rozstrzygalnych *)

Module Count.

Definition perm {A : Type} (l1 l2 : list A) : Prop :=
  forall p : A -> bool, count p l1 = count p l2.

Lemma count_ex :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p l = 0 \/
    exists (x : A) (l1 l2 : list A),
      p x = true /\ l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    left. reflexivity.
    destruct IHt.
      destruct (p h) eqn: Hph.
        right. exists h, [], t. split; trivial.
        left. assumption.
      destruct H as (x & l1 & l2 & eq1 & eq2); subst.
        destruct (p h) eqn: Hph.
          right. exists h, [], (l1 ++ x :: l2). split; trivial.
          right. exists x, (h :: l1), l2. cbn. split; trivial.
Qed.
(* end hide *)

Import Exchange.

Lemma Perm_perm :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> perm l1 l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    red. reflexivity.
    destruct H as (x & y & r1 & r2 & eq1 & eq2); subst.
      unfold perm in *. intro. rewrite <- (IHPerm p).
      rewrite 2!count_app. cbn.
      destruct (p x), (p y); reflexivity.
Qed.
(* end hide *)

Lemma perm_Perm :
  forall (A : Type) (l1 l2 : list A),
    perm l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  intros. apply Permutation_Perm.
  apply Permutation_count_conv. exact H.
Qed.
(* end hide *)

End Count.

(** ** Permutacje przez wstawianie *)

Module Insert.

Inductive Insert {A : Type} (x : A) : list A -> list A -> Type :=
| Insert_here :
    forall l : list A, Insert x l (x :: l)
| Insert_there :
    forall (h : A) (t t' : list A), Insert x t t' -> Insert x (h :: t) (h :: t').

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_nil    : Perm [] []
| Perm_Insert :
    forall (x : A) (l1 l1' l2 l2' : list A),
      Insert x l1 l1' -> Insert x l2 l2' -> Perm l1 l2 -> Perm l1' l2'.

#[global] Hint Constructors Insert Perm : core.

Lemma Perm_refl :
  forall {A : Type} (l : list A),
    Perm l l.
Proof.
  induction l as [| h t]; econstructor; eauto.
Qed.

Lemma Perm_Insert' :
  forall {A : Type} (x : A) (l1 l2 : list A),
    Insert x l1 l2 -> Perm (x :: l1) l2.
Proof.
  induction 1.
    apply Perm_refl.
    econstructor; eauto. apply Perm_refl.
Qed.

Lemma Perm_trans :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> forall l3 : list A, Perm l2 l3 -> Perm l1 l3.
Proof.
  intros until 2. revert l1 H.
  induction H0; intros.
    assumption.
    {
      revert x l1 l2 l2' X X0 H0 IHPerm.
      induction H; intros.
        inv X.
        {
          apply Perm_Insert' in X.
          apply Perm_Insert' in X0.
          apply Perm_Insert' in X1.
          apply Perm_Insert' in X2.
Admitted.

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    constructor.
    econstructor; eauto.
    econstructor; eauto. apply Perm_refl.
    eapply Perm_trans; eassumption.
Qed.

Lemma Permutation_Insert :
  forall {A : Type} (x : A) (l1 l2 : list A),
    Insert x l1 l2 -> Permutation (x :: l1) l2.
Proof.
  induction 1.
    reflexivity.
    econstructor; eauto.
Qed.

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  induction 1.
    reflexivity.
    {
      apply Permutation_Insert in X.
      apply Permutation_Insert in X0.
      rewrite <- X, <- X0.
      constructor.
      assumption.
    }
Qed.

End Insert.

(** ** Permutacje przez wstawianie v2 (TODO) *)

Module Insert2.

(* Inductive Insert {A : Type} (x : A) : list A -> list A -> Type :=
| Insert_here :
    forall l : list A, Insert x l (x :: l)
| Insert_there :
    forall (h : A) (t t' : list A), Insert x t t' -> Insert x (h :: t) (h :: t').
 *)

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_nil    : Perm [] []
| Perm_insert :
    forall (x : A) (l1 l2 r1 r2 : list A),
      Perm (l1 ++ l2) (r1 ++ r2) -> Perm (l1 ++ x :: l2) (r1 ++ x :: r2).

#[global] Hint Constructors Perm : core.

Lemma Perm_refl :
  forall {A : Type} (l : list A),
    Perm l l.
Proof.
  induction l as [| h t].
    constructor.
    apply (Perm_insert h [] t [] t). cbn. assumption.
Qed.

Lemma Perm_sym :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Perm l2 l1.
Proof.
  induction 1.
    constructor.
    constructor. assumption.
Qed.

Lemma Perm_trans :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> forall l3 : list A, Perm l2 l3 -> Perm l1 l3.
Proof.
  intros until 2.
  revert l1 H.
  induction H0; intros.
    assumption.
    inv H.
      apply (f_equal length) in H3. rewrite length_app in H3. cbn in H3. lia.
Restart.
  induction 1 as [| x l1 l2 r1 r2 H12 IH].
    intros. assumption.
    {
      intros l3 H23. remember (r1 ++ x :: r2) as MID.
      revert l1 l2 H12 IH HeqMID.
      induction H23; intros.
        apply (f_equal length) in HeqMID. rewrite length_app in HeqMID. cbn in HeqMID. lia.
Admitted.

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    constructor.
    apply (Perm_insert x [] l [] l'). cbn. assumption.
    apply (Perm_insert x [y] l [] (y :: l)). cbn. apply Perm_refl.
    eapply Perm_trans; eassumption.
Qed.

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  induction 1.
    reflexivity.
    rewrite !Permutation_middle. constructor. assumption.
Qed.

End Insert2.

(** * Znajdowanie wszystkich permutacji (TODO) *)

(** ** Znajdowanie permutacji przez selekcję *)

Module perms_select.

Fixpoint select {A : Type} (l : list A) : list (list A * list A) :=
match l with
| [] => [([], [])]
| h :: t => [([], l)] ++ map (fun '(a, b) => (h :: a, b)) (select t)
end.

Lemma select_app :
  forall {A : Type} {l1 l2 : list A},
    select (l1 ++ l2) =
      map (fun '(l, r) => (app l l2, r)) (select l1) ++
      map (fun '(l, r) => (app l1 l, r)) (select l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
Abort.
(* end hide *)

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| h :: t =>
    bind (fun ll =>
      map (fun '(l, r) => l ++ h :: r) (select ll)) (perms t)
end.

(* Compute select [1; 2; 3]. *)
(* Compute perms [1; 2; 3]. *)

Lemma Permutation_bind :
  forall {A B : Type} (f g : A -> list B),
    (forall x : A, Permutation (f x) (g x)) ->
      forall l : list A, Permutation (bind f l) (bind g l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    apply Permutation_app; auto.
Qed.
(* end hide *)

Lemma Permutation_select_app :
  forall {A : Type} {l1 l2 : list A},
    Permutation (select (l1 ++ l2)) (select (l2 ++ l1)).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    replace (l2 ++ h1 :: t1) with ((l2 ++ [h1]) ++ t1).
      rewrite <- IHt1.
Admitted.
(* end hide *)

Lemma map_select :
  forall {A B : Type} (f : A -> B) (l : list A),
    select (map f l)
      =
    map (fun '(L, R) => (map f L, map f R)) (select l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt, !map_map. do 2 f_equal.
Admitted.
(* end hide *)

Lemma Permutation_perms :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (perms l1) (perms l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    do 2 constructor.
    rewrite 2!bind_spec. apply Permutation_join, Permutation_map.
      assumption.
    rewrite !bind_bind. apply Permutation_bind. intro l'.
      rewrite !bind_spec, !map_map, <- !bind_spec. generalize (select l').
        induction l0 as [| h t]; cbn.
          reflexivity.
          apply Permutation_app.
            destruct h.
Admitted.
(* end hide *)

Lemma elem_perms :
  forall (A : Type) (l : list A),
    elem l (perms l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    rewrite bind_spec, elem_join.
      exists (map (fun '(l, r) => l ++ h :: r) (select t)). split.
        destruct t; constructor.
        apply elem_map_conv. exists t. split.
          reflexivity.
          assumption.
Qed.
(* end hide *)

Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
(* begin hide *)
Proof.
  intros. apply Permutation_perms in H.
  rewrite <- (Permutation_elem _ (perms l1) (perms l2)).
    apply elem_perms.
    assumption.
Qed.
(* end hide *)

End perms_select.

Module perms_ins.

(** ** Znajdowanie permutacji przez wstawianie *)

Fixpoint ins {A : Type} (x : A) (l : list A) : list (list A) :=
match l with
| [] => [[x]]
| h :: t => [x :: h :: t] ++ map (cons h) (ins x t)
end.

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| h :: t => bind (ins h) (perms t)
end.

Lemma len_ins :
  forall (A : Type) (x : A) (l : list A),
    length (ins x l) = S (length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_map, IHt. reflexivity.
Qed.
(* end hide *)

Fixpoint nsum (l : list nat) : nat :=
match l with
| [] => 0
| h :: t => h + nsum t
end.

Lemma len_join :
  forall (A : Type) (ll : list (list A)),
    length (join ll) = nsum (map length ll).
(* begin hide *)
Proof.
  induction ll as [| h t]; cbn.
    reflexivity.
    rewrite length_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma len_perms :
  forall (A : Type) (l : list A),
    length (perms l) = fact (length l).
(* begin hide *)
Proof.
  induction l as [| h t].
    cbn. reflexivity.
    cbn [perms].
    rewrite bind_spec, len_join, map_map.
Abort.
(* end hide *)

Lemma map_ins :
  forall (A B : Type) (f : A -> B) (x : A) (l : list A),
    map (map f) (ins x l) = ins (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    f_equal. rewrite <- IHt, !map_map. cbn. reflexivity.
Qed.
(* end hide *)

Lemma ins_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    l1 = [] \/
    l2 = [] \/
      ins x (l1 ++ l2) =
      map (fun l => app l l2) (ins x l1) ++
      map (app l1) (ins x l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    left. reflexivity.
    induction l2 as [| h2 t2]; cbn.
      right. left. reflexivity.
      do 2 right. decompose [or] IHt2; subst; clear IHt2.
        inversion H.
Abort.
(* end hide *)

Lemma ins_snoc :
  forall (A : Type) (x y : A) (l : list A),
    ins x (snoc y l) =
    snoc (snoc x (snoc y l)) (map (snoc y) (ins x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    f_equal. rewrite IHt. rewrite map_snoc, !map_map.
      cbn. reflexivity.
Qed.
(* end hide *)

Lemma map_ext_eq :
  forall {A B : Type} {f g : A -> B} {l : list A},
    (forall x : A, f x = g x) ->
      map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intro.
    reflexivity.
    rewrite H, (IHt H). reflexivity.
Qed.
(* end hide *)

Lemma ins_rev :
  forall (A : Type) (x : A) (l : list A),
    ins x (rev l) = rev (map rev (ins x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite ins_snoc, IHt.
      rewrite map_rev, map_map, <- map_rev. f_equal.
      rewrite map_rev, map_map. cbn. f_equal.
Qed.
(* end hide *)

Lemma elem_ins :
  forall (A : Type) (x : A) (l : list A),
    elem (x :: l) (ins x l).
(* begin hide *)
Proof.
  destruct l; constructor.
Qed.
(* end hide *)

Lemma elem_perms :
  forall (A : Type) (l : list A),
    elem l (perms l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    rewrite bind_spec, elem_join. exists (ins h t). split.
      apply elem_ins.
      apply elem_map. assumption.
Qed.
(* end hide *)

Lemma Permutation_elem_ins :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem l2 (ins x l1) -> Permutation (x :: l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn.
    inversion 1; subst.
      reflexivity.
      inversion H2.
    inversion 1; subst.
      reflexivity.
      rewrite elem_map_conv in H2. destruct H2 as (r & Heq & Hel).
        subst. rewrite perm_swap. constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Permutation_bind :
  forall (A B : Type) (f g : A -> list B) (l1 l2 : list A),
    (forall x : A, Permutation (f x) (g x)) ->
      Permutation l1 l2 ->
        Permutation (bind f l1) (bind g l2).
(* begin hide *)
Proof.
  induction 2; cbn.
    constructor.
    apply Permutation_app.
      apply H.
      assumption.
    induction l as [| h t]; cbn.
      rewrite 2!app_nil_r. rewrite Permutation_app_comm.
        apply Permutation_app; apply H.
      rewrite (Permutation_app_comm _ (f h)),
              (Permutation_app_comm _ (g h)).
        rewrite !app_assoc. apply Permutation_app.
          rewrite <- !app_assoc. assumption.
          apply H.
    assert (Permutation (bind f l) (bind f l')).
      rewrite !bind_spec. apply Permutation_join, Permutation_map.
        assumption.
      rewrite H0, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma count_join :
  forall (A : Type) (p : A -> bool) (l : list (list A)),
    count p (join l) = nsum (map (count p) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite count_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma nsum_app :
  forall l1 l2 : list nat,
    nsum (l1 ++ l2) = nsum l1 + nsum l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite IHt1, Nat.add_assoc. reflexivity.
Qed.
(* end hide *)

Fixpoint deepcount
  {A : Type} (p : A -> bool) (l : list (list A)) : nat :=
match l with
| [] => 0
| h :: t => count p h + deepcount p t
end.

Lemma Permutation_bind_ins :
  forall {A : Type} (x y : A) (l : list A),
    Permutation (bind (ins x) (ins y l)) (bind (ins y) (ins x l)).
(* begin hide *)
Proof.
  induction l as [| h t].
    cbn. constructor.
    {
      change (ins x (h :: t)) with ([x :: h :: t] ++ map (cons h) (ins x t)).
      change (ins y (h :: t)) with ([y :: h :: t] ++ map (cons h) (ins y t)).
      rewrite !bind_app.
Admitted.
(* end hide *)

Lemma Permutation_perms :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (perms l1) (perms l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    do 2 constructor.
    rewrite 2!bind_spec. apply Permutation_join, Permutation_map.
      assumption.
    rewrite !bind_bind. apply Permutation_bind.
      2: reflexivity.
      apply Permutation_bind_ins.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
(* begin hide *)
Proof.
  intros. rewrite <- (Permutation_elem _ (perms l1)).
    apply elem_perms.
    apply Permutation_perms. assumption.
Qed.
(* end hide *)

Lemma perms_Permutation :
  forall {A : Type} {l1 l2 : list A},
    elem l1 (perms l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros until l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inv H.
      constructor.
      inv H2.
Abort.
(* end hide *)

End perms_ins.

(** ** Znajdowanie permutacji przez cykle *)

Require Import FunctionalExtensionality.
From Typonomikon Require D4.

Module perms_cycles.

Import cycles.
Import D4.

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| h :: t => join (map (fun t => cycles (cons h t)) (perms t))
end.

Compute cycles [1; 2].
Compute perms [3].
Compute perms [2; 3].
Compute cycles (map (cons 2) [[3]]).
Compute perms [1; 2; 3].
Compute perms [1; 2; 3; 4].

Fixpoint sum (l : list nat) : nat :=
match l with
| [] => 0
| h :: t => h + sum t
end.

Lemma len_join :
  forall {A : Type} (l : list (list A)),
    length (join l) = sum (map length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma len_cycles_aux :
  forall {A : Type} (l : list A) (n : nat),
    length (cycles_aux n l) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma len_cycles :
  forall {A : Type} (l : list A),
    l <> [] -> length (cycles l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intro.
    contradiction.
    rewrite len_cycles_aux. reflexivity.
Qed.
(* end hide *)

Lemma sum_map_S :
  forall l : list nat,
    sum (map S l) = length l + sum l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    f_equal. rewrite IHt, Nat.add_comm, <- !Nat.add_assoc.
      f_equal. apply Nat.add_comm.
Qed.
(* end hide *)

Lemma sum_replicate :
  forall n m : nat,
    sum (replicate n m) = n * m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    intro. rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma length_perms :
  forall {A : Type} (l : list A),
    length (perms l) = fact (length l) /\
      map length (perms l) =
      replicate (length (perms l)) (length l).
(* begin hide *)
Proof.
  induction l as [| h t].
    cbn. split; reflexivity.
    destruct IHt as [IH1 IH2]. split.
      cbn. rewrite len_join, map_map. cbn.
        replace (fun x => S (length (cycles_aux (length x) (h :: x))))
           with (fun x => S (@length A x)).
          2: {
            apply functional_extensionality. intro.
            rewrite len_cycles_aux. reflexivity.
          }
          {
            rewrite <- map_map, IH2.
            rewrite sum_map_S, length_replicate, sum_replicate.
            rewrite IH1. lia.
          }
      cbn. rewrite len_join, map_map. cbn.
        replace (fun x => S (length (cycles_aux (length x) (h :: x))))
           with (fun x => S (@length A x)).
          2: {
            apply functional_extensionality. intro.
            rewrite len_cycles_aux. reflexivity.
          }
          {
            rewrite <- (map_map _ _ _ _ S). rewrite IH2.
            rewrite sum_map_S, length_replicate, sum_replicate.
            rewrite map_join, map_map. cbn.
Abort.
(* end hide *)

Lemma perms_spec :
  forall {A : Type} (l1 l2 : list A),
    elem l1 (perms l2) -> Permutation l1 l2.
(* begin hide *)
Proof.

Abort.
(* end hide *)

Lemma perms_spec :
  forall {A : Type} (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
(* begin hide *)
Proof.
  induction 1.
    cbn. constructor.
    cbn. apply elem_join. eexists. split.
      2: { apply elem_map. exact IHPermutation. }
      admit.
    cbn. rewrite map_join, !map_map. apply elem_join. eexists. split.
      admit.
      admit.
Abort.
(* end hide *)

End perms_cycles.

(** * Wut da fuk? (TODO) *)

Module Specs.

Import Count.

Import perms_select.

Lemma perm_perms :
  forall {A : Type} {l1 l2 : list A},
    perm l1 l2 -> elem l1 (perms l2).
(* begin hide *)
Proof.
  intros until l2. revert l1.
  induction l2 as [| h2 t2]; cbn; unfold perm; intros.
    specialize (H (fun _ => true)). destruct l1.
      constructor.
      inv H.
    destruct l1 as [| h1 t1].
      specialize (H (fun _ => true)). cbn in H. inv H.
      cbn in H. rewrite bind_spec, elem_join. eexists. split.
        2: {
          apply elem_map. apply IHt2. red. intro.
          specialize (H p). destruct (p h1) eqn: ph1, (p h2) eqn: ph2.
            inv H. reflexivity.
Abort.
(* end hide *)

End Specs.

(** * Zbiory *)

(** ** Zbiory jako zdeduplikowane permutacje *)

(* Module SetPermDedup. *)

Inductive SameSet {A : Type} : list A -> list A -> Prop :=
| SameSet_nil   : SameSet [] []
| SameSet_cons  :
    forall (h : A) (t1 t2 : list A), SameSet t1 t2 -> SameSet (h :: t1) (h :: t2)
| SameSet_swap  :
    forall (x y : A) (l : list A), SameSet (y :: x :: l) (x :: y :: l)
| SameSet_dedup :
    forall (h : A) (t : list A), SameSet (h :: t) (h :: h :: t)
| SameSet_trans :
    forall l1 l2 l3 : list A, SameSet l1 l2 -> SameSet l2 l3 -> SameSet l1 l3.

Lemma SameSet_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSet l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  induction 1; unfold SetEquiv in *; intro z.
    reflexivity.
    rewrite !elem_cons', IHSameSet. reflexivity.
    rewrite !elem_cons'. firstorder.
    rewrite !elem_cons'. firstorder.
    rewrite IHSameSet1, IHSameSet2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_SameSet :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> SameSet l1 l2.
(* begin hide *)
Proof.
  induction 1; econstructor; eassumption.
Qed.
(* end hide *)

(* End SetPermDedup. *)

(** ** Zbiory za pomocą [Exists] *)

Module SetExists.

Definition SameSetEx {A : Type} (l1 l2 : list A) : Prop :=
  forall P : A -> Prop, Exists P l1 <-> Exists P l2.

Lemma SameSetEx_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSetEx l1 l2 <-> SetEquiv l1 l2.
(* begin hide *)
Proof.
  unfold SameSetEx, SetEquiv.
  split; intros.
    specialize (H (fun y => x = y)). rewrite !Exists_spec in H.
      firstorder; specialize (H x); specialize (H0 x); cbn in *; firstorder congruence.
    rewrite !Exists_spec. firstorder.
Qed.
(* end hide *)

End SetExists.

(** ** Zbiory za pomocą transpozycji i deduplikacji *)

Module SetTranspositionDedup.

Inductive Transposition {A : Type} : list A -> list A -> Prop :=
| Transposition' :
    forall (x y : A) (l1 l2 l3 : list A),
      Transposition (l1 ++ x :: l2 ++ y :: l3) (l1 ++ y :: l2 ++ x :: l3).

Inductive Dedup {A : Type} : list A -> list A -> Prop :=
| Dedup' :
    forall (x : A) (l1 l2 l3 : list A),
      Dedup (l1 ++ x :: l2 ++ x :: l3) (l1 ++ x :: l2 ++ l3).

Inductive SameSetTD {A : Type} : list A -> list A -> Prop :=
| SameSetTD_refl   :
    forall l : list A, SameSetTD l l
| SameSetTD_transp :
    forall l1 l2 l3 : list A,
      Transposition l1 l2 -> SameSetTD l2 l3 -> SameSetTD l1 l3
| SameSetTD_dedup  :
    forall l1 l2 l3 : list A,
      Dedup l1 l2 -> SameSetTD l2 l3 -> SameSetTD l1 l3.

Lemma SameSetTD_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSetTD l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  unfold SetEquiv.
  induction 1; intro.
    apply SetEquiv_refl.
    inv H. rewrite <- IHSameSetTD, !elem_app, !elem_cons', !elem_app, !elem_cons'. firstorder.
    inv H. rewrite <- IHSameSetTD, !elem_app, !elem_cons', !elem_app, !elem_cons'. firstorder.
Qed.
(* end hide *)

End SetTranspositionDedup.

(** ** Zbiory za pomocą sąsiednich transpozycji i deduplikacji *)

Module SetAdjacentTranspositionDedup.

Inductive AdjacentTransposition {A : Type} : list A -> list A -> Prop :=
| AdjacentTransposition' :
    forall (x y : A) (l1 l2 : list A),
      AdjacentTransposition (l1 ++ x :: y :: l2) (l1 ++ y :: x :: l2).

Inductive AdjacentDedup {A : Type} : list A -> list A -> Prop :=
| AdjacentDedup' :
    forall (x : A) (l1 l2 : list A),
      AdjacentDedup (l1 ++ x :: x :: l2) (l1 ++ x :: l2).

Inductive SameSetATD {A : Type} : list A -> list A -> Prop :=
| SameSetATD_refl   :
    forall l : list A, SameSetATD l l
| SameSetATD_transp :
    forall l1 l2 l3 : list A,
      AdjacentTransposition l1 l2 -> SameSetATD l2 l3 -> SameSetATD l1 l3
| SameSetATD_dedup  :
    forall l1 l2 l3 : list A,
      AdjacentDedup l1 l2 -> SameSetATD l2 l3 -> SameSetATD l1 l3.

Lemma SameSetATD_trans :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD l1 l2 ->
      forall {l3 : list A}, SameSetATD l2 l3 -> SameSetATD l1 l3.
(* begin hide *)
Proof.
  induction 1; intros.
    assumption.
    econstructor.
      eassumption.
      apply IHSameSetATD. assumption.
    econstructor 3.
      eassumption.
      apply IHSameSetATD. assumption.
Qed.
(* end hide *)

Lemma SameSetATD_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  unfold SetEquiv.
  induction 1; intro.
    apply SetEquiv_refl.
    inv H. rewrite <- IHSameSetATD, !elem_app, !elem_cons'. firstorder.
    inv H. rewrite <- IHSameSetATD, !elem_app, !elem_cons'. firstorder.
Qed.

Lemma AdjacentTransposition_cons :
  forall {A : Type} {t1 t2 : list A},
    AdjacentTransposition t1 t2 ->
      forall h : A, AdjacentTransposition (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  induction 1.
  intro h.
  rewrite <- !app_cons_l.
  constructor.
Qed.
(* end hide *)

Lemma AdjacentDedup_cons :
  forall {A : Type} {t1 t2 : list A},
    AdjacentDedup t1 t2 ->
      forall h : A, AdjacentDedup (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  destruct 1.
  intro h.
  rewrite <- !app_cons_l.
  constructor.
Qed.
(* end hide *)

Lemma SameSetATD_cons :
  forall {A : Type} {t1 t2 : list A},
    SameSetATD t1 t2 ->
      forall h : A, SameSetATD (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  induction 1; intros h.
    constructor.
    apply (@SameSetATD_transp _ _ (h :: l2)).
      apply AdjacentTransposition_cons. assumption.
      apply IHSameSetATD.
    apply (@SameSetATD_dedup _ _ (h :: l2)).
      apply AdjacentDedup_cons. assumption.
      apply IHSameSetATD.
Qed.
(* end hide *)

Lemma SetEquiv_SameSetATD :
  forall {A : Type} {l1 l2 : list A},
    SetEquiv l1 l2 -> SameSetATD l1 l2.
(* begin hide *)
Proof.
  unfold SetEquiv.
  induction l1 as [| h1 t1];
  intros l2 H.
    admit.
    {
      assert (elem h1 l2).
        apply H. left.
      apply elem_spec in H0.
      destruct H0 as (l1 & l3 & H0); subst.
      admit.
    }
Restart.
  intros.
Admitted.
(* end hide *)

Inductive SameSetATD' {A : Type} (l1 : list A) : list A -> Prop :=
| SameSetATD'_refl   :
    SameSetATD' l1 l1
| SameSetATD'_transp :
    forall l2 l3 : list A,
      SameSetATD' l1 l2 -> AdjacentTransposition l2 l3 -> SameSetATD' l1 l3
| SameSetATD'_dedup  :
    forall l2 l3 : list A,
      SameSetATD' l1 l2 -> AdjacentDedup l2 l3 -> SameSetATD' l1 l3.

Lemma SameSetATD'_trans :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD' l1 l2 ->
      forall {l3 : list A}, SameSetATD' l2 l3 -> SameSetATD' l1 l3.
(* begin hide *)
Proof.
  intros until 2. revert l1 H.
  induction H0; intros.
    assumption.
    econstructor.
      apply IHSameSetATD'. assumption.
      assumption.
    econstructor 3.
      apply IHSameSetATD'. assumption.
      assumption.
Qed.
(* end hide *)

Lemma SameSetATD'_spec :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD' l1 l2 <-> SameSetATD l1 l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      constructor.
      apply (SameSetATD_trans IHSameSetATD'). econstructor.
        eassumption.
        constructor.
      apply (SameSetATD_trans IHSameSetATD'). econstructor 3.
        eassumption.
        constructor.
    induction 1.
      constructor.
      eapply SameSetATD'_trans.
        2: eassumption.
        econstructor.
          constructor.
          assumption.
      eapply SameSetATD'_trans.
        2: eassumption.
        econstructor 3.
          constructor.
          assumption.
Qed.
(* end hide *)

End SetAdjacentTranspositionDedup.