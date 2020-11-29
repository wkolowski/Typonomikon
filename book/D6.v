(** * D6: Więcej list [TODO] *)

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

Require Import D5.

(** * Predykaty i relacje na listach - znowu (TODO) *)

Module Recursives.

(** Można zadać sobie pytanie: skoro predykaty takie jak [elem] czy
    [exists] można zdefiniować zarówno induktywnie jak i przez rekursję,
    który sposób jest lepszy?

    Odpowiedź jest prosta: jeżeli możesz użyć rekursji, zrób to. *)

Fixpoint elem {A : Type} (x : A) (l : list A) : Prop :=
match l with
    | [] => False
    | h :: t => x = h \/ elem x t
end.

Fixpoint all {A : Type} (P : A -> Prop) (l : list A) : Prop :=
match l with
    | [] => True
    | h :: t => P h /\ all P t
end.

Lemma all_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    all P l <-> Forall P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    rewrite Forall_nil. reflexivity.
    rewrite Forall_cons, IHt. reflexivity.
Qed.
(* end hide *)

Fixpoint exactly
  {A : Type} (P : A -> Prop) (n : nat) (l : list A) : Prop :=
match l, n with
    | [], 0 => True
    | [], _ => False
    | h :: t, 0 => ~ P h /\ exactly P 0 t
    | h :: t, S n' =>
        (P h /\ exactly P n' t) \/ (~ P h /\ exactly P n t)
end.

Lemma exactly_spec :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    exactly P n l <-> Exactly P n l.
(* begin hide *)
Proof.
  intros. revert n.
  induction l as [| h t]; cbn.
    destruct n; cbn.
      firstorder. apply Ex_0.
      firstorder. inversion H.
    destruct n as [| n']; cbn.
      rewrite IHt, Exactly_0_cons. reflexivity.
      rewrite !IHt, Exactly_S_cons. reflexivity.
Qed.
(* end hide *)

(** ** [exists] *)

(* begin hide *)
Fixpoint ex {A : Type} (P : A -> Prop) (l : list A) : Prop :=
match l with
    | [] => False
    | h :: t => P h \/ ex P t
end.
(* end hide *)

Lemma ex_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l <-> exists x : A, elem x l /\ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder.
    firstorder congruence.
Qed.
(* end hide *)

Lemma ex_nil :
  forall (A : Type) (P : A -> Prop),
    ex P [] <-> False.
(* begin hide *)
Proof.
  split; inversion 1.
Qed.
(* end hide *)

Lemma ex_cons :
  forall (A : Type) (P : A -> Prop) (h : A) (t : list A),
    ex P (h :: t) <-> P h \/ ex P t.
(* begin hide *)
Proof.
  split.
    inversion 1; subst; [left | right]; assumption.
    destruct 1; [left | right]; assumption.
Qed.
(* end hide *)

Lemma ex_length :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l -> 1 <= length l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    destruct 1.
    intros _. apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma ex_snoc :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    ex P (snoc x l) <-> ex P l \/ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder.
    rewrite IHt. firstorder.
Qed.
(* end hide *)

Lemma ex_app :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    ex P (l1 ++ l2) <-> ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    firstorder.
    rewrite IHt1. tauto.
Qed.
(* end hide *)

Lemma ex_rev :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P (rev l) <-> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite ex_app, IHt. cbn. tauto.
Qed.
(* end hide *)

Lemma ex_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    ex P (map f l) -> ex (fun x : A => P (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    tauto.
Qed.
(* end hide *)

Lemma ex_join :
  forall (A : Type) (P : A -> Prop) (ll : list (list A)),
    ex P (join ll) <->
    ex (fun l : list A => ex  P l) ll.
(* begin hide *)
Proof.
  induction ll as [| h t]; cbn; intros.
    reflexivity.
    rewrite ex_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma ex_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    ex P (replicate n x) <-> 1 <= n /\ P x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    firstorder. inversion H.
    firstorder. apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma ex_nth :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l <->
    exists (n : nat) (x : A), nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder congruence.
    rewrite IHt. split.
      destruct 1.
        exists 0, h. split; trivial.
        destruct H as (n & x & H1 & H2).
          exists (S n), x. split; assumption.
      destruct 1 as (n & x & H1 & H2). destruct n as [| n'].
        left. congruence.
        right. exists n', x. split; assumption.
Qed.
(* end hide *)

Lemma ex_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P l ->
    match remove n l with
        | None => True
        | Some (x, l') => ~ P x -> ex P l'
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 2.
    destruct n as [| n'].
      firstorder.
      destruct 1.
        case_eq (remove n' t).
          intros [a la] eq Hnot. cbn. left. assumption.
          trivial.
        case_eq (remove n' t).
          intros [a la] eq Hnot. cbn. specialize (IHt n' H).
            rewrite eq in IHt. right. apply IHt. assumption.
          trivial.
Qed.
(* end hide *)

Lemma ex_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P (take n l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      inversion H.
      cbn in H. firstorder.
Qed.
(* end hide *)

Lemma ex_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P (drop n l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      cbn in H. assumption.
      right. apply (IHt _ H).
Qed.
(* end hide *)

Lemma ex_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P l -> ex P (take n l) \/ ex P (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. assumption.
    destruct n as [| n']; cbn.
      right. assumption.
      firstorder.
Qed.
(* end hide *)

Lemma ex_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      ex P l <-> P x \/ ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 2.
    destruct n as [| n']; cbn; inversion 1; subst.
      cbn. tauto.
      case_eq (splitAt n' t); intros.
        destruct p, p. rewrite (IHt _ _ _ _ H0).
          rewrite H0 in H1. inversion H1; subst. cbn. tauto.
        rewrite H0 in H1. inversion H1.
Restart.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  rewrite ex_app, ex_cons. firstorder.
Qed.
(* end hide *)

Lemma ex_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat) (x : A),
    ex P (insert l n x) <-> P x \/ ex P l.
(* begin hide *)
Proof.
  intros.
  rewrite <- (app_take_drop _ l n) at 2.
  rewrite insert_spec, !ex_app, ex_cons.
  tauto.
Qed.
(* end hide *)

Lemma ex_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      ex P l' <->
      ex P (take n l) \/ P x \/ ex P (drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (n <? length l).
    inversion H; subst. rewrite ex_app, ex_cons. reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma ex_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (filter p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h); cbn in H; firstorder.
Qed.
(* end hide *)

Lemma ex_filter_conv :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P l ->
      ex P (filter p l) \/
      ex P (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 1.
    destruct (p h); cbn; firstorder.
Qed.
(* end hide *)

Lemma ex_filter_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ ex P (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    assumption.
    specialize (IHt H). specialize (H h). destruct (p h); cbn in *.
      firstorder congruence.
      contradiction.
Qed.
(* end hide *)

Lemma ex_partition :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      ex P l <-> ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H.
  inversion H; subst; clear H. split; intro.
    apply ex_filter_conv. assumption.
    destruct H; apply ex_filter in H; assumption.
Qed.
(* end hide *)

Lemma ex_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (takeWhile p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  try destruct (p h); inversion H; subst; clear H.
    left. assumption.
    right. apply IHt, H0.
Qed.
(* end hide *)

Lemma ex_takeWhile_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ ex P (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    assumption.
    specialize (IHt H). specialize (H h).
      destruct (p h); cbn in *; firstorder congruence.
Qed.
(* end hide *)

Lemma ex_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (dropWhile p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h); firstorder.
Qed.
(* end hide *)

Lemma ex_takeWhile_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P l -> ex P (takeWhile p l) \/ ex P (dropWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 1.
    destruct (p h); cbn; firstorder.
Qed.
(* end hide *)

Lemma ex_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        ex P l <-> ex P b \/ P x \/ ex P e.
(* begin hide *)
Proof.
  intros. apply span_spec in H0.
  rewrite H0, ex_app, ex_cons.
  reflexivity.
Qed.
(* end hide *)

Lemma ex_interesting :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (hb : B) (tb : list B),
    ex (fun a : A => ex (fun b : B => P (a, b)) tb) la ->
    ex (fun a : A => ex (fun b : B => P (a, b)) (hb :: tb)) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn.
    contradiction.
    intros. destruct H.
      left. right. assumption.
      right. cbn in IHta. apply IHta. assumption.
Qed.
(* end hide *)

Lemma ex_zip :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (lb : list B),
    ex P (zip la lb) ->
      ex (fun a : A => ex (fun b : B => P (a, b)) lb) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    assumption.
    induction lb as [| hb tb]; inversion H; subst; clear H.
      left. left. assumption.
      specialize (IHta _ H0). right.
        apply ex_interesting. assumption.
Qed.
(* end hide *)

Lemma ex_pmap :
  forall (A B : Type) (f : A -> option B) (P : B -> Prop) (l : list A),
    ex P (pmap f l) <->
      ex (fun x : A => match f x with | Some b => P b | _ => False end) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite IHt.
      reflexivity.
      tauto.
Qed.
(* end hide *)

Lemma ex_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    ex P (intersperse x l) <->
    ex P l \/ (P x /\ 2 <= length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    firstorder lia.
    destruct (intersperse x t) eqn: eq; cbn in *.
      rewrite IHt. firstorder. destruct t; cbn in eq.
        inversion H2. inversion H4.
        destruct (intersperse x t); inversion eq.
      rewrite IHt. firstorder. destruct t; cbn in *.
        inversion eq.
        right. split.
          assumption.
          apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)

End Recursives.

(** * Rozstrzyganie predykatów i relacji na listach (TODO) *)

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
  intros.
  pose (Prefix_Suffix _ (rev l1) (rev l2)).
  rewrite 2!rev_inv in i.
  unfold Suffix_dec.
  destruct (Prefix_dec_spec eq_dec_spec (rev l1) (rev l2)).
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

(** * Znajdowanie wszystkich podstruktur (TODO) *)

(** ** Podlisty/podtermy *)

Module sublists.

Fixpoint sublists {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => []
    | h :: t => t :: sublists t
end.

Lemma sublists_spec :
  forall {A : Type} (l1 l2 : list A),
    Sublist l1 l2 -> elem l1 (sublists l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    right. assumption.
Qed.
(* end hide *)

Lemma sublists_spec' :
  forall {A : Type} (l1 l2 : list A),
    elem l1 (sublists l2) -> Sublist l1 l2.
(* begin hide *)
Proof.
  induction l2 as [| h2 t2]; cbn.
    inversion 1.
    inversion 1; subst.
      constructor.
      constructor. apply IHt2. assumption.
Qed.
(* end hide *)

End sublists.

(** ** Sufiksy *)

Module suffixes.

Fixpoint suffixes {A : Type} (l : list A) : list (list A) :=
  l ::
match l with
    | [] => []
    | h :: t => suffixes t
end.

Lemma suffixes_spec :
  forall {A : Type} (l1 l2 : list A),
    Suffix l1 l2 -> elem l1 (suffixes l2).
(* begin hide *)
Proof.
  induction 1.
    destruct l; constructor.
    cbn. constructor. assumption.
Qed.
(* end hide *)

Lemma suffixes_spec' :
  forall {A : Type} (l1 l2 : list A),
    elem l1 (suffixes l2) -> Suffix l1 l2.
(* begin hide *)
Proof.
  induction l2 as [| h2 t2]; cbn.
    inversion 1; subst.
      constructor.
      inversion H2.
    inversion 1; subst.
      constructor.
      constructor. apply IHt2. assumption.
Qed.
(* end hide *)

End suffixes.

(** ** Prefiksy *)

Module prefixes.

Import suffixes.

Fixpoint prefixes {A : Type} (l : list A) : list (list A) :=
  [] ::
match l with
    | [] => []
    | h :: t => map (cons h) (prefixes t)
end.

Lemma prefixes_spec :
  forall {A : Type} (l1 l2 : list A),
    Prefix l1 l2 -> elem l1 (prefixes l2).
(* begin hide *)
Proof.
  induction 1.
    destruct l; constructor.
    cbn. constructor. apply elem_map. assumption.
Qed.
(* end hide *)

Lemma elem_map_cons :
  forall {A : Type} (h1 h2 : A) (t1 : list A) (t2 : list (list A)),
    elem (h1 :: t1) (map (cons h2) t2) -> h1 = h2.
(* begin hide *)
Proof.
  intros until t2. revert h1 h2 t1.
  induction t2 as [| h t]; cbn; intros.
    inv H.
    inv H.
      reflexivity.
      apply (IHt _ _ _ H2).
Qed.
(* end hide *)

Lemma prefixes_spec' :
  forall {A : Type} (l1 l2 : list A),
    elem l1 (prefixes l2) -> Prefix l1 l2.
(* begin hide *)
Proof.
  intros until l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inv H.
      constructor.
      inv H2.
    inv H.
      constructor.
      destruct l1 as [| h1 t1].
        constructor.
        replace h1 with h2 in *.
          constructor. apply IHt2. apply elem_map_conv' in H2.
            assumption.
            inversion 1; auto.
          apply elem_map_cons in H2. symmetry. assumption.
Qed.
(* end hide *)

End prefixes.

(** ** Podciągi *)

Module subseqs.

Fixpoint subseqs {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | h :: t => map (cons h) (subseqs t) ++ subseqs t
end.

Compute subseqs [1; 2; 3; 4; 5].

Lemma Subseq_subseqs :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> elem l1 (subseqs l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn.
      constructor.
      apply elem_app_r. assumption.
    apply elem_app_l, elem_map. assumption.
    apply elem_app_r. assumption.
Qed.
(* end hide *)

Lemma subseqs_Subseq :
  forall (A : Type) (l1 l2 : list A),
    elem l1 (subseqs l2) -> Subseq l1 l2.
(* begin hide *)
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
(* end hide *)

End subseqs.

(** ** Podzbiory *)

Module subsets.

(* begin hide *)
(* TODO: znaleźć specyfikację dla [subsets] *)
(* end hide *)

Fixpoint subsets {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | h :: t => subsets t ++ map (cons h) (subsets t)
end.

Import prefixes.

End subsets.

(** ** Cykle *)

Module cycles.

Fixpoint cycles_aux {A : Type} (n : nat) (l : list A) : list (list A) :=
match n with
    | 0 => []
    | S n' => cycle n l :: cycles_aux n' l
end.

Compute cycles_aux 0 [1; 2; 3; 4; 5].
Compute cycles_aux 5 [1; 2; 3; 4; 5].

Definition cycles {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | _ => cycles_aux (length l) l
end.

Compute cycles [].
Compute cycles [1].
Compute cycles [1; 2; 3; 4; 5].

Lemma Cycle_cycles_aux :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall n : nat,
      elem l1 (cycles_aux (S (length l2) + n) l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn; intros.
      constructor.
      destruct (IHt n).
Admitted.
(* end hide *)

End cycles.

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

Hint Constructors AtLeast : core.

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

Hint Constructors Exactly : core.

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

Compute select [1; 2; 3].
Compute perms [1; 2; 3].

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

(* TODO: bind_app *)

Lemma bind_bind :
  forall {A B C : Type} (f : A -> list B) (g : B -> list C) (l : list A),
    bind g (bind f l) = bind (fun x : A => bind g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite bind_spec, map_app, join_app, <- !bind_spec, IHt. reflexivity.
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
    select (map f l) = map (fun '(L, R) => (map f L, map f R)) (select l).
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
            destruct h. Check Permutation_map.
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
    cbn [perms]. Search length bind.
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
    rewrite <- !snoc_app_singl. rewrite ins_snoc, IHt.
      rewrite map_rev, map_map, <- map_rev. f_equal.
      rewrite map_rev, map_map. cbn. f_equal.
      apply map_ext_eq. intro. apply snoc_app_singl.
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

Lemma bind_comm :
  forall (A B C : Type) (f g: A -> list A) (l : list A),
    bind f (bind g l) =
    bind g (bind f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite !bind_spec, !map_app in *.
      rewrite !join_app. rewrite IHt. do 2 f_equal.
Abort.
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
    rewrite IHt1, plus_assoc. reflexivity.
Qed.
(* end hide *)

Fixpoint deepcount
  {A : Type} (p : A -> bool) (l : list (list A)) : nat :=
match l with
    | [] => 0
    | h :: t => count p h + deepcount p t
end.

Lemma bind_assoc :
  forall
    (A B C : Type) (f : A -> list B) (g : B -> list C) (la : list A),
      bind g (bind f la) = bind (fun x => bind g (f x)) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn.
    reflexivity.
    intros. rewrite !bind_spec, !map_app, join_app in *.
      rewrite IHta. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_bind_ins :
  forall (A : Type) (x y : A) (l : list A),
    Permutation
      (bind (ins x) (ins y l))
      (bind (ins y) (ins x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    rewrite perm_swap. do 2 constructor. apply Permutation_app.
      apply Permutation_count_conv. intro.
        rewrite !count_map.
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
    rewrite !bind_assoc. apply Permutation_bind.
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

Module perms_cycles.

Import cycles.

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
    | [] => [[]]
    | h :: t =>
        join (map (fun t => cycles (cons h t)) (perms t))
end.

Compute cycles [1; 2].
Compute perms [3].
Compute perms [2; 3].
Compute cycles (map (cons 2) [[3]]).
Compute perms [1; 2; 3].
Compute perms [1; 2; 3; 4].

Require Import D4.

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
    f_equal. rewrite IHt, plus_comm, <- !plus_assoc.
      f_equal. apply plus_comm.
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
          Focus 2. Require Import FunctionalExtensionality.
            apply functional_extensionality. intro.
            rewrite len_cycles_aux. reflexivity.
          {
            rewrite <- map_map, IH2.
            rewrite sum_map_S, length_replicate, sum_replicate.
            rewrite IH1. lia.
          }
      cbn. rewrite len_join, map_map. cbn.
        replace (fun x => S (length (cycles_aux (length x) (h :: x))))
           with (fun x => S (@length A x)).
          Focus 2. Require Import FunctionalExtensionality.
            apply functional_extensionality. intro.
            rewrite len_cycles_aux. reflexivity.
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
      Focus 2. apply elem_map. exact IHPermutation.
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
        Focus 2.
        {
          apply elem_map. apply IHt2. red. intro.
          specialize (H p). destruct (p h1) eqn: ph1, (p h2) eqn: ph2.
            Focus 3.
            inv H. reflexivity.
Abort.
(* end hide *)

End Specs.

(** * Zbiory jako zdeduplikowane permutacje *)

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
Proof.
  induction 1; unfold SetEquiv in *; intro z.
    reflexivity.
    rewrite !elem_cons', IHSameSet. reflexivity.
    rewrite !elem_cons'. firstorder.
    rewrite !elem_cons'. firstorder.
    rewrite IHSameSet1, IHSameSet2. reflexivity.
Qed.

Lemma Permutation_SameSet :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> SameSet l1 l2.
Proof.
  induction 1; econstructor; eassumption.
Qed.

(* End SetPermDedup. *)

(** * Zbiory jako zdeduplikowane permutacje po raz drugi *)

Module SetPermNoDup.

Definition Represents {A : Type} (l1 l2 : list A) : Prop :=
  Permutation l1 l2 /\ NoDup l2.

Inductive RepresentSameSet {A : Type} (l1 l2 : list A) : Prop :=
    | SameSet'' :
        forall l : list A,
          Represents l1 l -> Represents l2 l -> RepresentSameSet l1 l2.

Lemma RepresentSameSet_Represents :
  forall {A : Type} {l1 l2 : list A},
    RepresentSameSet l1 l2 -> SameSet l1 l2.
Proof.
  intros A l1 l2 [l [HP1 HN1] [HP2 HN2]].
  apply Permutation_SameSet.
  eapply Permutation_trans.
    eassumption.
    symmetry. assumption.
Qed.

Lemma SameSet_RepresentSameSet :
  forall {A : Type} {l1 l2 : list A},
    SameSet l1 l2 -> RepresentSameSet l1 l2.
Proof.
  induction 1.
    exists []; repeat constructor.
    admit.
    exists (x :: y :: l); constructor.
      constructor.
      constructor.
Abort.

End SetPermNoDup.

(** * Zbiory za pomocą [Exists] *)

Module SetExists.

Definition SameSetEx {A : Type} (l1 l2 : list A) : Prop :=
  forall P : A -> Prop, Exists P l1 <-> Exists P l2.

Lemma SameSetEx_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSetEx l1 l2 <-> SetEquiv l1 l2.
Proof.
  unfold SameSetEx, SetEquiv.
  split; intros.
    specialize (H (fun y => x = y)). rewrite !Exists_spec in H.
      firstorder; specialize (H x); specialize (H0 x); cbn in *; firstorder congruence.
    rewrite !Exists_spec. firstorder.
Qed.

End SetExists.

(** * Zbiory za pomocą sąsiednich transpozycji *)

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

Inductive SameSetATD' {A : Type} (l1 : list A) : list A -> Prop :=
    | SameSetATD'_refl   :
        SameSetATD' l1 l1
    | SameSetATD'_transp :
        forall l2 l3 : list A,
          SameSetATD' l1 l2 -> AdjacentTransposition l2 l3 -> SameSetATD' l1 l3
    | SameSetATD'_dedup  :
        forall l2 l3 : list A,
          SameSetATD' l1 l2 -> AdjacentDedup l2 l3 -> SameSetATD' l1 l3.

Lemma SameSetATD_trans :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD l1 l2 ->
      forall {l3 : list A}, SameSetATD l2 l3 -> SameSetATD l1 l3.
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

Lemma SameSetATD'_trans :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD' l1 l2 ->
      forall {l3 : list A}, SameSetATD' l2 l3 -> SameSetATD' l1 l3.
Proof.
  induction 1; intros.
    assumption.
    econstructor.
      eassumption.
Restart.
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

Lemma SameSetATD'_spec :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD' l1 l2 <-> SameSetATD l1 l2.
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

Lemma SameSetATD_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD l1 l2 -> SetEquiv l1 l2.
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
Proof.
  induction 1.
  intro h.
  rewrite <- !app_cons_l.
  constructor.
Qed.

Lemma AdjacentDedup_cons :
  forall {A : Type} {t1 t2 : list A},
    AdjacentDedup t1 t2 ->
      forall h : A, AdjacentDedup (h :: t1) (h :: t2).
Proof.
  induction 1.
  intro h.
  rewrite <- !app_cons_l.
  constructor.
Qed.

Lemma SameSetATD_cons :
  forall {A : Type} {t1 t2 : list A},
    SameSetATD t1 t2 ->
      forall h : A, SameSetATD (h :: t1) (h :: t2).
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

Lemma SetEquiv_SameSetATD :
  forall {A : Type} {l1 l2 : list A},
    SetEquiv l1 l2 -> SameSetATD l1 l2.
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
Admitted.

End SetAdjacentTranspositionDedup.

(** * Zbiory za pomocą transpozycji *)

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
Proof.
  unfold SetEquiv.
  induction 1; intro.
    apply SetEquiv_refl.
    inv H. rewrite <- IHSameSetTD, !elem_app, !elem_cons', !elem_app, !elem_cons'. firstorder.
    inv H. rewrite <- IHSameSetTD, !elem_app, !elem_cons', !elem_app, !elem_cons'. firstorder.
Qed.

End SetTranspositionDedup.

(** * Permutacje, jeszcze dziwniej *)

Module PermWeird.

Inductive Elem {A : Type} (x : A) : list A -> Type :=
    | Z : forall l : list A, Elem x (x :: l)
    | S : forall {t : list A}, Elem x t -> forall h : A, Elem x (h :: t).

Arguments Z {A x} _.
Arguments S {A x t} _ _.

Require Import H.

Definition Perm {A : Type} (l1 l2 : list A) : Type :=
  forall x : A, iso (Elem x l1) (Elem x l2).

Require Import Equality.

(* Lemma Permutation_Perm :
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
End PermWeird.