(** * H4: Nierówność i różność [TODO] *)

Set Universe Polymorphism.

Require Import Arith.
Require Import Bool.
Require Import Equality.
Require Import FunctionalExtensionality.

Require Import List.
Import ListNotations.

From Typonomikon Require Import H1.
From Typonomikon Require Import D5.

(** * Różność *)

(** ** Nierówność liczb naturalnych - rekurencyjnie *)

Module nat_neq_rec.

(** A co to znaczy, że liczby naturalne nie są równe? *)

(** Powinien być tylko jeden dowód na nierówność. *)

Fixpoint code (n m : nat) : Type :=
match n, m with
    | 0, 0 => False
    | 0, S _ => True
    | S _, 0 => True
    | S n', S m' => code n' m'
end.

Lemma isProp_code :
  forall {n m : nat} (c1 c2 : code n m), c1 = c2.
(* begin hide *)
Proof.
  induction n as [| n'], m as [| m']; cbn.
    1-3: destruct c1, c2; reflexivity.
    apply IHn'.
Qed.
(* end hide *)

Fixpoint encode {n m : nat} {struct n} : n <> m -> code n m.
(* begin hide *)
Proof.
  destruct n as [| n'], m as [| m']; cbn; intro p.
    apply p. reflexivity.
    exact I.
    exact I.
    apply encode. intro q. apply p. f_equal. exact q.
Defined.
(* end hide *)

Fixpoint decode {n m : nat} : code n m -> n <> m.
(* begin hide *)
Proof.
  destruct n as [| n'], m as [| m']; cbn; intro p.
    contradiction.
    inversion 1.
    inversion 1.
    intro q. apply (decode _ _ p). inversion q. reflexivity.
Defined.
(* end hide *)

Lemma encode_decode :
  forall {n m : nat} (p : n <> m),
    decode (encode p) = p.
Proof.
  intros.
  apply functional_extensionality.
  destruct x.
  contradiction.
Qed.

Lemma decode_encode :
  forall {n m : nat} (c : code n m),
    encode (decode c) = c.
Proof.
  intros.
  apply isProp_code.
Qed.

End nat_neq_rec.

(** ** Nierówność liczb naturalnych - induktywnie *)

Module nat_neq_ind.

Inductive nat_neq : nat -> nat -> Prop :=
    | ZS : forall n : nat, nat_neq 0 (S n)
    | SZ : forall n : nat, nat_neq (S n) 0
    | SS : forall n m : nat, nat_neq n m -> nat_neq (S n) (S m).

Arguments ZS {n}.
Arguments SZ {n}.
Arguments SS {n m} _.

Scheme nat_neq_ind' := Induction for nat_neq Sort Prop.

Lemma isProp_nat_neq :
  forall {n m : nat} (p q : nat_neq n m), p = q.
(* begin hide *)
Proof.
  induction p using nat_neq_ind';
  dependent destruction q.
    reflexivity.
    reflexivity.
    apply f_equal, IHp.
Qed.
(* end hide *)

Fixpoint encode {n m : nat} : n <> m -> nat_neq n m :=
match n, m with
    | 0, 0       => fun p => match p eq_refl with end
    | 0, S m'    => fun _ => @ZS m'
    | S n', 0    => fun _ => @SZ n'
    | S n', S m' => fun p => SS (@encode n' m' (fun p' => p (f_equal S p')))
end.

Fixpoint decode {n m : nat} (c : nat_neq n m) : n <> m.
Proof.
  destruct c.
    inversion 1.
    inversion 1.
    inversion 1. apply (decode _ _ c). assumption.
Defined.

Lemma encode_decode :
  forall {n m : nat} (p : n <> m),
    decode (encode p) = p.
(* begin hide *)
Proof.
  induction n as [| n'];
  destruct  m as [| m'];
  cbn; intros.
    contradiction.
    apply functional_extensionality. inversion x.
    apply functional_extensionality. inversion x.
    apply functional_extensionality. intro. contradiction.
Qed.
(* end hide *)

Lemma decode_encode :
  forall {n m : nat} (c : nat_neq n m),
    encode (decode c) = c.
(* begin hide *)
Proof.
  induction c using nat_neq_ind'; cbn.
    1-2: reflexivity.
    f_equal. rewrite <- IHc. f_equal.
      apply functional_extensionality.
      destruct x. cbn. rewrite IHc. reflexivity.
Qed.
(* end hide *)

End nat_neq_ind.

Module nat_eq_neq.

Import nat_eq_ind nat_neq_ind.

Lemma nat_eq_dec :
  forall n m : nat, nat_eq n m + nat_neq n m.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'].
  - left. constructor.
  - right. constructor.
  - right. constructor.
  - destruct (IHn' m').
    + left. constructor. assumption.
    + right. constructor. assumption.
Qed.
(* end hide *)

End nat_eq_neq.

(** ** Nierówność list - rekursywnie *)

Fixpoint list_neq_rec {A : Type} (l1 l2 : list A) : Prop :=
match l1, l2 with
    | [], [] => False
    | [], _ => True
    | _, [] => True
    | h1 :: t1, h2 :: t2 => h1 <> h2 \/ list_neq_rec t1 t2
end.

Lemma list_neq_rec_spec :
  forall (A : Type) (l1 l2 : list A),
    list_neq_rec l1 l2 -> l1 <> l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1];
  destruct l2 as [| h2 t2];
  cbn; intros.
    contradiction.
    congruence.
    congruence.
    inversion 1; subst. destruct H.
      contradiction.
      apply (IHt1 _ H). reflexivity.
Qed.
(* end hide *)

(** ** Nierówność list - induktywnie *)

Inductive list_neq_ind {A : Type} : list A -> list A -> Prop :=
    | nil_cons : forall h t, list_neq_ind nil (cons h t)
    | cons_nil : forall h t, list_neq_ind (cons h t) nil
    | cons_cons1 :
        forall h1 h2 t1 t2,
          h1 <> h2 -> list_neq_ind (cons h1 t1) (cons h2 t2)
    | cons_cons2 :
        forall h1 h2 t1 t2,
          list_neq_ind t1 t2 -> list_neq_ind (cons h1 t1) (cons h2 t2).

Lemma list_neq_ind_spec :
  forall {A : Type} (l1 l2 : list A),
    list_neq_ind l1 l2 -> l1 <> l2.
Proof.
  induction 1; cbn; congruence.
Qed.

Lemma list_neq_ind_list_neq_rec :
  forall {A : Type} (l1 l2 : list A),
    list_neq_ind l1 l2 -> list_neq_rec l1 l2.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; inversion_clear 1.
  1-2: trivial.
  - left. assumption.
  - right. apply IHt1. assumption.
Qed.

(** ** Różność (słaby apartheid) list - rekursywnie *)

Fixpoint list_apart_rec
  {A : Type} (R : A -> A -> Prop) (l1 l2 : list A) : Prop :=
match l1, l2 with
    | [], [] => False
    | h1 :: t1, h2 :: t2 => R h1 h2 \/ list_apart_rec R t1 t2
    | _, _ => True
end.

Lemma list_apart_list_neq_rec :
  forall {A : Type} (R : A -> A -> Prop) (l1 l2 : list A),
    (forall x y : A, R x y -> x <> y) ->
      list_apart_rec R l1 l2 -> list_neq_rec l1 l2.
Proof.
  induction l1 as [| h1 t1 IH]; destruct l2 as [| h2 t2]; cbn; firstorder.
Qed.

(** ** Różność (silny apartheid) list - rekursywnie *)

Fixpoint list_strong_apart_rec
  {A : Type} (R : A -> A -> Type) (l1 l2 : list A) : Type :=
match l1, l2 with
    | [], [] => False
    | h1 :: t1, h2 :: t2 => R h1 h2 + list_strong_apart_rec R t1 t2
    | _, _ => True
end.

Lemma list_strong_apart_rec_list_apart :
  forall {A : Type} (R : A -> A -> Prop) (l1 l2 : list A),
    (forall x y : A, R x y -> x <> y) ->
      list_strong_apart_rec R l1 l2 -> list_apart_rec R l1 l2.
Proof.
  induction l1 as [| h1 t1 IH]; destruct l2 as [| h2 t2]; cbn; firstorder.
Qed.

(** ** Różność list - induktywnie *)

Module list_neq_ind.

Inductive list_neq
  {A : Type} (R : A -> A -> Type) : list A -> list A -> Type :=
    | nc : forall (h : A) (t : list A), list_neq R [] (h :: t)
    | cn : forall (h : A) (t : list A), list_neq R (h :: t) []
    | cc1 : forall (h1 h2 : A) (t1 t2 : list A),
              R h1 h2 -> list_neq R (h1 :: t1) (h2 :: t2)
    | cc2 : forall (h1 h2 : A) (t1 t2 : list A),
              list_neq R t1 t2 -> list_neq R (h1 :: t1) (h2 :: t2).

#[global] Hint Constructors list_neq : core.

Lemma list_neq_irrefl_aux :
  forall {A : Type} {R : A -> A -> Prop} (l1 l2 : list A),
    (forall x : A, R x x -> False) ->
      list_neq R l1 l2 -> l1 <> l2.
(* begin hide *)
Proof.
  induction 2; inversion 1; subst.
    apply (H _ r).
    apply IHX. reflexivity.
Defined.
(* end hide *)

Lemma list_neq_irrefl_sym :
  forall {A : Type} {R : A -> A -> Prop} (l1 l2 : list A),
    (forall x y : A, R x y -> R y x) ->
      list_neq R l1 l2 -> list_neq R l2 l1.
(* begin hide *)
Proof.
  induction 2.
    1-3: constructor. apply H. assumption.
    constructor 4. assumption.
Defined.
(* end hide *)

Lemma list_neq_cotrans :
  forall {A : Type} {R : A -> A -> Prop} (l1 l3 : list A),
    (forall x y z : A, R x z -> R x y + R y z) ->
      list_neq R l1 l3 -> forall l2 : list A,
        list_neq R l1 l2 + list_neq R l2 l3.
(* begin hide *)
Proof.
  induction 2; intros.
    destruct l2; [right | left]; constructor.
    destruct l2; [left | right]; constructor.
    destruct l2 as [| h t].
      left. constructor.
      destruct (X _ h _ r).
        left. constructor. assumption.
        right. constructor. assumption.
    destruct l2 as [| h t].
      left. constructor.
      destruct (IHX0 t).
        left. constructor 4. assumption.
        right. constructor 4. assumption.
Defined.
(* end hide *)

Inductive Exists2
  {A : Type} (R : A -> A -> Type) : list A -> list A -> Type :=
    | E2_here :
        forall {h1 h2 : A} (t1 t2 : list A),
          R h1 h2 -> Exists2 R (h1 :: t1) (h2 :: t2)
    | E2_there :
        forall {h1 h2 : A} {t1 t2 : list A},
          Exists2 R t1 t2 -> Exists2 R (h1 :: t1) (h2 :: t2).

Lemma Exists2_list_neq :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    Exists2 R l1 l2 -> list_neq R l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor. assumption.
    constructor 4. assumption.
Qed.
(* end hide *)

Inductive DifferentStructure
  {A : Type} : list A -> list A -> Type :=
    | DS_nc :
        forall (h : A) (t : list A),
          DifferentStructure [] (h :: t)
    | DS_cn :
        forall (h : A) (t : list A),
          DifferentStructure (h :: t) []
    | DS_cc :
        forall (h1 h2 : A) {t1 t2 : list A},
          DifferentStructure t1 t2 ->
            DifferentStructure (h1 :: t1) (h2 :: t2).

(** Insajt, że o ja pierdole: [list_neq] to w sumie [Exists2] lub
    [DifferentStructure], czyli listy różnią się, gdy różnią się
    na którymś elemencie lub mają różną długość. *)

Lemma lnE2 :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    list_neq R l1 l2 -> Exists2 R l1 l2 + DifferentStructure l1 l2.
(* begin hide *)
Proof.
  induction 1.
    right. constructor.
    right. constructor.
    left. constructor. assumption.
    destruct IHX.
      left. constructor 2. assumption.
      right. constructor. assumption.
Defined.
(* end hide *)

Lemma lnE2_conv :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    Exists2 R l1 l2 + DifferentStructure l1 l2 -> list_neq R l1 l2.
(* begin hide *)
Proof.
  destruct 1.
    induction e.
      constructor. assumption.
      constructor 4. assumption.
    induction d.
      constructor.
      constructor.
      constructor 4. assumption.
Defined.
(* end hide *)

Lemma okurwa :
  forall
    (A : Type) (R : A -> A -> Type) (h1 h2 : A) (t1 t2 : list A)
    (r1 : R h1 h2) (r2 : R h1 h2),
      @inl _
        (DifferentStructure (h1 :: t1) (h2 :: t2))
        (E2_here R t1 t2 r1)
      =
      inl (E2_here R t1 t2 r2) ->
        r1 = r2.
(* begin hide *)
Proof.
  assert (forall (A B : Type) (x y : A), @inl A B x = inl y -> x = y).
    inversion 1. reflexivity.
  intros. apply H in H0.
  apply (f_equal
    (fun x : Exists2 R (h1 :: t1) (h2 :: t2) =>
      match x with
          | E2_here _ _ _ r => Some r
          | _             => None
      end))
  in H0.
  inversion H0. reflexivity.
Qed.
(* end hide *)

Lemma lnE2_lnE2_conv :
  forall
    {A : Type} {R : A -> A -> Prop} {l1 l2 : list A}
    (c : list_neq R l1 l2),
      lnE2_conv (lnE2 c) = c.
(* begin hide *)
Proof.
  induction c; cbn.
    1-3: reflexivity.
    destruct (list_neq_rect A R _) eqn: Heq.
      cbn. f_equal. induction e; cbn in *.
        dependent destruction c; cbn in *.
          f_equal. symmetry. apply okurwa in Heq. assumption.
          cbn in *. rewrite Heq in IHc. cbn in IHc. inversion IHc.
        dependent destruction c.
          cbn in *. inversion Heq.
          cbn in *. rewrite Heq in IHc. cbn in IHc. assumption.
      cbn. f_equal. dependent destruction c; cbn in *.
        inversion Heq; subst; cbn. reflexivity.
        inversion Heq; subst; cbn. reflexivity.
        inversion Heq.
        rewrite Heq in IHc. cbn in IHc. assumption.
Qed.
(* end hide *)

Lemma lnE2_conv_lnE2 :
  forall
    {A : Type} {R : A -> A -> Prop} {l1 l2 : list A}
    (x : Exists2 R l1 l2 + DifferentStructure l1 l2),
      lnE2 (lnE2_conv x) = x.
(* begin hide *)
Proof.
  destruct x.
    induction e; cbn in *.
      reflexivity.
      destruct (list_neq_rect A R _); inversion IHe. reflexivity.
    induction d; cbn in *.
      reflexivity.
      reflexivity.
      destruct (list_neq_rect A R _); inversion IHd. reflexivity.
Qed.
(* end hide *)

Inductive DifferentStructure'
  {A : Type} : list A -> list A -> SProp :=
    | DS'_nc :
        forall (h : A) (t : list A),
          DifferentStructure' [] (h :: t)
    | DS'_cn :
        forall (h : A) (t : list A),
          DifferentStructure' (h :: t) []
    | DS'_cc :
        forall (h1 h2 : A) {t1 t2 : list A},
          DifferentStructure' t1 t2 ->
            DifferentStructure' (h1 :: t1) (h2 :: t2).

Lemma DS_DS' :
  forall {A : Type} {l1 l2 : list A},
    DifferentStructure l1 l2 -> DifferentStructure' l1 l2.
(* begin hide *)
Proof.
  induction 1; constructor; assumption.
Qed.
(* end hide *)

Inductive sEmpty : SProp := .

Lemma sEmpty_rec' :
  forall A : Type, sEmpty -> A.
(* begin hide *)
Proof.
  destruct 1.
Qed.
(* end hide *)

Lemma DS'_spec :
  forall {A : Type} {l1 l2 : list A},
    DifferentStructure' l1 l2 -> l1 <> l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1];
  destruct l2 as [| h2 t2];
  cbn; intros H Heq; inv Heq.
    apply sEmpty_rec'. inv H.
    apply (IHt1 t2).
      inv H. assumption.
      reflexivity.
Defined.
(* end hide *)

Lemma DS'_DS :
  forall {A : Type} {l1 l2 : list A},
    DifferentStructure' l1 l2 -> DifferentStructure l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1];
  destruct l2 as [| h2 t2];
  cbn; intros; try constructor.
    apply sEmpty_rec'. inv H.
    apply IHt1. inv H. assumption.
Defined.
(* end hide *)

Lemma isProp_DS :
  forall
    {A : Type} {l1 l2 : list A}
    (p q : DifferentStructure l1 l2),
      p = q.
(* begin hide *)
Proof.
  induction p; intro q.
    refine (match q with DS_nc _ _   => _ end). reflexivity.
    refine (match q with DS_cn _ _   => _ end). reflexivity.
    dependent destruction q. f_equal. apply IHp.
Qed.
(* end hide *)

Lemma DS_DS'_DS :
  forall {A : Type} {l1 l2 : list A} (p : DifferentStructure l1 l2),
    DS'_DS (DS_DS' p) = p.
(* begin hide *)
Proof.
  intros. apply isProp_DS.
Qed.
(* end hide *)

Lemma DS'_DS_DS' :
  forall {A : Type} {l1 l2 : list A} (p : DifferentStructure' l1 l2),
    DS_DS' (DS'_DS p) = p.
Proof.
  reflexivity.
Abort.

Inductive sor (A : Type) (B : SProp) : Type :=
    | sinl : A -> sor A B
    | sinr : B -> sor A B.

Arguments sinl {A B} _.
Arguments sinr {A B} _.

Lemma lnE2' :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    list_neq R l1 l2 -> sor (Exists2 R l1 l2) (DifferentStructure' l1 l2).
(* begin hide *)
Proof.
  induction 1.
    right. constructor.
    right. constructor.
    left. constructor. assumption.
    destruct IHX.
      left. constructor 2. assumption.
      right. constructor. assumption.
Defined.
(* end hide *)

Lemma lnE2'_conv :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    sor (Exists2 R l1 l2) (DifferentStructure' l1 l2) -> list_neq R l1 l2.
(* begin hide *)
Proof.
  destruct 1.
    induction e.
      constructor. assumption.
      constructor 4. assumption.
    revert l2 d.
    induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; intro.
      apply sEmpty_rec'. inv d.
      constructor.
      constructor.
      constructor 4. apply IHt1. inv d. assumption.
Defined.
(* end hide *)

Lemma okurwa' :
  forall
    (A : Type) (R : A -> A -> Type) (h1 h2 : A) (t1 t2 : list A)
    (r1 : R h1 h2) (r2 : R h1 h2),
      @sinl _
        (DifferentStructure' (h1 :: t1) (h2 :: t2))
        (E2_here R t1 t2 r1)
      =
      sinl (E2_here R t1 t2 r2) ->
        r1 = r2.
(* begin hide *)
Proof.
  assert (forall A B (x y : A), @sinl A B x = sinl y -> x = y).
    inversion 1. reflexivity.
  intros. apply H in H0.
  apply (f_equal
    (fun x : Exists2 R (h1 :: t1) (h2 :: t2) =>
      match x with
          | E2_here _ _ _ r => Some r
          | _             => None
      end))
  in H0.
  inversion H0. reflexivity.
Qed.
(* end hide *)

Lemma lnE2'_lnE2'_conv :
  forall
    {A : Type} {R : A -> A -> Prop} {l1 l2 : list A}
    (c : list_neq R l1 l2),
      lnE2'_conv (lnE2' c) = c.
(* begin hide *)
Proof.
  induction c; cbn.
    1-3: reflexivity.
    destruct (list_neq_rect A R _) eqn: Heq.
      cbn. f_equal. induction e; cbn in *.
        dependent destruction c; cbn in *.
          f_equal. symmetry. apply okurwa' in Heq. assumption.
          cbn in *. rewrite Heq in IHc. cbn in IHc. inversion IHc.
        dependent destruction c.
          cbn in *. inversion Heq.
          cbn in *. rewrite Heq in IHc. cbn in IHc. assumption.
      cbn. f_equal. dependent destruction c; cbn in *.
        inversion Heq; subst; cbn. reflexivity.
        inversion Heq; subst; cbn. reflexivity.
        inversion Heq.
        rewrite Heq in IHc. cbn in IHc. assumption.
Qed.
(* end hide *)

Lemma lnE2'_conv_lnE2' :
  forall
    {A : Type} {R : A -> A -> Prop} {l1 l2 : list A}
    (x : sor (Exists2 R l1 l2) (DifferentStructure' l1 l2)),
      lnE2' (lnE2'_conv x) = x.
Proof.
  destruct x.
    induction e; cbn in *.
      reflexivity.
      destruct (list_neq_rect A R _); inversion IHe. reflexivity.
    revert l2 d.
    induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; intro.
      apply sEmpty_rec. inv d.
      reflexivity.
      reflexivity.
Abort.

(** Wnioski: próba użycia tutaj [SProp] jest bardzo poroniona. *)

End list_neq_ind.

(** ** Nierówność liczb konaturalnych - induktywnie *)

From Typonomikon Require F2.

Module conat_neq.

Import F2.

Inductive conat_neq : conat -> conat -> Prop :=
    | cnzs :
        forall c : conat, conat_neq zero (succ c)
    | cnsz :
        forall c : conat, conat_neq (succ c) zero
    | cnss :
        forall n m : conat, conat_neq n m -> conat_neq (succ n) (succ m).

Lemma conat_neq_spec :
  forall n m : conat,
    conat_neq n m -> n <> m.
(* begin hide *)
Proof.
  induction 1; intro Heq; inversion Heq; congruence.
Qed.
(* end hide *)

Lemma conat_neq_irrefl :
  forall n : conat, ~ conat_neq n n.
(* begin hide *)
Proof.
  intros n Hneq. eapply conat_neq_spec; eauto.
Qed.
(* end hide *)

End conat_neq.

(** ** Nierówność strumieni *)

From Typonomikon Require F3.

Module Stream_neq.

Import F3.

Inductive Stream_neq
  {A : Type} : Stream A -> Stream A -> Type :=
    | Stream_apart_hd' :
        forall t1 t2 : Stream A,
          hd t1 <> hd t2 -> Stream_neq t1 t2
    | Stream_apart_tl' :
        forall t1 t2 : Stream A,
          Stream_neq (tl t1) (tl t2) -> Stream_neq t1 t2.

Lemma Stream_neq_not_sim :
  forall {A : Type} {s1 s2 : Stream A},
    Stream_neq s1 s2 -> ~ sim s1 s2.
(* begin hide *)
Proof.
  induction 1; intros []; contradiction.
Qed.
(* end hide *)

Lemma Stream_neq_neq :
  forall {A : Type} {s1 s2 : Stream A},
    Stream_neq s1 s2 -> s1 <> s2.
(* begin hide *)
Proof.
  induction 1; intros ->; contradiction.
Qed.
(* end hide *)

End Stream_neq.

(** ** Różność (słaby apartheid) strumieni - induktywnie *)

From Typonomikon Require F3.

Module Stream_apart.

Import F3 Stream_neq.

Inductive Stream_apart
  {A : Type} (R : A -> A -> Prop) : Stream A -> Stream A -> Type :=
    | Stream_apart_hd :
        forall (h1 h2 : A) (t1 t2 : Stream A),
          R h1 h2 -> Stream_apart R (scons h1 t1) (scons h2 t2)
    | Stream_apart_tl :
        forall (h1 h2 : A) (t1 t2 : Stream A),
          Stream_apart R t1 t2 -> Stream_apart R (scons h1 t1) (scons h2 t2).

Lemma Stream_apart_not_sim :
  forall {A : Type} {R : A -> A -> Prop} {s1 s2 : Stream A},
    (forall x : A, ~ R x x) ->
      Stream_apart R s1 s2 -> ~ sim s1 s2.
(* begin hide *)
Proof.
  induction 2; intros Hsim; inversion Hsim; cbn in *; subst; clear Hsim.
  - apply (H h2). assumption.
  - contradiction.
Qed.
(* end hide *)

Lemma Stream_neq_Stream_apart :
  forall {A : Type} {s1 s2 : Stream A},
    Stream_neq s1 s2 ->
      Stream_apart (fun x y => x <> y) s1 s2.
(* begin hide *)
Proof.
  induction 1.
  - destruct t1, t2. cbn in *. left. assumption.
  - destruct t1, t2. cbn in *. right. assumption.
Qed.
(* end hide *)

Lemma Stream_apart_Stream_neq :
  forall {A : Type} {R : A -> A -> Prop} {s1 s2 : Stream A},
    (forall x : A, ~ R x x) ->
      Stream_apart R s1 s2 -> Stream_neq s1 s2.
(* begin hide *)
Proof.
  induction 2.
  - left. cbn. intro. subst. apply (H _ r).
  - right. cbn. assumption.
Qed.
(* end hide *)

End Stream_apart.

(** ** Różność (silny apartheid) strumieni - induktywnie *)

From Typonomikon Require F3.

Module Stream_strong_apart.

Import F3 Stream_apart.

Inductive Stream_strong_apart
  {A : Type} (R : A -> A -> Type) : Stream A -> Stream A -> Type :=
    | Stream_strong_apart_hd :
        forall s1 s2 : Stream A,
          R (hd s1) (hd s2) -> Stream_strong_apart R s1 s2
    | Stream_strong_apart_tl :
        forall s1 s2 : Stream A,
          Stream_strong_apart R (tl s1) (tl s2) -> Stream_strong_apart R s1 s2.

Lemma Stream_strong_apart_spec :
  forall {A : Type} {R : A -> A -> Prop} {s1 s2 : Stream A},
    (forall x : A, ~ R x x) ->
      Stream_strong_apart R s1 s2 -> Stream_apart R s1 s2.
(* begin hide *)
Proof.
  intros A R s1 s2 HR HSsa; induction HSsa.
  - destruct s1, s2; cbn in *; left. assumption.
  - destruct s1, s2; cbn in *; right. assumption.
Qed.
(* end hide *)

End Stream_strong_apart.

(** ** Różność kolist *)

From Typonomikon Require F4.

Module CoList_apart.

Import F4.

Inductive CoList_apart {A : Type} (R : A -> A -> Type) (l1 l2 : CoList A) : Type :=
    | CLa_nil_cons :
        uncons l1 = NilF -> uncons l2 <> NilF -> CoList_apart R l1 l2
    | CLa_cons_nil :
        uncons l1 <> NilF -> uncons l2 = NilF -> CoList_apart R l1 l2
    | CLa_head :
        forall
          {h1 : A} {t1 : CoList A} (Hu1 : uncons l1 = ConsF h1 t1)
          {h2 : A} {t2 : CoList A} (Hu2 : uncons l2 = ConsF h2 t2),
            R h1 h2 -> CoList_apart R l1 l2
    | CLa_tail :
        forall
          {h1 : A} {t1 : CoList A} (Hu1 : uncons l1 = ConsF h1 t1)
          {h2 : A} {t2 : CoList A} (Hu2 : uncons l2 = ConsF h2 t2),
            CoList_apart R t1 t2 -> CoList_apart R l1 l2.

Lemma CoList_apart_spec :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 : CoList A},
    (forall x : A, R x x -> False) ->
      CoList_apart R l1 l2 -> ~ lsim l1 l2.
(* begin hide *)
Proof.
  intros A R l1 l2 HR; induction 1; intros [Hlsim].
  - inversion Hlsim; subst; clear Hlsim; congruence.
  - inversion Hlsim; subst; clear Hlsim; congruence.
  - inversion Hlsim; subst; clear Hlsim.
    + congruence.
    + apply (HR h3). congruence.
  - inversion Hlsim; subst; clear Hlsim; congruence.
Qed.
(* end hide *)

End CoList_apart.

(** ** Różność funkcji *)

(** Funkcje są różne (w silnym sensie), gdy różnią się dla jakiegoś
    argumentu. *)

Inductive fun_apart
  {A B : Type} (R : B -> B -> Type) (f g : A -> B) : Type :=
    | fun_apart' : forall {x : A}, R (f x) (g x) -> fun_apart R f g.

Lemma fun_apart_spec :
  forall {A B : Type} (R : B -> B -> Type) (f g : A -> B),
    (forall x : B, R x x -> False) ->
      fun_apart R f g -> f <> g.
(* begin hide *)
Proof.
  intros A B R f g HR [x r] ->.
  apply (HR (g x)). apply r.
Qed.
(* end hide *)

Lemma fun_apart_spec' :
  forall {A B : Type} (R : B -> B -> Type) (f g : A -> B),
    (forall x : B, R x x -> False) ->
      fun_apart R f g -> ~ (forall x : A, f x = g x).
(* begin hide *)
Proof.
  intros A B R f g HR [x r] Hext.
  apply (HR (g x)). rewrite <- Hext at 1. assumption.
Qed.
(* end hide *)

Inductive dep_fun_apart
  {A : Type} {B : A -> Type}
  (R : forall x : A, B x -> B x -> Type)
  (f g : forall x : A, B x) : Type :=
    | dep_fun_apart' : forall {x : A}, R x (f x) (g x) -> dep_fun_apart R f g.

Lemma dep_fun_apart_spec :
  forall
    {A : Type} {B : A -> Type}
    (R : forall x : A, B x -> B x -> Type)
    (f g : forall x : A, B x)
    (HR : forall {x : A} (y : B x), R x y y -> False),
      dep_fun_apart R f g -> f <> g.
(* begin hide *)
Proof.
  intros A B R f g HR [x r] ->.
  apply (HR _ (g x)). apply r.
Qed.
(* end hide *)

Lemma dep_fun_apart_spec' :
  forall
    {A : Type} {B : A -> Type}
    (R : forall x : A, B x -> B x -> Type)
    (f g : forall x : A, B x)
    (HR : forall {x : A} (y : B x), R x y y -> False),
      dep_fun_apart R f g -> ~ (forall x : A, f x = g x).
(* begin hide *)
Proof.
  intros A B R f g HR [x r] Hext.
  apply (HR _ (g x)). rewrite <- Hext at 1. assumption.
Qed.
(* end hide *)

(** * Protokoły różnicowe *)

Module DiffProtocols.

Print list_neq_ind.list_neq.

(** [list_neq_ind.list_neq] to pokazanie na odpowiadające sobie miejsca w
    dwóch listach, które różnią się znajdującym się tam elementem. *)

Inductive ListDiffProtocol
  {A : Type} (R : A -> A -> Type) : list A -> list A -> Type :=
    | nn' : ListDiffProtocol R [] []
    | nc' : forall (h : A) (t : list A), ListDiffProtocol R [] (h :: t)
    | cn' : forall (h : A) (t : list A), ListDiffProtocol R (h :: t) []
    | cc1' : forall (h1 h2 : A) (t1 t2 : list A),
              R h1 h2 -> ListDiffProtocol R t1 t2 ->
                ListDiffProtocol R (h1 :: t1) (h2 :: t2)
    | cc2' : forall (h : A) (t1 t2 : list A),
              ListDiffProtocol R t1 t2 ->
                ListDiffProtocol R (h :: t1) (h :: t2).

(** [ListDiffProtocol] to sprawozdanie mówiące, w których miejscach listy
    się różnią, a w których są takie same (i od którego miejsca jedna jest
    dłuższa od drugiej).

    Spróbujmy udowodnić, że jeżeli elementy mogą się różnić tylko na
    jeden sposób, to protokół jest unikalny. *)

Lemma isProp_ListDiffProtocol :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    (forall (x y : A) (p q : R x y), p = q) ->
    (forall x : A, ~ R x x) ->
      forall p q : ListDiffProtocol R l1 l2, p = q.
Proof.
  induction p; dependent destruction q; try reflexivity; f_equal.
    apply H.
    apply IHp.
    destruct (H0 _ r).
    destruct (H0 _ r).
    apply IHp.
Qed.

(** Protokoły są zwrotne i symetryczne, ale niekoniecznie przechodnie. *)

Lemma proto_refl :
  forall {A : Type} {R : A -> A -> Type} (l : list A),
    ListDiffProtocol R l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    constructor 5. assumption.
Qed.
(* end hide *)

Lemma proto_sym :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 : list A},
    (forall x y : A, R x y -> R y x) ->
      ListDiffProtocol R l1 l2 -> ListDiffProtocol R l2 l1.
(* begin hide *)
Proof.
  induction 2.
    1-4: constructor.
      apply X. assumption.
      assumption.
    constructor 5. assumption.
Qed.
(* end hide *)

#[global] Hint Constructors ListDiffProtocol : core.

Lemma proto_trans :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 l3 : list A},
    (forall x y z : A, R x y -> R y z -> R x z) ->
      ListDiffProtocol R l1 l2 -> ListDiffProtocol R l2 l3 ->
        ListDiffProtocol R l1 l3.
Proof.
  intros * H HLDP. revert l3.
  induction HLDP; inversion 1; subst; auto.
    admit.
Abort.

(** Protokół różnicowy dla funkcji mówi, dla których argumentów wyniki
    są takie same, a dla których są różne. *)

Definition FunDiffProtocol
  {A B : Type} (R : B -> B -> Prop) (f g : A -> B) : Type :=
    forall x : A, f x = g x \/ R (f x) (g x).

End DiffProtocols.