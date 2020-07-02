(** * H2: Równość i ścieżki [TODO] *)

Set Universe Polymorphism.

Require Import Arith.
Require Import Bool.

(** * Ścieżki w typach induktywnych *)

(** ** Ścieżki między liczbami naturalnymi - rekurencyjnie *)

Module nat_eq_rec.

Fixpoint code (n m : nat) : Type :=
match n, m with
    | 0, 0 => unit
    | S _, 0 => Empty_set
    | 0, S _ => Empty_set
    | S n', S m' => code n' m'
end.

Fixpoint encode_aux (n : nat) : code n n :=
match n with
    | 0 => tt
    | S n' => encode_aux n'
end.

Definition encode {n m : nat} (p : n = m) : code n m :=
match p with
    | eq_refl => encode_aux n
end.

Fixpoint decode {n m : nat} : code n m -> n = m :=
match n, m with
    | 0, 0 => fun _ => eq_refl
    | 0, S _ => fun c => match c with end
    | S _, 0 => fun c => match c with end
    | S n', S m' => fun c => @f_equal _ _ S _ _ (@decode n' m' c)
end.

Lemma decode_encode :
  forall (n m : nat) (p : n = m),
    decode (encode p) = p.
(* begin hide *)
Proof.
  destruct p; cbn.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma isProp_code :
  forall (n m : nat) (c1 c2 : code n m), c1 = c2.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m']; cbn; try destruct c1, c2.
    reflexivity.
    intros. apply IHn'.
Qed.
(* end hide *)

Lemma encode_decode :
  forall (n m : nat) (c : code n m),
    encode (decode c) = c.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m']; cbn; try destruct c.
    reflexivity.
    intro. apply isProp_code.
Qed.
(* end hide *)

Lemma K_nat :
  forall (n : nat) (p : n = n), p = eq_refl.
(* begin hide *)
Proof.
  intros. rewrite <- (decode_encode _ _ p).
  replace (encode p) with (encode_aux n).
    induction n as [| n']; cbn.
      reflexivity.
      rewrite IHn'.
        cbn. reflexivity.
        reflexivity.
    apply isProp_code.
Qed.
(* end hide *)

End nat_eq_rec.

(** ** Ścieżki między liczbami naturalnymi - induktywnie *)

Module nat_eq_ind.

Inductive nat_eq : nat -> nat -> Prop :=
    | nat_eq_0 : nat_eq 0 0
    | nat_eq_S : forall {n m : nat}, nat_eq n m -> nat_eq (S n) (S m).

Fixpoint encode' (n : nat) : nat_eq n n :=
match n with
    | 0 => nat_eq_0
    | S n' => nat_eq_S (encode' n')
end.

Definition encode {n m : nat} (p : n = m) : nat_eq n m :=
match p with
    | eq_refl => encode' n
end.

Fixpoint decode {n m : nat} (c : nat_eq n m) : n = m :=
match c with
    | nat_eq_0 => eq_refl
    | nat_eq_S c' => f_equal S (decode c')
end.

Lemma encode_decode :
  forall {n m : nat} (p : n = m),
    decode (encode p) = p.
(* begin hide *)
Proof.
  destruct p. cbn.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Scheme nat_eq_ind' := Induction for nat_eq Sort Prop.

Lemma decode_encode :
  forall {n m : nat} (c : nat_eq n m),
    encode (decode c) = c.
(* begin hide *)
Proof.
  induction c using nat_eq_ind'; cbn.
    reflexivity.
    destruct (decode c) eqn: H. cbn in *. rewrite IHc. reflexivity.
Qed.
(* end hide *)

End nat_eq_ind.

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

Require Import FunctionalExtensionality.

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

Module nat_neq_ind.

Inductive nat_neq : nat -> nat -> Type :=
    | ZS : forall n : nat, nat_neq 0 (S n)
    | SZ : forall n : nat, nat_neq (S n) 0
    | SS : forall n m : nat, nat_neq n m -> nat_neq (S n) (S m).

Arguments ZS {n}.
Arguments SZ {n}.
Arguments SS {n m} _.

Require Import Equality.

Lemma isProp_nat_neq :
  forall {n m : nat} (p q : nat_neq n m), p = q.
Proof.
  induction p; dependent destruction q.
    reflexivity.
    reflexivity.
    apply f_equal, IHp.
Qed.

(* begin hide *)
(** TODO *)
(*Fixpoint encode {n m : nat} (p n <> m) : nat_neq n m
match p with
    | ZS => I
    | SZ => I
    | SS p' => encode p'
end.

Fixpoint encode {n m : nat} : n <> m -> nat_neq n m.
match n, m with
    | 0, 0 => fun c : 0 <> 0 => match c eq_refl with end
    | 0, S _ => fun _ => ZS
    | S _, 0 => fun _ => SZ
    | S n', S m' => fun c : S n' <> S m' => SS (@decode n' m' c)
end.

Lemma encode_decode :
  forall {n m : nat} (p : nat_neq n m),
    decode (encode p) = p.
(* begin hide *)
Proof.
  induction p; cbn.
    1-2: reflexivity.
    rewrite IHp. reflexivity.
Qed.
(* end hide *)

Lemma decode_encode :
  forall {n m : nat} (c : code n m),
    encode (decode c) = c.
(* begin hide *)
Proof.
  induction n as [| n'], m as [| m']; cbn.
    destruct c.
    1-2: destruct c; reflexivity.
    intro c. apply IHn'.
Qed.
(* end hide *)
*)
(* end hide *)

End nat_neq_ind.

Module nat_eq_neq.

Import nat_eq_ind.

Import nat_neq_ind.

Lemma nat_eq_dec :
  forall n m : nat, nat_eq n m + nat_neq n m.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'].
    left. constructor.
    right. constructor.
    right. constructor.
    destruct (IHn' m').
      left. constructor. assumption.
      right. constructor. assumption.
Qed.
(* end hide *)

End nat_eq_neq.

(** ** Ścieżki między listami *)

Require Import D5.

Module list_eq_ind.

(** Kody nie muszą być rekurencyjne - mogą być induktywne. *)

Inductive code {A : Type} : list A -> list A -> Prop :=
    | nils : code [] []
    | conss :
        forall {h1 h2 : A} {t1 t2 : list A},
          h1 = h2 -> code t1 t2 -> code (h1 :: t1) (h2 :: t2).

Fixpoint encode' {A : Type} (l : list A) : code l l :=
match l with
    | [] => nils
    | h :: t => conss eq_refl (encode' t)
end.

Definition encode
  {A : Type} {l1 l2 : list A} (p : l1 = l2) : code l1 l2 :=
match p with
    | eq_refl => encode' l1
end.

Definition decode' {A : Type} {l1 l2 : list A} (c : code l1 l2) : l1 = l2.
(* begin hide *)
Proof.
  induction c.
    reflexivity.
    exact (f_equal2 (@cons A) H IHc).
Qed.
(* end hide *)

Fixpoint decode {A : Type} {l1 l2 : list A} (c : code l1 l2) : l1 = l2 :=
match c with
    | nils => eq_refl
    | conss p c' =>
        match p, decode c' with
            | eq_refl, eq_refl => eq_refl
        end
end.

Lemma encode_decode :
  forall {A : Type} {l1 l2 : list A} (p : l1 = l2),
    decode (encode p) = p.
(* begin hide *)
Proof.
  destruct p. cbn.
  induction l1 as [| h t]; cbn.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Scheme code_ind' := Induction for code Sort Prop.

Lemma decode_encode :
  forall {A : Type} {l1 l2 : list A} (c : code l1 l2),
    encode (decode c) = c.
(* begin hide *)
Proof.
  induction c using code_ind'; cbn.
    reflexivity.
    destruct e. destruct (decode c). cbn in *. rewrite IHc. reflexivity.
Qed.
(* end hide *)

End list_eq_ind.

Module list_eq_forall.

Definition code {A : Type} (l1 l2 : list A) : Prop :=
  forall n : nat, nth n l1 = nth n l2.

Definition encode
  {A : Type} {l1 l2 : list A} (p : l1 = l2) : code l1 l2 :=
match p with
    | eq_refl => fun n => eq_refl
end.

Definition decode {A : Type} {l1 l2 : list A} (c : code l1 l2) : l1 = l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    specialize (c 0). cbn in c. destruct l2.
Abort.
(* end hide *)

End list_eq_forall.

(** ** Nierówność list *)

Module list_neq.

Inductive list_neq
  {A : Type} (R : A -> A -> Type) : list A -> list A -> Type :=
    | nc : forall (h : A) (t : list A), list_neq R [] (h :: t)
    | cn : forall (h : A) (t : list A), list_neq R (h :: t) []
    | cc1 : forall (h1 h2 : A) (t1 t2 : list A),
              R h1 h2 -> list_neq R (h1 :: t1) (h2 :: t2)
    | cc2 : forall (h1 h2 : A) (t1 t2 : list A),
              list_neq R t1 t2 -> list_neq R (h1 :: t1) (h2 :: t2).

Hint Constructors list_neq.

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

End list_neq.

(** * Ścieżki w typach koinduktywnych *)

(** ** Nierówność strumieni *)

Module Stream_neq.

Require Import F3.

Inductive Stream_neq
  {A : Type} (R : A -> A -> Prop) : Stream A -> Stream A -> Type :=
    | sn_here :
        forall (h1 h2 : A) (t1 t2 : Stream A),
          R h1 h2 -> Stream_neq R (scons h1 t1) (scons h2 t2)
    | sn_there :
        forall (h1 h2 : A) (t1 t2 : Stream A),
          Stream_neq R t1 t2 -> Stream_neq R (scons h1 t1) (scons h2 t2).

Lemma Stream_neq_not_sim :
  forall {A : Type} {R : A -> A -> Prop} {s1 s2 : Stream A},
    (forall x : A, ~ R x x) ->
      Stream_neq R s1 s2 -> ~ sim s1 s2.
(* begin hide *)
Proof.
  induction 2.
    inversion 1. cbn in *. subst. apply (H h2). assumption.
    inversion 1. cbn in *. contradiction.
Qed.
(* end hide *)

End Stream_neq.

(** * Ścieżki między funkcjami *)

(** * Ścieżki w uniwersum *)

(** ** Ćwiczenia *)

(** **** Ćwiczenie *)

(** Miło by było pamiętać, że Coq to nie jest jakiś tam biedajęzyk
    programowania, tylko pełnoprawny system podstaw matematyki (no,
    prawie...). W związku z tym pokaż, że [nat <> Type]. *)

Module nat_not_Type.

Definition idtoeqv {A B : Type} (p : A = B) : A -> B.
(* begin hide *)
Proof.
  destruct p. intro x. exact x.
Defined.
(* end hide *)

Lemma idtoeqv_sur :
  forall (A B : Type) (p : A = B) (b : B),
    exists a : A, idtoeqv p a = b.
(* begin hide *)
Proof.
  destruct p. intro a. exists a. reflexivity.
Qed.
(* end hide *)

Definition wut
  (f : nat -> Type) (n : nat) (h : f n -> forall m : nat, f m -> bool)
  : forall k : nat, f k -> bool.
(* begin hide *)
Proof.
  intros k x. destruct (Nat.eqb_spec n k).
    destruct e. exact (negb (h x n x)).
    exact true.
Defined.
(* end hide *)

Theorem nat_not_Type : ~ @eq Type nat Type.
(* begin hide *)
Proof.
  intro p.
  pose (f := idtoeqv p). pose (idtoeqv_sur _ _ p).
  change (idtoeqv p) with f in e. clearbody f e.
  pose (A := forall n : nat, f n -> bool).
  destruct (e A) as [n q].
  pose (h := idtoeqv q). pose (e' := idtoeqv_sur _ _ q).
  change (idtoeqv q) with h in e'; clearbody h e'.
  destruct (e' (wut f n h)) as [x r]; unfold wut in r.
  apply (@f_equal _ _ (fun f => f n x)) in r.
  destruct (Nat.eqb_spec n n) as [s | s].
    rewrite (nat_eq_rec.K_nat _ s) in r. destruct (h x n x); inversion r.
    contradiction.
Qed.
(* end hide *)

End nat_not_Type.

(** **** Ćwiczenie *)

(** To samo co wyżej, ale tym razem dla dowolnego typu, który ma
    rozstrzygalną równość oraz spełnia aksjomat K. *)

(* begin hide *)
Module EqDec_not_Type.

Variables
  (A : Type)
  (eq_dec : A -> A -> bool)
  (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
  (K : forall (x : A) (p : x = x), p = eq_refl).

Definition idtoeqv {A B : Type} (p : A = B) : A -> B.
(* begin hide *)
Proof.
  destruct p. intro x. exact x.
Defined.
(* end hide *)

Lemma idtoeqv_sur :
  forall (A B : Type) (p : A = B) (b : B),
    exists a : A, idtoeqv p a = b.
(* begin hide *)
Proof.
  destruct p. intro a. exists a. reflexivity.
Qed.
(* end hide *)

Definition wut
  (f : A -> Type) (x : A) (h : f x -> forall y : A, f y -> bool)
  : forall z : A, f z -> bool.
(* begin hide *)
Proof.
  intros y fy. destruct (eq_dec_spec x y).
    destruct e. exact (negb (h fy x fy)).
    exact true.
Defined.
(* end hide *)

Theorem A_not_Type : ~ @eq Type A Type.
(* begin hide *)
Proof.
  intro p.
  pose (f := idtoeqv p); pose (idtoeqv_sur _ _ p);
  change (idtoeqv p) with f in e; clearbody f e.
  pose (H := forall x : A, f x -> bool).
  destruct (e H) as [x q].
  pose (h := idtoeqv q); pose (e' := idtoeqv_sur _ _ q);
  change (idtoeqv q) with h in e'; clearbody h e'.
  destruct (e' (wut f x h)) as [fx r]; unfold wut in r.
  apply (@f_equal _ _ (fun f => f x fx)) in r.
  destruct (eq_dec_spec x x) as [s | s].
    rewrite (K _ s) in r. destruct (h fx x fx); inversion r.
    contradiction.
Qed.
(* end hide *)

End EqDec_not_Type.

(** **** Ćwiczenie *)

(** Dobrze wiemy, że [Prop] to nie [Type]... a może jednak? Rozstrzygnij,
    czy [Prop = Type] zachodzi, czy nie. *)

Module Prop_not_Type.

Require Import ProofIrrelevance.

Goal forall P : Prop, @eq Type P bool -> False.
(* begin hide *)
Proof.
  intros.
  assert (forall b1 b2 : bool, b1 = b2).
    rewrite <- H. apply proof_irrelevance.
  specialize (H0 true false). inversion H0.
Qed.
(* end hide *)

Definition transport
  {A : Type} (P : A -> Type) {x y : A} (p : x = y) : P x -> P y.
(* begin hide *)
Proof.
  destruct p. exact (@id _).
Defined.
(* end hide *)

Goal Prop <> Type.
(* begin hide *)
(* TODO *)
Proof.
  intro.
  pose Unnamed_thm.
  assert (~ forall A : Type, A = bool -> False).
    intro. apply (H0 bool). reflexivity.
  assert (forall P : Type -> Type, P Type -> P Prop).
    intros. rewrite H. assumption.
  apply H0. intros. apply eq_sym in H.
  assert (~ exists (P : Prop) (x y : P), x <> y).
    admit.
  apply eq_sym in H. destruct H.
Abort.
(* end hide *)

End Prop_not_Type.

(** * Protokoły różnicowe *)

Module DiffProtocols.

Require Import Equality.

Print list_neq.list_neq.

(** [list_neq.list_neq] to pokazanie na odpowiadające sobie miejsca w
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

Lemma proto_trans :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 l3 : list A},
    (forall x y z : A, R x y -> R y z -> R x z) ->
      ListDiffProtocol R l1 l2 -> ListDiffProtocol R l2 l3 ->
        ListDiffProtocol R l1 l3.
Proof.
  Hint Constructors ListDiffProtocol.
  intros * H HLDP. revert l3.
  induction HLDP; inversion 1; subst; auto.
    admit.
Abort.

(** Funkcje są różne (w silnym sensie), gdy różnią się dla jakiegoś
    argumentu. *)

Definition FunDiffPoint
  {A B : Type} (R : B -> B -> Prop) (f g : A -> B) : Type :=
    {x : A | R (f x) (g x)}.

(** Protokół różnicowy dla funkcji mówi, dla których argumentów wyniki
    są takie same, a dla których są różne. *)

Definition FunDiffProtocol
  {A B : Type} (R : B -> B -> Prop) (f g : A -> B) : Type :=
    forall x : A, f x = g x \/ R (f x) (g x).

End DiffProtocols.