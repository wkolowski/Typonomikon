(** * H1: Równość i ścieżki [TODO] *)

Set Universe Polymorphism.

Require Import Arith.
Require Import Bool.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import StrictProp.

(** * Równość - powtórka (TODO) *)

(** * Ścieżki (TODO) *)

Definition transport
  {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
match p with
| eq_refl => u
end.

Lemma sigT_eq :
  forall
    {A : Type} (P : A -> Type)
    {x y : A} (p : x = y)
    {u : P x} {v : P y} (q : transport P p u = v),
      existT P x u = existT P y v.
Proof.
  destruct p. cbn. destruct 1. reflexivity.
Defined.

Lemma sigT_eq' :
  forall
    {A : Type} (P : A -> Type) {x y : sigT P},
      x = y ->
        {p : projT1 x = projT1 y & transport P p (projT2 x) = projT2 y}.
Proof.
  destruct 1, x. cbn. exists eq_refl. cbn. reflexivity.
Defined.

Definition ap
  {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
match p with
| eq_refl => eq_refl
end.

(* Lemma 2.3.10 *)
Lemma transport_ap :
  forall {A B : Type} (P : B -> Type) (f : A -> B)
    (x y : A) (p : x = y) (u : P (f x)),
      transport P (ap f p) u =
      @transport A (fun x => P (f x)) x y p u.
Proof.
  destruct p. cbn. reflexivity.
Defined.

(** * Równość a ścieżki *)

(** #<a class='link' href='https://homotopytypetheory.org/2012/01/22/univalence-versus-extraction/'>
    Uniwalencja versus ekstrakcja</a># *)

Module Path_is_eq.

Unset Universe Polymorphism.

Inductive Path {A : Type} (x : A) : A -> Type :=
| idp : Path x x.

Arguments idp {A x}.

Definition eq_to_Path {A : Type} {x y : A} (e : x = y) : Path x y :=
match e with
| eq_refl => idp
end.

Definition Path_to_eq {A : Type} {x y : A} (p : Path x y) : x = y :=
match p with
| idp => eq_refl
end.

Lemma eq_to_Path_to_eq :
  forall {A : Type} {x y : A} (e : x = y),
    Path_to_eq (eq_to_Path e) = e.
Proof.
  destruct e. cbn. reflexivity.
Qed.

Lemma Path_to_eq_to_Path :
  forall {A : Type} {x y : A} (p : Path x y),
    eq_to_Path (Path_to_eq p) = p.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma eq_to_Path_to_eq' :
  forall {A : Type} {x y : A} (e : x = y),
    Path (Path_to_eq (eq_to_Path e)) e.
Proof.
  destruct e. cbn. reflexivity.
Defined.

Lemma Path_to_eq_to_Path' :
  forall {A : Type} {x y : A} (p : Path x y),
    Path (eq_to_Path (Path_to_eq p)) p.
Proof.
  destruct p. cbn. reflexivity.
Defined.

Class iso (A B : Type) : Type :=
{
  f : A -> B;
  linv : {g : B -> A | forall a : A, g (f a) = a};
  rinv : {h : B -> A | forall b : B, f (h b) = b};
}.

Definition ProofIrrelevance : Prop :=
  forall (P : Prop) (p1 p2 : P), p1 = p2.

Definition UA : Type :=
  forall A B : Type, iso (iso A B) (Path A B).

#[refine]
#[export]
Instance iso_id : iso bool bool :=
{
  f := fun b => b;
}.
Proof.
  exists (fun b => b). reflexivity.
  exists (fun b => b). reflexivity.
Defined.

#[refine]
#[export]
Instance iso_negb : iso bool bool :=
{
  f := negb;
}.
Proof.
  exists negb. destruct a; reflexivity.
  exists negb. destruct b; reflexivity.
Defined.

Lemma ProofIrrelevance_UA_inconsistent :
  ProofIrrelevance -> UA -> False.
Proof.
  unfold ProofIrrelevance, UA.
  intros pi ua.
  destruct (ua bool bool) as [F [G FG] [H HF]].
  assert (forall x y : iso bool bool, x = y).
    intros. rewrite <- FG, <- (Path_to_eq_to_Path (F y)), (pi _ (eq_to_Path (Path_to_eq (F y))) (F x)), FG.
    reflexivity.
  specialize (H0 iso_id iso_negb).
  assert (forall b : bool, @f _ _ iso_negb b = b).
    intro. rewrite <- H0. reflexivity.
  specialize (H1 true).
  cbn in H1. congruence.
Qed.

End Path_is_eq.

(** * Ścieżki w typach induktywnych (TODO) *)

(* TODO: napisać wstęp *)

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
  forall {n m : nat} (p : n = m),
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

Lemma isSet_nat :
  forall {n m : nat} (p q : n = m), p = q.
(* begin hide *)
Proof.
  intros.
  rewrite <- (decode_encode p),
          <- (decode_encode q).
  f_equal.
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
  destruct p; cbn.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Scheme nat_eq_ind' := Induction for nat_eq Sort Prop.

Lemma isProp_code :
  forall {n m : nat} (c1 c2 : nat_eq n m), c1 = c2.
(* begin hide *)
Proof.
  induction c1 using nat_eq_ind';
  dependent destruction c2.
    reflexivity.
    f_equal. apply IHc1.
Qed.
(* end hide *)

Lemma decode_encode :
  forall {n m : nat} (c : nat_eq n m),
    encode (decode c) = c.
(* begin hide *)
Proof.
  intros. apply isProp_code.
Qed.
(* end hide *)

Lemma isSet_nat :
  forall {n m : nat} (p q : n = m), p = q.
(* begin hide *)
Proof.
  intros.
  rewrite <- (encode_decode p),
          <- (encode_decode q).
  apply f_equal.
  apply isProp_code.
Qed.
(* end hide *)

End nat_eq_ind.

(** Jak powiedział śp. Stefan Kisielewski: "teoria typów bohatersko
    zwalcza problemy nieznane w żadnej innej teorii". *)

(** Okazuje się, że sortu [SProp] można całkiem efektywnie użyć do pokazywania,
    że coś jest zdaniem w sensie HoTTowym. Dzięki temu dowód jest krótszy o
    całe 33%. Całkiem nieźle. *)

Module nat_eq_rec_SProp.

Fixpoint code (n m : nat) : SProp :=
match n, m with
| 0, 0 => sUnit
| S _, 0 => sEmpty
| 0, S _ => sEmpty
| S n', S m' => code n' m'
end.

Fixpoint encode_aux (n : nat) : code n n :=
match n with
| 0 => stt
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
  forall {n m : nat} (p : n = m),
    decode (encode p) = p.
(* begin hide *)
Proof.
  destruct p; cbn.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma isSet_nat:
  forall {n m : nat} (p q : n = m), p = q.
(* begin hide *)
Proof.
  intros.
  rewrite <- (decode_encode p),
          <- (decode_encode q).
  reflexivity.
Qed.
(* end hide *)

End nat_eq_rec_SProp.

(** ** Porządek [<=] na liczbach naturalnych *)

Module encodedecode1.

Fixpoint code (n m : nat) : SProp :=
match n, m with
| 0, _ => sUnit
| _, 0 => sEmpty
| S n', S m' => code n' m'
end.

Inductive gutle : nat -> nat -> Prop :=
| gutle_0 : forall m : nat, gutle 0 m
| gutle_SS : forall n m : nat, gutle n m -> gutle (S n) (S m).

Fixpoint encode {n m : nat} (H : gutle n m) : code n m :=
match H with
| gutle_0 _ => stt
| gutle_SS _ _ H' => encode H'
end.

Fixpoint decode (n m : nat) : code n m -> gutle n m :=
match n, m with
| 0   , _    => fun _ => gutle_0 m
| _   , 0    => fun c => match c with end
| S n', S m' => fun c => gutle_SS _ _ (decode n' m' c)
end.

Fixpoint decode_encode
  {n m : nat} (H : gutle n m) : decode n m (encode H) = H.
Proof.
  destruct H; cbn.
    reflexivity.
    f_equal. apply decode_encode.
Defined.

Lemma isProp_gutle :
  forall {n m : nat} (p q : gutle n m), p = q.
Proof.
  intros.
  rewrite <- (decode_encode p), <- (decode_encode q).
  reflexivity.
Qed.

End encodedecode1.

(** ** Jeszcze raz [<=], lecz tym razem używając [SProp] *)

Module encodedecode2.

Fixpoint code (n m : nat) : SProp :=
match n, m with
| 0, _ => sUnit
| _, 0 => sEmpty
| S n', S m' => code n' m'
end.

Fixpoint encode' (n : nat) : code n n :=
match n with
| 0 => stt
| S n' => encode' n'
end.

Fixpoint code_S {n m : nat} : code n m -> code n (S m) :=
match n, m with
| 0, _ => fun _ => stt
| _, 0 => fun c => match c with end
| S n', S m' => fun c => @code_S n' m' c
end.

Fixpoint encode {n m : nat} (H : n <= m) : code n m :=
match H with
| le_n _ => encode' n
| le_S _ _ H' => code_S (encode H')
end.

Lemma le_n_S_transparent :
  forall n m : nat,
    n <= m -> S n <= S m.
Proof.
  induction 1; constructor; assumption.
Defined.

Definition decode :
  forall {n m : nat}, code n m -> n <= m.
Proof.
  induction n as [| n'].
    intros. clear H. induction m as [| m'].
      constructor.
      constructor. assumption.
    destruct m as [| m']; cbn; intro.
      destruct H.
      apply le_n_S_transparent, IHn'. assumption.
Defined.

Lemma decode_code_S :
  forall {n m : nat} (c : code n m),
    decode (code_S c) = le_S _ _ (decode c).
Proof.
  induction n as [| n'].
    destruct m; reflexivity.
    destruct m as [| m'].
      cbn. destruct c.
      simpl. intros. rewrite IHn'. cbn. reflexivity.
Qed.

Lemma decode_encode :
  forall {n m : nat} (H : n <= m),
    decode (encode H) = H.
Proof.
  fix IH 3.
  destruct H; cbn.
    induction n as [| n'].
      cbn. reflexivity.
      simpl. rewrite IHn'. cbn. reflexivity.
    rewrite decode_code_S, IH. reflexivity.
Qed.

Lemma isProp_le :
  forall {n m : nat} {H1 H2 : n <= m},
    H1 = H2.
Proof.
  intros.
  rewrite <- (decode_encode H1),
          <- (decode_encode H2).
  reflexivity.
Qed.

End encodedecode2.

(** ** Ścieżki między listami *)

From Typonomikon Require Import D5.

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

(* begin hide *)
(* TODO
Check code_ind.
Check code_ind'.
*)
(* end hide *)

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

(** Insajt, że o ja pierdole: jak się ma [list_eq] do [Forall]? *)

Inductive Forall2
  {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| nil2 : Forall2 R [] []
| cons2 :
    forall {h1 h2 : A} {t1 t2 : list A},
      R h1 h2 -> Forall2 R t1 t2 -> Forall2 R (h1 :: t1) (h2 :: t2).

Lemma list_eq_Forall :
  forall {A : Type} {l1 l2 : list A},
    code l1 l2 <-> Forall2 (@eq A) l1 l2.
Proof.
  split; induction 1; constructor; assumption.
Qed.

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
  revert l2 c.
  induction l1 as [| h1 t1];
  destruct l2 as [| h2 t2];
  cbn; intros.
    reflexivity.
    specialize (c 0). cbn in c. refine (match c with eq_refl => _ end). red. trivial.
    specialize (c 0). cbn in c. refine (match c with eq_refl => _ end). red. trivial.
    rewrite (IHt1 _ (fun n => c (S n))). specialize (c 0). cbn in c.
      refine (match c with eq_refl => _ end). reflexivity.
Defined.

Lemma decode_encode :
  forall {A : Type} {l1 l2 : list A} (p : l1 = l2),
    decode (encode p) = p.
Proof.
  destruct p. cbn.
  induction l1 as [| h t].
    cbn. reflexivity.
    cbn. cbn. f_equal.
Abort.

Lemma encode_decode :
  forall {A : Type} {l1 l2 : list A} (c : code l1 l2),
    encode (decode c) = c.
Proof.
  induction l1 as [| h1 t1];
  destruct  l2 as [| h2 t2];
  intros.
    red in c. cbn in *.
Abort.
(* end hide *)

End list_eq_forall.

(** * Ścieżki w typach koinduktywnych (TODO) *)

(** * Ścieżki między funkcjami (TODO) *)

(** * Ścieżki w uniwersum (TODO) *)

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

Lemma nat_not_Type : ~ @eq Type nat Type.
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
    rewrite (nat_eq_rec.isSet_nat s eq_refl) in r.
    destruct (h x n x); inversion r.
    contradiction.
Qed.
(* end hide *)

End nat_not_Type.

(** **** Ćwiczenie *)

(** To samo co wyżej, ale tym razem dla dowolnego typu, który ma
    rozstrzygalną równość oraz spełnia aksjomat K. *)

(* begin hide *)
Section EqDec_not_Type.

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

Variables
  (A : Type)
  (eq_dec : A -> A -> bool)
  (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
  (K : forall (x : A) (p : x = x), p = eq_refl).

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

Lemma A_not_Type : ~ @eq Type A Type.
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

(** Dobrze wiemy, że [SProp] to nie [Type]... a może jednak?
    Rozstrzygnij, czy [SProp = Type] zachodzi, czy nie. *)

Module SProp_not_Type.

Definition S := SProp.
Definition U := Type.

Lemma SProp_not_Type :
  S <> U.
Proof.
  intro.
  assert (forall (P : S) (p1 p2 : P), p1 = p2) by reflexivity.
  assert ((forall (A : U) (x y : A), x = y) -> False).
    intro. specialize (H1 bool true false). congruence.
  apply H1. intros.
Abort.

End SProp_not_Type.

(** * Parametryczność, a raczej jej brak (TODO) *)

(* begin hide *)
(* Tutaj szczegóły: https://arxiv.org/pdf/1701.05617.pdf *)
(* end hide *)

Axiom LEM : forall (A : Type), A + (A -> False).

Open Scope type_scope.

Definition bad' (A : Type) :
  {f : A -> A &
    (@eq Type bool A * forall x : A, f x <> x) +
    ((@eq Type bool A -> False) * forall x : A, f x = x)}.
Proof.
  destruct (LEM (@eq Type bool A)).
    destruct e. exists negb. left. split.
      reflexivity.
      destruct x; inversion 1.
    exists (fun x : A => x). right. split.
      assumption.
      reflexivity.
Defined.

Definition bad (A : Type) : A -> A := projT1 (bad' A).

Lemma bad_is_bad :
  forall b : bool, bad bool b <> b.
Proof.
  unfold bad.
  intros. destruct bad'; cbn. destruct s as [[p H] | [p H]].
    apply H.
    contradiction p. reflexivity.
Defined.

Lemma bad_ist_gut :
  forall (A : Type) (x : A),
    (@eq Type bool A -> False) -> bad A x = x.
Proof.
  unfold bad. intros A x p.
  destruct bad' as [f [[q H] | [q H]]]; cbn.
    contradiction p.
    apply H.
Defined.