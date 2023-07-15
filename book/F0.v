(** * F0: Równość, nierówność, różność i ścieżki [TODO] *)

Set Universe Polymorphism.

Require Import Arith.
Require Import Bool.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import StrictProp.

From Typonomikon Require Import D5.

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
    całe 33%%. Całkiem nieźle. *)

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

(** ** Ścieżki w uniwersum (TODO) *)

(** * Nierówność i różność *)

(** ** Liczby naturalne (TODO) *)

(** A co to znaczy, że liczby naturalne nie są równe? *)

(** Powinien być tylko jeden dowód na nierówność. *)

(** *** Nierówność liczb naturalnych - rekurencyjnie *)

Module nat_neq_rec.

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

(** *** Nierówność liczb naturalnych - induktywnie *)

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
  - reflexivity.
  - reflexivity.
  - apply f_equal, IHp.
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
  - inversion 1.
  - inversion 1.
  - inversion 1. apply (decode _ _ c). assumption.
Defined.

Lemma encode_decode :
  forall {n m : nat} (p : n <> m),
    decode (encode p) = p.
(* begin hide *)
Proof.
  induction n as [| n'];
  destruct  m as [| m'];
  cbn; intros.
  - contradiction.
  - apply functional_extensionality. inversion x.
  - apply functional_extensionality. inversion x.
  - apply functional_extensionality. contradiction.
Qed.
(* end hide *)

Lemma decode_encode :
  forall {n m : nat} (c : nat_neq n m),
    encode (decode c) = c.
(* begin hide *)
Proof.
  induction c using nat_neq_ind'; cbn; [reflexivity.. |].
  rewrite <- IHc. do 2 f_equal.
  apply functional_extensionality.
  destruct x; cbn.
  rewrite IHc.
  reflexivity.
Qed.
(* end hide *)

End nat_neq_ind.

(** *** Tadam *)

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

(** ** Listy *)

(** *** Różność list - induktywnie *)

Module list_apart_ind.

Inductive list_apart
  {A : Type} (R : A -> A -> Type) : list A -> list A -> Type :=
| nc  : forall (h : A) (t : list A), list_apart R [] (h :: t)
| cn  : forall (h : A) (t : list A), list_apart R (h :: t) []
| cc1 : forall (h1 h2 : A) (t1 t2 : list A),
          R h1 h2 -> list_apart R (h1 :: t1) (h2 :: t2)
| cc2 : forall (h1 h2 : A) (t1 t2 : list A),
          list_apart R t1 t2 -> list_apart R (h1 :: t1) (h2 :: t2).

#[global] Hint Constructors list_apart : core.

Lemma list_apart_irrefl :
  forall {A : Type} {R : A -> A -> Prop} (l1 l2 : list A),
    (forall x : A, R x x -> False) ->
      list_apart R l1 l2 -> l1 <> l2.
(* begin hide *)
Proof.
  induction 2; inversion 1; subst.
  - apply (H _ r).
  - apply IHX. reflexivity.
Defined.
(* end hide *)

Lemma list_apart_sym :
  forall {A : Type} {R : A -> A -> Prop} (l1 l2 : list A),
    (forall x y : A, R x y -> R y x) ->
      list_apart R l1 l2 -> list_apart R l2 l1.
(* begin hide *)
Proof.
  induction 2; [constructor.. |].
  - apply H. assumption.
  - constructor 4. assumption.
Defined.
(* end hide *)

Lemma list_apart_cotrans :
  forall {A : Type} {R : A -> A -> Prop} (l1 l3 : list A),
    (forall x y z : A, R x z -> R x y + R y z) ->
      list_apart R l1 l3 -> forall l2 : list A,
        list_apart R l1 l2 + list_apart R l2 l3.
(* begin hide *)
Proof.
  induction 2; intros.
  - destruct l2; [right | left]; constructor.
  - destruct l2; [left | right]; constructor.
  - destruct l2 as [| h t].
    + left. constructor.
    + destruct (X _ h _ r).
      * left. constructor. assumption.
      * right. constructor. assumption.
  - destruct l2 as [| h t].
    + left. constructor.
    + destruct (IHX0 t).
      * left. constructor 4. assumption.
      * right. constructor 4. assumption.
Defined.
(* end hide *)

(** *** Różność list a [Exists2] *)

Inductive Exists2
  {A : Type} (R : A -> A -> Type) : list A -> list A -> Type :=
| E2_here :
    forall {h1 h2 : A} (t1 t2 : list A),
      R h1 h2 -> Exists2 R (h1 :: t1) (h2 :: t2)
| E2_there :
    forall {h1 h2 : A} {t1 t2 : list A},
      Exists2 R t1 t2 -> Exists2 R (h1 :: t1) (h2 :: t2).

Lemma Exists2_list_apart :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    Exists2 R l1 l2 -> list_apart R l1 l2.
(* begin hide *)
Proof.
  induction 1.
  - constructor. assumption.
  - constructor 4. assumption.
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

Lemma isProp_DS :
  forall
    {A : Type} {l1 l2 : list A}
    (p q : DifferentStructure l1 l2),
      p = q.
(* begin hide *)
Proof.
  induction p; intro q.
  - refine (match q with DS_nc _ _   => _ end). reflexivity.
  - refine (match q with DS_cn _ _   => _ end). reflexivity.
  - dependent destruction q. f_equal. apply IHp.
Qed.
(* end hide *)

(** Insajt, że o ja pierdole: [list_apart] to w sumie [Exists2] lub
    [DifferentStructure], czyli listy różnią się, gdy różnią się
    na którymś elemencie lub mają różną długość. *)

Lemma list_apart_to_ED :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    list_apart R l1 l2 -> Exists2 R l1 l2 + DifferentStructure l1 l2.
(* begin hide *)
Proof.
  induction 1.
  - right. constructor.
  - right. constructor.
  - left. constructor. assumption.
  - destruct IHX.
    + left. constructor 2. assumption.
    + right. constructor. assumption.
Defined.
(* end hide *)

Lemma list_apart_to_ED_conv :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    Exists2 R l1 l2 + DifferentStructure l1 l2 -> list_apart R l1 l2.
(* begin hide *)
Proof.
  destruct 1.
  - induction e.
    + constructor. assumption.
    + constructor 4. assumption.
  - induction d.
    + constructor.
    + constructor.
    + constructor 4. assumption.
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
  assert (forall (A B : Type) (x y : A), @inl A B x = inl y -> x = y)
    by (inversion 1; reflexivity).
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

Lemma list_apart_to_ED_list_apart_to_ED_conv :
  forall
    {A : Type} {R : A -> A -> Prop} {l1 l2 : list A}
    (c : list_apart R l1 l2),
      list_apart_to_ED_conv (list_apart_to_ED c) = c.
(* begin hide *)
Proof.
  induction c; cbn; [reflexivity.. |].
  destruct (list_apart_rect A R _) eqn: Heq; cbn; f_equal.
  - induction e; cbn in *.
    + dependent destruction c; cbn in *.
      * f_equal. symmetry. apply okurwa in Heq. assumption.
      * cbn in *. rewrite Heq in IHc. cbn in IHc. inversion IHc.
    + dependent destruction c.
      * cbn in *. inversion Heq.
      * cbn in *. rewrite Heq in IHc. cbn in IHc. assumption.
  - dependent destruction c; cbn in *.
    + inversion Heq; subst; cbn. reflexivity.
    + inversion Heq; subst; cbn. reflexivity.
    + inversion Heq.
    + rewrite Heq in IHc. cbn in IHc. assumption.
Qed.
(* end hide *)

Lemma list_apart_to_ED_conv_list_apart_to_ED :
  forall
    {A : Type} {R : A -> A -> Prop} {l1 l2 : list A}
    (x : Exists2 R l1 l2 + DifferentStructure l1 l2),
      list_apart_to_ED (list_apart_to_ED_conv x) = x.
(* begin hide *)
Proof.
  destruct x.
  - induction e; cbn in *.
    + reflexivity.
    + destruct (list_apart_rect A R _); inversion IHe. reflexivity.
  - induction d; cbn in *.
    + reflexivity.
    + reflexivity.
    + destruct (list_apart_rect A R _); inversion IHd. reflexivity.
Qed.
(* end hide *)

End list_apart_ind.

(** *** Różność list - rekurencyjnie *)

Fixpoint list_apart'
  {A : Type} (R : A -> A -> Type) (l1 l2 : list A) : Type :=
match l1, l2 with
| [], [] => False
| h1 :: t1, h2 :: t2 => R h1 h2 + list_apart' R t1 t2
| _, _ => True
end.

Lemma apart_to_apart' :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 : list A},
    list_apart_ind.list_apart R l1 l2 -> list_apart' R l1 l2.
(* begin hide *)
Proof.
  now induction 1; cbn; [trivial.. | left | right].
Defined.
(* end hide *)

Lemma apart'_to_apart :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 : list A},
    list_apart' R l1 l2 -> list_apart_ind.list_apart R l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
  - easy.
  - constructor.
  - constructor.
  - intros [r | H].
    + now constructor 3.
    + now constructor 4; apply IHt1.
Defined.
(* end hide *)

Lemma appart_to_apart'_to_apart :
  forall {A : Type} (R : A -> A -> Type) (l1 l2 : list A)
    (x : list_apart_ind.list_apart R l1 l2),
      apart'_to_apart (apart_to_apart' x) = x.
(* begin hide *)
Proof.
  dependent induction x; cbn; [easy.. |].
  destruct (list_rect _ _ _); f_equal.
  - now dependent destruction x.
  - now dependent destruction x.
  - dependent destruction x; admit.
  - dependent destruction x.
Abort.
(* end hide *)

(** ** Różność strumieni (TODO) *)

From Typonomikon Require F2 F3.

Module Stream_apart.

Import F2.

Inductive Stream_apart
  {A : Type} (R : A -> A -> Type) : Stream A -> Stream A -> Type :=
| Stream_apart_hd :
    forall s1 s2 : Stream A,
      R (hd s1) (hd s2) -> Stream_apart R s1 s2
| Stream_apart_tl :
    forall s1 s2 : Stream A,
      Stream_apart R (tl s1) (tl s2) -> Stream_apart R s1 s2.

Definition Stream_neq {A : Type} : Stream A -> Stream A -> Type :=
  Stream_apart (fun x y => x <> y).

Lemma Stream_neq_Stream_apart :
  forall {A : Type} (R : A -> A -> Type) {s1 s2 : Stream A},
    (forall x : A, R x x -> False) ->
      Stream_apart R s1 s2 -> Stream_neq s1 s2.
(* begin hide *)
Proof.
  intros A R s1 s2 Hirrefl.
  induction 1.
  - constructor 1.
    intros Heq.
    apply Hirrefl with (hd s1).
    now rewrite Heq at 2.
  - constructor 2.
    now apply IHX.
Qed.
(* end hide *)

Lemma Stream_neq_not_sim :
  forall {A : Type} {s1 s2 : Stream A},
    Stream_neq s1 s2 -> ~ sim s1 s2.
(* begin hide *)
Proof.
  induction 1; intros []; contradiction.
Qed.
(* end hide *)

Lemma not_sim_neq :
  forall {A : Type} {s1 s2 : Stream A},
    ~ sim s1 s2 -> s1 <> s2.
(* begin hide *)
Proof.
  intros A s1 s2 Hsn ->.
  now apply Hsn, sim_refl.
Qed.
(* end hide *)

End Stream_apart.

(** ** Nierówność liczb konaturalnych *)

Module conat_apart.

Import F3.

Inductive conat_apart : conat -> conat -> Prop :=
| conat_apart_zero_succ :
    forall c1 c2 : conat,
      out c1 = Z -> out c2 <> Z -> conat_apart c1 c2
| conat_apart_succ_zero :
    forall c1 c2 : conat,
      out c1 <> Z -> out c2 = Z -> conat_apart c1 c2
| conat_apart_succ_succ :
    forall (c1 c2 : conat) (c1' c2' : conat),
      out c1 = S c1' -> out c2 = S c2' -> conat_apart c1' c2' -> conat_apart c1 c2.

Lemma conat_apart_spec :
  forall n m : conat,
    conat_apart n m -> n <> m.
(* begin hide *)
Proof.
  induction 1; intro Heq; inversion Heq; congruence.
Qed.
(* end hide *)

Lemma conat_apart_irrefl :
  forall n : conat, ~ conat_apart n n.
(* begin hide *)
Proof.
  intros n Hneq.
  now eapply conat_apart_spec; eauto.
Qed.
(* end hide *)

End conat_apart.

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