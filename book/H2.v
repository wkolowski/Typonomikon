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

Require Import Equality.

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

Require Import H1.

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

(** ** Różność liczb naturalnych - rekurencyjnie *)

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

Inductive nat_neq : nat -> nat -> Prop :=
    | ZS : forall n : nat, nat_neq 0 (S n)
    | SZ : forall n : nat, nat_neq (S n) 0
    | SS : forall n m : nat, nat_neq n m -> nat_neq (S n) (S m).

Arguments ZS {n}.
Arguments SZ {n}.
Arguments SS {n m} _.

Require Import Equality FunctionalExtensionality.

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
    left. constructor.
    right. constructor.
    right. constructor.
    destruct (IHn' m').
      left. constructor. assumption.
      right. constructor. assumption.
Qed.
(* end hide *)

End nat_eq_neq.

(** ** Porządek [<=] na liczbach naturalnych *)

Module encodedecode1.

Require Import H1.

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
    | n'  , 0    => fun c => match c with end
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

Module encodedecode2.

Require Import H1.

Fixpoint code (n m : nat) : SProp :=
match n, m with
    | 0, _ => sUnit
    | _, 0 => sEmpty
    | S n', S m' => code n' m'
end.

Definition encode :
  forall {n m : nat}, n <= m -> code n m.
Proof.
  induction n as [| n'].
    cbn. constructor.
    destruct m as [| m'].
      inversion 1.
      cbn. intro. apply IHn'. apply le_S_n. assumption.
Defined.

Fixpoint encode' (n : nat) : code n n :=
match n with
    | 0 => stt
    | S n' => encode' n'
end.

(*
Definition encode {n m : nat} (H : n <= m) : code n m.
Proof.
  destruct H.
    apply encode'.
    destruct n; cbn.
      exact stt.
*)

(*
Fixpoint decode {n m : nat} : code n m -> n <= m :=
match n, m with
    | 0   , _    => fun _ => le_0_n m
    | _   , 0    => fun c => match c with end
    | S n', S m' => fun c => le_n_S n' m' (decode c)
end.
*)

Definition decode :
  forall {n m : nat}, code n m -> n <= m.
Proof.
  induction n as [| n'].
    intros. clear H. induction m as [| m'].
      constructor.
      constructor. assumption.
    destruct m as [| m']; cbn; intro.
      destruct H.
      apply le_n_S, IHn'. assumption.
Defined.

Scheme le_ind' := Induction for le Sort Prop.

Require Import Equality.

Lemma decode_encode :
  forall {n m : nat} (H : n <= m),
    decode (encode H) = H. (* TODO: kody dla [n <= m] *)
Proof.
Admitted.

End encodedecode2.

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
  induction l1 as [| h1 t1]; cbn.
    specialize (c 0). cbn in c. destruct l2.
Abort.
(* end hide *)

End list_eq_forall.

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

Require Import Equality.

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

End list_neq_ind.

(** ** Różność list - rekursywnie *)

Module list_neq_rec.

Fixpoint list_neq {A : Type} (l1 l2 : list A) : Prop :=
match l1, l2 with
    | [], [] => False
    | [], _ => True
    | _, [] => True
    | h1 :: t1, h2 :: t2 => h1 <> h2 \/ list_neq t1 t2
end.

Lemma list_neq_spec :
  forall (A : Type) (l1 l2 : list A),
    list_neq l1 l2 -> l1 <> l2.
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

End list_neq_rec.

(** ** Apartheid list (TODO) *)

(* begin hide *)
Module weak_apart.

Inductive unequal {A : Type} : list A -> list A -> Prop :=
    | nil_cons : forall h t, unequal nil (cons h t)
    | cons_nil : forall h t, unequal (cons h t) nil
    | cons_cons1 :
        forall h1 h2 t1 t2,
          h1 <> h2 -> unequal (cons h1 t1) (cons h2 t2)
    | cons_cons2 :
        forall h1 h2 t1 t2,
          unequal t1 t2 -> unequal (cons h1 t1) (cons h2 t2).

(*
Goal
  forall {A : Type} (l1 l2 : list A),
    unequal l1 l2 <-> neq l1 l2.
Proof.
  split.
    induction 1; cbn; firstorder.
    revert l2. induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
      contradiction.
      1-2: constructor.
      destruct 1.
        constructor 3. assumption.
        constructor 4. apply IHt1. assumption.
Qed.
*)

End weak_apart.

Module param_apart.

Fixpoint neq
  {A : Type} (apart : A -> A -> Prop) (l1 l2 : list A) : Prop :=
match l1, l2 with
    | nil, nil => False
    | nil, cons _ _ => True
    | cons _ _, nil => True
    | cons h1 t1, cons h2 t2 => apart h1 h2 \/ neq apart t1 t2
end.

(*
Goal
  forall {A : Type} (apart : A -> A -> Prop) (l1 l2 : list A),
    unequal apart l1 l2 <-> neq apart l1 l2.
Proof.
  split.
    induction 1; cbn; firstorder.
    revert l2. induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
      contradiction.
      1-2: constructor.
      destruct 1.
        constructor 3. assumption.
        constructor 4. apply IHt1. assumption.
Qed.
*)

End param_apart.
(* end hide *)

(** * Ścieżki w typach koinduktywnych *)

(** ** Nierówność liczb konaturalnych *)

Module conat_neq.

Require Import F2.

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
  induction 1.
    inversion 1.
    inversion 1.
    intro Heq. apply (f_equal pred) in Heq.
      cbn in Heq. inversion Heq; subst. contradiction.
Qed.
(* end hide *)

End conat_neq.

(** ** Różność strumieni *)

Module Stream_neq.

Require Import F3.

Inductive Stream_neq
  {A : Type} (R : A -> A -> Prop) : Stream A -> Stream A -> Type :=
    | Stream_neq_hd :
        forall (h1 h2 : A) (t1 t2 : Stream A),
          R h1 h2 -> Stream_neq R (scons h1 t1) (scons h2 t2)
    | Stream_neq_tl :
        forall (h1 h2 : A) (t1 t2 : Stream A),
          Stream_neq R t1 t2 -> Stream_neq R (scons h1 t1) (scons h2 t2).

Inductive Stream_neq'
  {A : Type} : Stream A -> Stream A -> Type :=
    | Stream_neq_hd' :
        forall t1 t2 : Stream A,
          hd t1 <> hd t2 -> Stream_neq' t1 t2
    | Stream_neq_tl' :
        forall t1 t2 : Stream A,
          Stream_neq' (tl t1) (tl t2) -> Stream_neq' t1 t2.

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

Lemma Stream_neq'_not_sim :
  forall {A : Type} {s1 s2 : Stream A},
      Stream_neq' s1 s2 -> ~ sim s1 s2.
(* begin hide *)
Proof.
  induction 1; intros []; contradiction.
Qed.
(* end hide *)

Lemma Stream_neq'_Stream_neq :
  forall {A : Type} {s1 s2 : Stream A},
    Stream_neq' s1 s2 ->
      Stream_neq (fun x y => x <> y) s1 s2.
(* begin hide *)
Proof.
  induction 1.
    destruct t1, t2. cbn in *. left. assumption.
    destruct t1, t2. cbn in *. right. assumption.
Qed.
(* end hide *)

Lemma Stream_neq_Stream_neq' :
  forall {A : Type} {R : A -> A -> Prop} {s1 s2 : Stream A},
    (forall x : A, ~ R x x) ->
      Stream_neq R s1 s2 -> Stream_neq' s1 s2.
(* begin hide *)
Proof.
  induction 2.
    left. cbn. intro. subst. apply (H _ r).
    right. cbn. assumption.
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