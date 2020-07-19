(** * H: [Nie]równości, ścieżki i przepaście [TODO] *)

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

Require Import G.

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

Require Import G.

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

Require Import G.

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
  induction p; dependent destruction q.
    1-2: reflexivity.
    f_equal. apply IHp.
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

(** * Izomorfizmy typów (TODO) *)

(* begin hide *)

(** TODO: Izomorfizmy dla typów induktywnych (patrz notatka poniżej).

    Każde drzewo jest drzewem o jakiejś wysokości (no chyba że ma
    nieskończone rozgałęzienie, to wtedy nie). Uogólniając: każdy
    element typu induktywnego jest elementem odpowiadającego mu
    typu indeksowanego o pewnym indeksie. UWAGA: rozróżnienie na
    drzewa o skończonej wysokości vs drzewa o ograniczonej wysokości. *)

(* end hide *)


Definition isopair {A B : Type} (f : A -> B) (g : B -> A) : Prop :=
  (forall a : A, g (f a) = a) /\
  (forall b : B, f (g b) = b).

Definition iso (A B : Type) : Prop :=
  exists (f : A -> B) (g : B -> A), isopair f g.

(** ** Produkty i sumy *)

Definition swap {A B : Type} (x : A * B) : B * A :=
match x with
    | (a, b) => (b, a)
end.

Lemma prod_comm :
  forall A B : Type, iso (A * B) (B * A).
Proof.
  intros. exists swap, swap. split.
    destruct a; cbn; reflexivity.
    destruct b; cbn; reflexivity.
Qed.

Definition reassoc {A B C : Type} (x : A * (B * C)) : (A * B) * C :=
match x with
    | (a, (b, c)) => ((a, b), c)
end.

Definition unreassoc {A B C : Type} (x : (A * B) * C) : A * (B * C) :=
match x with
    | ((a, b), c) => (a, (b, c))
end.

Lemma prod_assoc :
  forall A B C : Type, iso (A * (B * C)) ((A * B) * C).
Proof.
  intros. exists reassoc, unreassoc. split.
    destruct a as [a [b c]]; cbn; reflexivity.
    destruct b as [[a b] c]; cbn; reflexivity.
Qed.

Lemma prod_unit_l :
  forall A : Type, iso (unit * A) A.
Proof.
  intro. exists snd. exists (fun a : A => (tt, a)). split.
    destruct a as [[] a]; cbn; reflexivity.
    reflexivity.
Qed.

Lemma prod_unit_r :
  forall A : Type, iso (A * unit) A.
Proof.
  intro. exists fst. exists (fun a : A => (a, tt)). split.
    destruct a as [a []]. cbn. reflexivity.
    reflexivity.
Qed.

(** Trzeba przerobić rozdział o typach i funkcjach tak, żeby nie mieszać
    pojęć kategorycznych (wprowadzonych na początku) z teoriozbiorowymi
    (injekcja, surjekcja, bijekcja). Przedstawić te 3 ostatnie jako
    explicite charakteryzacje pojęć kategorycznych. *)

Lemma sum_empty_l :
  forall A : Type, iso (Empty_set + A) A.
Proof.
  intro. eexists. eexists. Unshelve. all: cycle 1.
    destruct 1 as [[] | a]. exact a.
    exact inr.
    split.
      destruct a as [[] | a]; reflexivity.
      reflexivity.
Qed.

Lemma sum_empty_r :
  forall A : Type, iso (A + Empty_set) A.
Proof.
  intro. eexists. eexists. Unshelve. all: cycle 1.
    destruct 1 as [a | []]. exact a.
    exact inl.
    split.
      destruct a as [a | []]; reflexivity.
      reflexivity.
Qed.

Lemma sum_assoc :
  forall A B C : Type, iso (A + (B + C)) ((A + B) + C).
Proof.
  intros. do 2 eexists. Unshelve. all: cycle 1.
    1-2: firstorder.
    split.
      destruct a as [a | [b | c]]; reflexivity.
      destruct b as [[a | b] | c]; reflexivity.
Qed.

Lemma sum_comm :
  forall A B : Type, iso (A + B) (B + A).
Proof.
  intros. do 2 eexists. Unshelve. all: cycle 1.
    1-2: firstorder.
    split.
      destruct a; reflexivity.
      destruct b; reflexivity.
Qed.

(** ** Liczby naturalne *)

Definition pred (n : nat) : option nat :=
match n with
    | 0 => None
    | S n' => Some n'
end.

Definition unpred (on : option nat) : nat :=
match on with
    | None => 0
    | Some n => S n
end.

Lemma iso_nat_option_Nat :
  iso nat (option nat).
Proof.
  red. exists pred, unpred.
  split.
    destruct a as [| a']; cbn; reflexivity.
    destruct b as [b' |]; cbn; reflexivity.
Qed.

(** ** Listy *)

Definition uncons {A : Type} (l : list A) : option (A * list A) :=
match l with
    | [] => None
    | h :: t => Some (h, t)
end.

Definition ununcons {A : Type} (x : option (A * list A)) : list A :=
match x with
    | None => []
    | Some (h, t) => h :: t
end.

Lemma list_char_iso :
  forall A : Type, iso (list A) (option (A * list A)).
Proof.
  intro. exists uncons, ununcons. split.
    destruct a as [| h t]; cbn; reflexivity.
    destruct b as [[h t] |]; cbn; reflexivity.
Qed.

(** ** Strumienie *)

Require Import F3.

(** Jak można się domyślić po przykładach, charakterystyczne izomorfizmy
    dla prostych typów induktywnych są łatwe. A co z innowacyjniejszymi
    rodzajami definicji induktywnych oraz z definicjami koinduktywnymi?
    Sprawdźmy to! *)

Definition hdtl {A : Type} (s : Stream A) : A * Stream A :=
  (hd s, tl s).

Definition unhdtl {A : Type} (x : A * Stream A) : Stream A :=
{|
    hd := fst x;
    tl := snd x;
|}.

Lemma Stream_iso_char :
  forall A : Type, iso (Stream A) (A * Stream A).
Proof.
  intro. exists hdtl, unhdtl. split.
  all: unfold hdtl, unhdtl; cbn.
    destruct a; reflexivity.
    destruct b; reflexivity.
Qed.

(** ** Ciekawsze izomorfizmy *)

Require Import FunInd.

(** Jak trudno jest zrobić ciekawsze izomorfizmy? *)

Function div2 (n : nat) : nat + nat :=
match n with
    | 0 => inl 0
    | 1 => inr 0
    | S (S n') =>
        match div2 n' with
            | inl m => inl (S m)
            | inr m => inr (S m)
        end
end.

Definition undiv2 (x : nat + nat) : nat :=
match x with
    | inl n => 2 * n
    | inr n => S (2 * n)
end.

Lemma iso_nat_natnat :
  iso nat (nat + nat).
Proof.
  exists div2, undiv2. split.
    intro. functional induction (div2 a); cbn.
      1-2: reflexivity.
      rewrite e0 in IHs. cbn in IHs. rewrite <- plus_n_Sm, IHs. reflexivity.
      rewrite e0 in IHs. cbn in IHs. rewrite <- plus_n_Sm, IHs. reflexivity.
    destruct b.
      cbn. functional induction (div2 n); cbn.
        1-2: reflexivity.
        rewrite <- 2!plus_n_Sm. cbn. rewrite IHs. reflexivity.
        rewrite <- 2!plus_n_Sm. cbn. rewrite IHs. reflexivity.
      induction n as [| n'].
        cbn. reflexivity.
        cbn in *. destruct n' as [| n'']; cbn in *.
          reflexivity.
          rewrite <- plus_n_Sm. rewrite IHn'. reflexivity.
Qed.

(** Niezbyt trudno, ale łatwo też nie. *)

Function fill_square (n : nat) : nat * nat :=
match n with
    | 0 => (0, 0)
    | S n' =>
        match fill_square n' with
            | (0, m) => (S m, 0)
            | (S m1, m2) => (m1, S m2)
        end
end.

Compute D5.map fill_square (D5.iterate S 50 0).

Definition zigzag_order (x y : nat * nat) : Prop :=
  exists n m : nat,
    x = fill_square n /\
    y = fill_square m /\ n < m.

(*
Function unfill_square (x : nat * nat) {wf zigzag_order x} : nat :=
match x with
    | (0, 0) => 0
    | (S n, 0) => S (unfill_square (0, n))
    | (n, S m) => S (unfill_square (S n, m))
end.
Proof.
  Focus 4. red. destruct a as [n m]. constructor.
    destruct y as [n' m']. unfold zigzag_order.
Admitted.
*)

Unset Guard Checking.
Fixpoint unfill_square (x : nat * nat) : nat :=
match x with
    | (0, 0) => 0
    | (S n, 0) => S (unfill_square (0, n))
    | (n, S m) => S (unfill_square (S n, m))
end.
Set Guard Checking.

Lemma iso_nat_natnat' :
  iso nat (nat * nat).
Proof.
  exists fill_square, unfill_square. split.
    intro. functional induction (fill_square a).
Admitted.

(** Jak trudno jest z podstawowych izomorfizmów dla produktów i sum
    uskładać coś w stylu nat ~ list nat? A może nie da się i trzeba
    robić ręcznie? *)

Require Import vec.

Definition vlist (A : Type) : Type :=
  {n : nat & vec A n}.

Fixpoint vectorize' {A : Type} (l : list A) : vec A (length l) :=
match l with
    | nil => vnil
    | cons h t => vcons h (vectorize' t)
end.

Definition vectorize {A : Type} (l : list A) : vlist A :=
  existT _ (length l) (vectorize' l).

Fixpoint toList {A : Type} {n : nat} (v : vec A n) : list A :=
match v with
    | vnil => nil
    | vcons h t => cons h (toList t)
end.

Definition listize {A : Type} (v : vlist A) : list A :=
  toList (projT2 v).

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

Lemma eq_head_tail :
  forall {A : Type} {n : nat} (v1 v2 : vec A (S n)),
    head v1 = head v2 -> tail v1 = tail v2 -> v1 = v2.
Proof.
  Require Import Equality.
  dependent destruction v1.
  dependent destruction v2.
  cbn. destruct 1, 1. reflexivity.
Qed.

Lemma transport_cons :
  forall {A : Type} {n m : nat} (h : A) (t : vec A n) (p : n = m),
    transport (fun n : nat => vec A (S n)) p
     (h :: t) = h :: transport (fun n : nat => vec A n) p t.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma iso_list_vlist :
  forall A : Type, iso (list A) (vlist A).
Proof.
  intro. red. exists vectorize, listize. split.
    induction a as [| h t]; cbn in *.
      reflexivity.
      rewrite IHt. reflexivity.
    destruct b as [n v]. unfold vectorize. cbn.
      induction v as [| h t]; cbn.
        reflexivity.
        apply sigT_eq' in IHv. cbn in IHv. destruct IHv.
          eapply sigT_eq. Unshelve. all: cycle 1.
            exact (ap S x).
            rewrite transport_ap, transport_cons, e. reflexivity.
Qed.

(** Wnioski: da się zrobić trochę... *)

Fixpoint nat_vec {n : nat} (arg : nat) : vec nat (S n) :=
match n with
    | 0 => arg :: vnil
    | S n' =>
        let
          (arg1, arg2) := fill_square arg
        in
          arg1 :: nat_vec arg2
end.

Fixpoint vec_nat {n : nat} (v : vec nat n) {struct v} : option nat :=
match v with
    | vnil => None
    | vcons h t =>
        match vec_nat t with
            | None => Some h
            | Some r => Some (unfill_square (h, r))
        end
end.

(*
Fixpoint vec_nat' {n : nat} (v : vec nat (S n)) : nat :=
match v with
    | vcons x vnil => x
    | vcons x v' => unfill_square (x, vec_nat' v')
end.

    | vnil => None
    | vcons h t =>
        match vec_nat t with
            | None => Some h
            | Some r => Some (unfill_square (h, r))
        end
end.
*)

Compute D5.map (@nat_vec 3) [111; 1111; 11111].
Compute D5.map vec_nat (D5.map (@nat_vec 3) [111; 1111]).

Lemma nat_vlist :
  forall n : nat, iso nat (vec nat (S n)).
Proof.
  unfold iso. intros.
  exists nat_vec.
  exists (fun v => match vec_nat v with | None => 0 | Some n => n end).
  split.
    Focus 2. dependent destruction b.
    induction n as [| n']. (*
      reflexivity.
      {
        intro. destruct (fill_square a) as [a1 a2].
        change (vec_nat _) with (match vec_nat (@nat_vec n' a2) with
                                  | None => Some a1
                                  | Some r => Some (unfill_square (a1, r))
                                  end).
        rewrite <- (IHn' a2).*)
Abort.

(** ... ale [nat ~ list nat] jest dość trudne. *)

(** * Dziwne aksjomaty i płynące z nich logiki (TODO) *)

Definition ProofIrrelevance : Prop :=
  forall (P : Prop) (p q : P), p = q.

Definition UIP : Prop :=
  forall (A : Type) (x y : A) (p q : x = y), p = q.

Definition K : Prop :=
  forall (A : Type) (x : A) (p : x = x), p = eq_refl x.

Definition PropositionalExtensionality : Prop :=
  forall P Q : Prop, (P <-> Q) -> P = Q.

Lemma UIP_K : UIP -> K.
(* begin hide *)
Proof.
  unfold UIP, K.
  intros UIP A x p.
  apply UIP.
Qed.
(* end hide *)

Lemma K_UIP : K -> UIP.
(* begin hide *)
Proof.
  unfold K, UIP.
  intros K A x y p q.
  destruct p.
  symmetry. apply K.
Qed.
(* end hide *)

Lemma ProofIrrelevance_UIP :
  ProofIrrelevance -> UIP.
(* begin hide *)
Proof.
  unfold ProofIrrelevance, UIP.
  intros PI A x y p q.
  apply PI.
Qed.
(* end hide *)

Lemma ProofIrrelevance_K :
  ProofIrrelevance -> K.
(* begin hide *)
Proof.
  unfold ProofIrrelevance, K.
  intros PI A x p.
  apply PI.
Qed.
(* end hide *)