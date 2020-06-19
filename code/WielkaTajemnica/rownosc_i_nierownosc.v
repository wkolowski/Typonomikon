(** * Równość list *)

Require Import D5.

Module rec.

(* Kody nie muszą być rekurencyjne - mogą być induktywne. *)
Fixpoint code {A : Type} (l1 l2 : list A) : Prop :=
match l1, l2 with
    | [], [] => True
    | h1 :: t1, h2 :: t2 => h1 = h2 /\ code t1 t2
    | _, _ => False
end.

Fixpoint encode {A : Type} (l : list A) : code l l :=
match l with
    | [] => I
    | _ :: t => conj eq_refl (encode t)
end.

Definition decode {A : Type} {l1 l2 : list A} (c : code l1 l2) : l1 = l2.
Proof.
  Abort.
(*    
match c with
    | I => eq_refl
    | conj p c' => match p with eq_refl => decode c' end
end.
*)

End rec.

Module ind.

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
Proof.
  induction c.
    reflexivity.
    exact (f_equal2 (@cons A) H IHc).
Qed.

Fixpoint decode {A : Type} {l1 l2 : list A} (c : code l1 l2) : l1 = l2 :=
match c with
    | nils => eq_refl
    | conss p c' => (*f_equal2 _ p (decode c')*)
        match p, decode c' with
            | eq_refl, eq_refl => eq_refl
        end
end.

Lemma encode_decode :
  forall {A : Type} {l1 l2 : list A} (p : l1 = l2),
    decode (encode p) = p.
Proof.
  destruct p. cbn.
  induction l1 as [| h t]; cbn.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.

Scheme code_ind' := Induction for code Sort Prop.

Lemma decode_encode :
  forall {A : Type} {l1 l2 : list A} (c : code l1 l2),
    encode (decode c) = c.
Proof.
  induction c using code_ind'; cbn.
    reflexivity.
    destruct e. destruct (decode c). cbn in *. rewrite IHc. reflexivity.
Qed.

End ind.

Module all.

Definition code {A : Type} (l1 l2 : list A) : Prop :=
  forall n : nat, nth n l1 = nth n l2.

Definition encode
  {A : Type} {l1 l2 : list A} (p : l1 = l2) : code l1 l2 :=
match p with
    | eq_refl => fun n => eq_refl
end.

Definition decode {A : Type} {l1 l2 : list A} (c : code l1 l2) : l1 = l2.
Proof.
  induction l1 as [| h1 t1]; cbn.
    specialize (c 0). cbn in c. destruct l2.
Abort.

End all.

Module coind.

Require Import F3.

(* Wiadomo, że kody to bipodobieństwa. *)

End coind.

Module nat_neq.

(* A co to znaczy, że liczby naturalne nie są równe? *)

Inductive nat_neq : nat -> nat -> Type :=
    | ZS : forall n : nat, nat_neq 0 (S n)
    | SZ : forall n : nat, nat_neq (S n) 0
    | SS : forall n m : nat, nat_neq n m -> nat_neq (S n) (S m).

Arguments ZS {n}.
Arguments SZ {n}.
Arguments SS {n m} _.

(* Powinien być tylko jeden dowód na nierówność. *)

Fixpoint code (n m : nat) : Type :=
match n, m with
    | 0, 0 => False
    | 0, S _ => True
    | S _, 0 => True
    | S n', S m' => code n' m'
end.

Fixpoint encode {n m : nat} {struct n} : n <> m -> code n m.
Proof.
  destruct n as [| n'], m as [| m']; cbn; intro p.
    apply p. reflexivity.
    exact I.
    exact I.
    apply encode. intro q. apply p. f_equal. exact q.
Defined.
(*
    cbn. in
match n, m with
    | 0, 0 => fun p : 0 <> 0 => p (eq_refl 0)
    | 0, S _ => I
    | S _, 0 => I
    | S n', S m' => @encode n' m'
end.
*)

Fixpoint decode {n m : nat} : code n m -> n <> m.
Proof.
  destruct n as [| n'], m as [| m']; cbn; intro p.
    contradiction.
    inversion 1.
    inversion 1.
    intro q. apply (decode _ _ p). inversion q. reflexivity.
Defined.

Fixpoint encode' {n m : nat} (p : nat_neq n m) : code n m :=
match p with
    | ZS => I
    | SZ => I
    | SS p' => encode' p'
end.

Fixpoint decode' {n m : nat} : code n m -> nat_neq n m :=
match n, m with
    | 0, 0 => fun c : False => match c with end
    | 0, S _ => fun _ => ZS
    | S _, 0 => fun _ => SZ
    | S n', S m' => fun c : code n' m' => SS (@decode' n' m' c)
end.

Lemma encode_decode :
  forall {n m : nat} (p : nat_neq n m),
    decode' (encode' p) = p.
Proof.
  induction p; cbn.
    1-2: reflexivity.
    rewrite IHp. reflexivity.
Qed.

Lemma decode_encode :
  forall {n m : nat} (c : code n m),
    encode' (decode' c) = c.
Proof.
  induction n as [| n'], m as [| m']; cbn.
    destruct c.
    1-2: destruct c; reflexivity.
    intro c. apply IHn'.
Qed.

Lemma isProp_code :
  forall {n m : nat} (c1 c2 : code n m), c1 = c2.
Proof.
  induction n as [| n'], m as [| m']; cbn.
    1-3: destruct c1, c2; reflexivity.
    apply IHn'.
Qed.

Lemma isProp_nat_neq :
  forall (n m : nat) (p q : nat_neq n m), p = q.
Proof.
  intros.
  rewrite <- (encode_decode p), <- (encode_decode q).
  rewrite (isProp_code (encode' p) (encode' q)). reflexivity.
Qed.

End nat_neq.

Module list_neq.

Inductive list_neq
  {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
    | nc : forall (h : A) (t : list A), list_neq R [] (h :: t)
    | cn : forall (h : A) (t : list A), list_neq R (h :: t) []
    | cc1 : forall (h1 h2 : A) (t1 t2 : list A),
              R h1 h2 -> list_neq R (h1 :: t1) (h2 :: t2)
    | cc2 : forall (h : A) (t1 t2 : list A),
              list_neq R t1 t2 -> list_neq R (h :: t1) (h :: t2).

Arguments nc {A R h t}.
Arguments cn {A R h t}.
Arguments cc1 {A R h1 h2 t1 t2} _.
Arguments cc2 {A R h t1 t2} _.

Lemma list_neq_irrefl_aux :
  forall {A : Type} {R : A -> A -> Prop} (l1 l2 : list A),
    (forall x : A, R x x -> False) ->
      list_neq R l1 l2 -> l1 <> l2.
Proof.
  induction 2.
    inversion 1.
    inversion 1.
    inversion 1; subst. apply (H h2). assumption.
    inversion 1; subst. contradiction.
Qed.

Lemma list_neq_irrefl_sym :
  forall {A : Type} {R : A -> A -> Prop} (l1 l2 : list A),
    (forall x y : A, R x y -> R y x) ->
      list_neq R l1 l2 -> list_neq R l2 l1.
Proof.
  induction 2.
    1-3: constructor. apply H. assumption.
    constructor 4. assumption.
Qed.

Lemma list_neq_cotrans :
  forall {A : Type} {R : A -> A -> Prop} (l1 l3 : list A),
    (forall x y z : A, R x z -> R x y \/ R y z) ->
      list_neq R l1 l3 -> forall l2 : list A,
        list_neq R l1 l2 \/ list_neq R l2 l3.
Proof.
  induction 2; intros.
    destruct l2; [right | left]; constructor.
    destruct l2; [left | right]; constructor.
    destruct l2 as [| h t].
      left. constructor.
      destruct (H _ h _ H0).
        left. constructor. assumption.
        right. constructor. assumption.
    destruct l2 as [| h' t'].
      left. constructor.
      destruct (IHlist_neq t').
        left.
Abort.

End list_neq.

Module fun_neq.

Definition fun_neq
  {A B : Type} (R : B -> B -> Prop) (f g : A -> B) : Type :=
    {x : A | R (f x) (g x)}.

