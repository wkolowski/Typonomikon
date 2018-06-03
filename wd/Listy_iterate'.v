Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Fixpoint iterate
  {A : Type} (f : A -> A) (n : nat) (x : A) : list A :=
match n with
    | 0 => []
    | S n' => x :: iterate f n' (f x)
end.

Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
match n with
    | 0 => x
    | S n' => iter f n' (f x)
end.

Lemma isEmpty_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    isEmpty (iterate f n x) =
    match n with
        | 0 => true
        | _ => false
    end.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma length_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    length (iterate f n x) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma iterate_plus :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    iterate f (n + m) x =
    iterate f n x ++ iterate f m (iter f n x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma snoc_iterate_iter :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iterate f n x ++ [iter f n x] = iterate f (S n) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma rev_iterate :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      iterate f n x = rev (iterate g n (iter f n x)).
(* begin hide *)
Proof.
  cbn.
  induction n as [| n']; cbn; intros.
    reflexivity.
Abort.
(* end hide *)

Lemma map_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    map f (iterate f n x) = iterate f n (f x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

(* TODO: join, bind *)

Lemma iterate_replicate :
  forall (A : Type) (n : nat) (x : A),
    iterate id n x = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Import Arith.

Lemma nth_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    nth m (iterate f n x) =
    if leb n m then None else Some (iter f m x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'.
    rewrite nth_nil. reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma head_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    head (iterate f n x) =
    match n with
        | 0 => None
        | S n' => Some x
    end.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma tail_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    tail (iterate f n x) =
    match n with
        | 0 => None
        | S n' => Some (iterate f n' (f x))
    end.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma last_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    last (iterate f n x) =
    match n with
        | 0 => None
        | S n' => Some (iter f n' x)
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    specialize (IHn' (f x)). destruct n'; cbn in *.
      reflexivity.
      cbn in IHn'. assumption.
Qed.
(* end hide *)

Lemma init_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    init (iterate f n x) =
    match n with
        | 0 => None
        | S n' => Some (iterate f n' x)
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. destruct n'; reflexivity.
Qed.
(* end hide *)

Lemma take_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    take m (iterate f n x) = iterate f (min n m) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite take_nil. reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma drop_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    drop m (iterate f n x) =
    iterate f (n - m) (iter f (min n m) x).
Proof.
  induction n as [| n']; cbn; intros.
    rewrite drop_nil. reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma filter_iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      filter p (iterate f n x) =
      if p x then iterate f n x else [].
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct (p x); reflexivity.
    rewrite (IHn' _ H), H. destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma takeWhile_iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      takeWhile p (iterate f n x) =
      if p x then iterate f n x else [].
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct (p x); reflexivity.
    rewrite (IHn' _ H), H. destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma dropWhile_iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      dropWhile p (iterate f n x) =
      if p x then [] else iterate f n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct (p x); reflexivity.
    rewrite (IHn' _ H), H. destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma zipWith_iterate :
  forall
    (A B C: Type) (fa : A -> A) (fb : B -> B) (g : A -> B -> C)
    (na nb : nat) (a : A) (b : B),
      zipWith g (iterate fa na a) (iterate fb nb b) =
      map (fun '(a, b) => g a b)
        (iterate (fun '(a, b) => (fa a, fb b)) (min na nb) (a, b)).
(* begin hide *)
Proof.
  induction na as [| na']; cbn; intros.
    reflexivity.
    destruct nb as [| nb']; cbn.
      reflexivity.
      rewrite IHna'. reflexivity.
Qed.
(* end hide *)

Lemma zip_iterate :
  forall
    (A B : Type) (fa : A -> A) (fb : B -> B) (na nb : nat) (a : A) (b : B),
      zip (iterate fa na a) (iterate fb nb b) =
      iterate (fun '(a, b) => (fa a, fb b)) (min na nb) (a, b).
(* begin hide *)
Proof.
  induction na as [| na']; cbn; intros.
    reflexivity.
    destruct nb as [| nb']; cbn.
      reflexivity.
      rewrite IHna'. reflexivity.
Qed.
(* end hide *)

Lemma intersperse_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x y : A),
    intersperse y (iterate f n x) =
    (fix g (n : nat) (x : A) : list A :=
    match n with
        | 0 => []
        | 1 => [x]
        | S (S n') => x :: y :: (f x) :: g n' (f (f x))
    end) n x.
(* begin hide *)
Proof.
  fix 3. destruct n as [| [| n']]; cbn; intros.
    1-2: reflexivity.
    rewrite <- (intersperse_iterate A f n' (f (f x)) y).
      destruct (iterate f n' (f (f x))); cbn.
        reflexivity.
Abort.
(* end hide *)

Lemma any_iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      any p (iterate f n x) =
      match n with
          | 0 => false
          | _ => p x
      end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct (p x) eqn: Heq; cbn.
      reflexivity.
      rewrite (IHn' _ H). destruct n'; cbn.
        reflexivity.
        rewrite H. assumption.
Qed.
(* end hide *)

Definition isZero (n : nat) : bool :=
match n with
    | 0 => true
    | _ => false
end.

Lemma all_iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      all p (iterate f n x) = orb (isZero n) (p x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite (IHn' _ H). rewrite H. destruct (p x); cbn.
      rewrite Bool.orb_true_r. all: reflexivity.
Qed.
(* end hide *)

Lemma find_iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      find p (iterate f n x) =
      if isZero n then None else if p x then Some x else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite (IHn' _ H). destruct (p x) eqn: Heq.
      reflexivity.
      destruct n'; cbn.
        reflexivity.
        rewrite H, Heq. reflexivity.
Qed.
(* end hide *)

Lemma findLast_iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      findLast p (iterate f n x) =
      match n with
          | 0 => None
          | S n' => if p x then Some (iter f n' x) else None
      end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite (IHn' _ H). destruct n' as [| n'']; cbn.
      reflexivity.
      rewrite H. destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)

Lemma iterate :
  forall (A : Type) (p : A -> bool) (f : A -> A) (n : nat) (x : A),
    (forall x : A, p (f x) = p x) ->
      iterate f n x = .
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
Qed.
(* end hide *)