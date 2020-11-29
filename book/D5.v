(** * D5: Listy *)

(** Lista to najprostsza i najczęściej używana w programowaniu funkcyjnym
    struktura danych. Czas więc przeżyć na własnej skórze ich implementację.

    UWAGA: ten rozdział wyewoluował do stanu dość mocno odbiegającego od
    tego, co jest w bibliotece standardowej — moim zdanem na korzyść. *)

(* begin hide *)
Require Export Recdef.
Require Export Lia Arith.
(* end hide *)

Require Export Bool.
Require Export Nat.

(* begin hide *)
Ltac inv H := inversion H; subst; clear H.
(* end hide *)

(** W części dowodów przydadzą nam się fakty dotyczące arytmetyki liczb
    naturalnych, które możemy znaleźć w module [Arith]. *)

(** Zdefiniuj [list] (bez podglądania). *)

(* begin hide *)
Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.
(* end hide *)

Arguments nil {A}.
Arguments cons {A} _ _.

(*Notation "[ ]" := nil.*)
Notation "[ ]" := nil (format "[ ]").
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** * Proste funkcje *)

(** ** [isEmpty] *)

(** Zdefiniuj funkcję [isEmpty], która sprawdza, czy lista jest pusta. *)

(* begin hide *)
Definition isEmpty {A : Type} (l : list A) : bool :=
match l with
    | [] => true
    | _ => false
end.
(* end hide *)

(** ** [length] *)

(** Zdefiniuj funkcję [length], która oblicza długość listy.

    Przykład:
    [length [1; 2; 3]] = [3]
*)

(* begin hide *)
Fixpoint length {A : Type} (l : list A) : nat :=
match l with
    | [] => 0
    | _ :: t => S (length t)
end.
(* end hide *)

Lemma length_nil :
  forall A : Type, length (@nil A) = 0.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma length_cons :
  forall (A : Type) (h : A) (t : list A),
    exists n : nat, length (h :: t) = S n.
(* begin hide *)
Proof.
  intros. exists (length t). cbn. trivial.
Qed.
(* end hide *)

Lemma length_0 :
  forall (A : Type) (l : list A),
    length l = 0 -> l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    inversion H.
Qed.
(* end hide *)

(** ** [snoc] *)

(** Zdefiniuj funkcję [snoc], która dokleja element [x] na koniec listy
    [l].

    Przykład:
    [snoc 42 [1; 2; 3]] = [[1; 2; 3; 42]]
*)

(* begin hide *)
Fixpoint snoc {A : Type} (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => h :: snoc x t
end.
(* end hide *)

Lemma snoc_isEmpty :
  forall (A : Type) (x : A) (l : list A),
    isEmpty l = true -> snoc x l = [x].
(* begin hide *)
Proof.
  destruct l; cbn.
    reflexivity.
    inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_snoc :
  forall (A : Type) (x : A) (l : list A),
    isEmpty (snoc x l) = false.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma length_snoc :
  forall (A : Type) (x : A) (l : list A),
    length (snoc x l) = S (length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma snoc_inv :
  forall (A : Type) (l1 l2 : list A) (x y : A),
    snoc x l1 = snoc y l2 -> x = y /\ l1 = l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    destruct l2 as [| h2 t2]; inv H.
      split; reflexivity.
      apply (f_equal isEmpty) in H2. rewrite isEmpty_snoc in H2. inv H2.
    destruct l2 as [| h2 t2]; cbn in *.
      inv H. apply (f_equal isEmpty) in H2.
        rewrite isEmpty_snoc in H2. inv H2.
      inv H. destruct (IHt1 _ _ _ H2). subst. split; reflexivity.
Qed.
(* end hide *)

(** ** [app] *)

(** Zdefiniuj funkcję [app], która skleja dwie listy.

    Przykład:
    [app [1; 2; 3] [4; 5; 6]] = [[1; 2; 3; 4; 5; 6]]
*)

(* begin hide *)
Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
match l1 with
    | [] => l2
    | h :: t => h :: app t l2
end.
(* end hide *)

Notation "l1 ++ l2" := (app l1 l2).

Lemma app_nil_l :
  forall (A : Type) (l : list A),
    [] ++ l = l.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma app_nil_r :
  forall (A : Type) (l : list A),
    l ++ [] = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma app_assoc :
  forall (A : Type) (l1 l2 l3 : list A),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Lemma isEmpty_app :
  forall (A : Type) (l1 l2 : list A),
    isEmpty (l1 ++ l2) = andb (isEmpty l1) (isEmpty l2).
(* begin hide *)
Proof.
  destruct l1, l2; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_app :
  forall (A : Type) (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intro.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Lemma snoc_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    snoc x (l1 ++ l2) = l1 ++ snoc x l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma app_snoc_l :
  forall (A : Type) (x : A) (l1 l2 : list A),
    snoc x l1 ++ l2 = l1 ++ x :: l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma app_snoc_r :
  forall (A : Type) (x : A) (l1 l2 : list A),
    l1 ++ snoc x l2 = snoc x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma snoc_app_singl :
  forall (A : Type) (x : A) (l : list A),
    snoc x l = l ++ [x].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma app_cons_l :
  forall (A : Type) (x : A) (l1 l2 : list A),
    (x :: l1) ++ l2 = x :: (l1 ++ l2).
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Lemma app_cons_r :
  forall (A : Type) (x : A) (l1 l2 : list A),
    l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    f_equal. rewrite IHt1. trivial.
Qed.
(* end hide *)

Lemma no_infinite_cons :
  forall (A : Type) (x : A) (l : list A),
    l = x :: l -> False.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    inversion H. apply IHt. assumption.
Qed.
(* end hide *)

Lemma no_infinite_app :
  forall (A : Type) (l l' : list A),
    l' <> [] -> l = l' ++ l -> False.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite app_nil_r in H0. subst. apply H. trivial.
    destruct l'.
      contradiction H. trivial.
      inversion H0. apply IHt with (l' ++ [a]).
        intro. assert (length (l' ++ [a]) = length (@nil A)).
          rewrite H1. trivial.
          rewrite length_app in H4. cbn in H4. rewrite plus_comm in H4.
            inversion H4.
        rewrite <- app_cons_r. assumption.
Qed.
(* end hide *)

Lemma app_inv_l :
  forall (A : Type) (l l1 l2 : list A),
    l ++ l1 = l ++ l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    apply IHt. inversion H. trivial.
Qed.
(* end hide *)

Lemma app_inv_r :
  forall (A : Type) (l l1 l2 : list A),
    l1 ++ l = l2 ++ l -> l1 = l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    destruct l2.
      trivial.
      cut False. inversion 1. eapply no_infinite_app; eauto. inversion 1.
    destruct l2.
      cbn in H. cut False. inversion 1. symmetry in H.
        rewrite <- app_cons_l in H. eapply no_infinite_app; eauto. inversion 1.
      inversion H. f_equal. apply IHt1. assumption.
Qed.
(* end hide *)

Lemma app_eq_nil :
  forall (A : Type) (l1 l2 : list A),
    l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    split; trivial.
    inversion H.
Qed.
(* end hide *)

(** ** [rev] *)

(** Zdefiniuj funkcję [rev], która odwraca listę.

    Przykład:
    [rev [1; 2; 3]] = [[3; 2; 1]]
*)

(* begin hide *)
Fixpoint rev {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => rev t ++ [h]
end.
(* end hide *)

Lemma isEmpty_rev :
  forall (A : Type) (l : list A),
    isEmpty (rev l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    rewrite isEmpty_app. cbn. rewrite Bool.andb_false_r. reflexivity.
Qed.
(* end hide *)

Lemma length_rev :
  forall (A : Type) (l : list A),
    length (rev l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite length_app, plus_comm. cbn. rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma snoc_rev :
  forall (A : Type) (x : A) (l : list A),
    snoc x (rev l) = rev (x :: l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. rewrite snoc_app, <- app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma rev_snoc :
  forall (A : Type) (x : A) (l : list A),
    rev (snoc x l) = x :: rev l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma rev_app :
  forall (A : Type) (l1 l2 : list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intro.
    rewrite app_nil_r. trivial.
    rewrite IHt1. rewrite app_assoc. trivial.
Qed.
(* end hide *)

Lemma rev_inv :
  forall (A : Type) (l : list A),
    rev (rev l) = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite rev_app. rewrite IHt. cbn. trivial.
Qed.
(* end hide *)

(** ** [map] *)

(** Zdefiniuj funkcję [map], która aplikuje funkcję [f] do każdego
    elementu listy.

    Przykład:
*)

(** [map isEmpty [[]; [1]; [2; 3]; []]] = [[true; false; false; true]] *)

(* begin hide *)
Fixpoint map {A B : Type} (f : A -> B) (la : list A) : list B :=
match la with
    | [] => []
    | h :: t => f h :: map f t
end.
(* end hide *)

Lemma map_id :
  forall (A : Type) (l : list A),
    map id l = l.
(* begin hide *)
Proof.
  unfold id. induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma map_map :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (fun x : A => g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma isEmpty_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    isEmpty (map f l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    length (map f l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma map_snoc :
  forall (A B : Type) (f : A -> B) (x : A) (l : list A),
    map f (snoc x l) = snoc (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma map_app :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Lemma map_rev :
  forall (A B : Type) (f : A -> B) (l : list A),
    map f (rev l) = rev (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite map_app, IHt. cbn. trivial.
Qed.
(* end hide *)

Lemma map_ext :
  forall (A B : Type) (f g : A -> B) (l : list A),
    (forall x : A, f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intro.
    trivial.
    rewrite H, IHt; trivial.
Qed.
(* end hide *)

(** ** [join] *)

(** Zdefiniuj funkcję [join], która spłaszcza listę list.

    Przykład:
    [join [[1; 2; 3]; [4; 5; 6]; [7]]] =
    [[1; 2; 3; 4; 5; 6; 7]]
*)

(* begin hide *)
Fixpoint join {A : Type} (lla : list (list A)) : list A :=
match lla with
    | [] => []
    | h :: t => h ++ join t
end.
(* end hide *)

Lemma join_snoc :
  forall (A : Type) (x : list A) (l : list (list A)),
    join (snoc x l) = join l ++ x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    rewrite ?IHt, app_assoc. reflexivity.
Qed.
(* end hide *)

Lemma join_app :
  forall (A : Type) (l1 l2 : list (list A)),
    join (l1 ++ l2) = join l1 ++ join l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    rewrite IHt1, app_assoc. trivial.
Qed.
(* end hide *)

Lemma rev_join :
  forall (A : Type) (l : list (list A)),
    rev (join l) = join (rev (map rev l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite rev_app, join_app, IHt. cbn. rewrite app_nil_r. reflexivity.
Qed.
(* end hide *)

Lemma map_join :
  forall (A B : Type) (f : A -> B) (l : list (list A)),
    map f (join l) = join (map (map f) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    rewrite map_app, IHt. trivial.
Qed.
(* end hide *)

(** ** [bind] *)

(** Zdefiniuj funkcję [bind], która spełnia specyfikację [bind_spec].
    Użyj rekursji, ale nie używaj funkcji [join] ani [map]. *)

(* begin hide *)
Fixpoint bind {A B : Type} (f : A -> list B) (l : list A) : list B :=
match l with
    | [] => []
    | h :: t => f h ++ bind f t
end.
(* end hide *)

Lemma bind_spec :
  forall (A B : Type) (f : A -> list B) (l : list A),
    bind f l = join (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma bind_snoc :
  forall (A B : Type) (f : A -> list B) (x : A) (l : list A),
    bind f (snoc x l) = bind f l ++ f x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    rewrite ?IHt, app_assoc. reflexivity.
Qed.
(* end hide *)

(** ** [replicate] *)

(** Zdefiniuj funkcję [replicate], która powiela dany element [n] razy,
    tworząc listę.

    Przykład:
    [replicate 5 0] = [[0; 0; 0; 0; 0]]
*)

(* begin hide *)
Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
match n with
    | 0 => []
    | S n' => x :: replicate n' x
end.
(* end hide *)

Definition isZero (n : nat) : bool :=
match n with
    | 0 => true
    | _ => false
end.

Lemma isEmpty_replicate :
  forall (A : Type) (n : nat) (x : A),
    isEmpty (replicate n x) = if isZero n then true else false.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma length_replicate :
  forall (A : Type) (n : nat) (x : A),
    length (replicate n x) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Lemma snoc_replicate :
  forall (A : Type) (x : A) (n : nat),
    snoc x (replicate n x) = replicate (S n) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.
(* end hide *)

Lemma replicate_plus :
  forall (A : Type) (n m : nat) (x : A),
    replicate (n + m) x = replicate n x ++ replicate m x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Lemma replicate_plus_comm :
  forall (A : Type) (n m : nat) (x : A),
    replicate (n + m) x = replicate (m + n) x.
(* begin hide *)
Proof.
  intros. f_equal. apply plus_comm.
Qed.
(* end hide *)

Lemma rev_replicate :
  forall (A : Type) (n : nat) (x : A),
    rev (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; trivial.
  change [x] with (replicate 1 x).
  rewrite IHn', <- replicate_plus, plus_comm. cbn. trivial.
Qed.
(* end hide *)

Lemma map_replicate :
  forall (A B : Type) (f : A -> B) (n : nat) (x : A),
    map f (replicate n x) = replicate n (f x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intro; try rewrite IHn'; trivial.
Qed.
(* end hide *)

(** ** [iterate] i [iter] *)

(** Zdefiniuj funkcję [iterate]. [iterate f n x] to lista postaci
    [[x, f x, f (f x), ..., f (... (f x) ...)]] o długości [n]. *)

(** Przykład: *)

(** [iterate S 5 0] = [[0; 1; 2; 3; 4]] *)

(** Zdefiniuj też funkcję [iter], która przyda się do podania
    charakteryzacji funkcji [iterate]. Zgadnij, czym ma ona być. *)

(* begin hide *)
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
(* end hide *)

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

Lemma snoc_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    snoc (iter f n x) (iterate f n x) =
    iterate f (S n) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
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

(* begin hide *)
Lemma iter_inverse :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      g (iter f n (f x)) = iter f n x.
Proof.
  induction n as [| n']; cbn; intros.
    apply H.
    apply IHn'. assumption.
Qed.

Lemma rev_iterate_aux :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      rev (iterate f (S n) x) = (iterate g (S n) (iter f n x)).
Proof.
  induction n as [| n']; intros.
    cbn. reflexivity.
    rewrite <- snoc_iterate_iter, rev_app, IHn'.
      2: assumption.
      cbn. do 2 f_equal; rewrite iter_inverse; trivial.
Qed.

Lemma rev_iterate :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      rev (iterate f n x) = (iterate g n (iter f (n - 1) x)).
Proof.
  destruct n as [| n']; intros.
    cbn. reflexivity.
    rewrite (rev_iterate_aux _ _ _ _ _ H). cbn.
      rewrite <- ?minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma map_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    map f (iterate f n x) = iterate f n (f x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma map_iter_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    map (iter f m) (iterate f n x) =
    iterate f n (iter f m x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. revert x. induction m as [| m']; cbn; intros.
      reflexivity.
      rewrite IHm'. reflexivity.
Qed.
(* end hide *)

Lemma iterate_replicate :
  forall (A : Type) (n : nat) (x : A),
    iterate id n x = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

(** ** [head], [tail] i [uncons] *)

(** *** [head] *)

(** Zdefiniuj funkcję [head], która zwraca głowę (pierwszy element)
    listy lub [None], gdy lista jest pusta.

    Przykład:
    [head [1; 2; 3]] = [Some 1]
*)

(* begin hide *)
Definition head {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | h :: _ => Some h
end.
(* end hide *)

Lemma head_nil :
  forall (A : Type), head [] = (@None A).
(* begin hide *)
Proof.
  cbn. reflexivity.
Qed.
(* end hide *)

Lemma head_cons :
  forall (A : Type) (h : A) (t : list A),
    head (h :: t) = Some h.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma head_isEmpty_true :
  forall (A : Type) (l : list A),
    isEmpty l = true -> head l = None.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_head_not_None :
  forall (A : Type) (l : list A),
    head l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma head_snoc :
  forall (A : Type) (x : A) (l : list A),
    head (snoc x l) =
    if isEmpty l then Some x else head l.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma head_app :
  forall (A : Type) (l1 l2 : list A),
    head (l1 ++ l2) =
    match l1 with
        | [] => head l2
        | h :: _ => Some h
    end.
(* begin hide *)
Proof. destruct l1; reflexivity. Qed.
(* end hide *)

Lemma head_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    head (map f l) =
    match l with
        | [] => None
        | h :: _ => Some (f h)
    end.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma head_replicate_S :
  forall (A : Type) (n : nat) (x : A),
    head (replicate (S n) x) = Some x.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma head_replicate :
  forall (A : Type) (n : nat) (x : A),
    head (replicate n x) =
    match n with
        | 0 => None
        | _ => Some x
    end.
(* begin hide *)
Proof. destruct n; reflexivity. Qed.
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

(** *** [tail] *)

(** Zdefiniuj funkcję [tail], która zwraca ogon listy (czyli wszystkie
    jej elementy poza głową) lub [None], gdy lista jest pusta.

    Przykład:
    [tail [1; 2; 3]] = [Some [2; 3]]
*)

(* begin hide *)
Definition tail {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | _ :: t => Some t
end.
(* end hide *)

Lemma tail_nil :
  forall A : Type, tail (@nil A) = None.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma tail_cons :
  forall (A : Type) (h : A) (t : list A),
    tail (h :: t) = Some t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma tail_isEmpty_true :
  forall (A : Type) (l : list A),
    isEmpty l = true -> tail l = None.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_tail_not_None :
  forall (A : Type) (l : list A),
    tail l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma tail_snoc :
  forall (A : Type) (x : A) (l : list A),
    tail (snoc x l) =
    match tail l with
        | None => Some []
        | Some t => Some (snoc x t)
    end.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma tail_app :
  forall (A : Type) (l1 l2 : list A),
    tail (l1 ++ l2) =
    match l1 with
        | [] => tail l2
        | h :: t => Some (t ++ l2)
    end.
(* begin hide *)
Proof.
  destruct l1 as [| h t]; cbn; reflexivity.
Qed.
(* end hide *)

Lemma tail_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    tail (map f l) =
    match l with
        | [] => None
        | _ :: t => Some (map f t)
    end.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma tail_replicate :
  forall (A : Type) (n : nat) (x : A),
    tail (replicate n x) =
    match n with
        | 0 => None
        | S n' => Some (replicate n' x)
    end.
(* begin hide *)
Proof. destruct n; reflexivity. Qed.
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

(** *** [uncons] *)

(** Zdefiniuj funkcję [uncons], która zwraca parę złożoną z głowy i ogona
    listy lub [None], gdy lista jest pusta. Nie używaj funkcji [head]
    ani [tail]. Udowodnij poniższą specyfikację.

    Przykład:
    [uncons [1; 2; 3]] = [Some (1, [2; 3])]
*)

(* begin hide *)
Definition uncons {A : Type} (l : list A) : option (A * list A) :=
match l with
    | [] => None
    | h :: t => Some (h, t)
end.
(* end hide *)

Lemma uncons_spec :
  forall (A : Type) (l : list A),
    uncons l =
    match head l, tail l with
        | Some h, Some t => Some (h, t)
        | _, _ => None
    end.
(* begin hide *)
Proof. destruct l; reflexivity. Qed.
(* end hide *)

(** ** [last], [init] i [unsnoc] *)

(** *** [last] *)

(** Zdefiniuj funkcję [last], która zwraca ostatni element listy lub
    [None], gdy lista jest pusta.

    Przykład:
    [last [1; 2; 3]] = [Some 3]
*)

(* begin hide *)
Function last {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | [x] => Some x
    | h :: t => last t
end.
(* end hide *)

Lemma last_nil :
  forall (A : Type), last [] = (@None A).
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma last_isEmpty_true :
  forall (A : Type) (l : list A),
    isEmpty l = true -> last l = None.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_last_not_None :
  forall (A : Type) (l : list A),
    last l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma last_snoc :
  forall (A : Type) (x : A) (l : list A),
    last (snoc x l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (snoc x t).
      inversion IHt.
      assumption.
Qed.
(* end hide *)

Lemma last_spec :
  forall (A : Type) (l : list A) (x : A),
    last (l ++ [x]) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. case_eq (t ++ [x]); cbn; intros.
      apply app_eq_nil in H. destruct H. inversion H0.
      reflexivity.
Qed.
(* end hide *)

Lemma last_app :
  forall (A : Type) (l1 l2 : list A),
    last (l1 ++ l2) =
    match l2 with
        | [] => last l1
        | _ => last l2
    end.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    destruct l2; reflexivity.
    destruct t1; cbn in *; intros.
      reflexivity.
      rewrite <- IHt1. reflexivity.
Qed.
(* end hide *)

Lemma last_replicate_S :
  forall (A : Type) (n : nat) (x : A),
    last (replicate (S n) x) = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn in *; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma last_replicate :
  forall (A : Type) (n : nat) (x : A),
    last (replicate n x) =
    match n with
        | 0 => None
        | _ => Some x
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn in *; intros.
    reflexivity.
    rewrite IHn'. destruct n'; reflexivity.
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

(** *** [init] *)

(** Zdefiniuj funkcję [init], która zwraca wszystkie elementy listy poza
    ostatnim lub [None], gdy lista jest pusta.

    Przykład:
    [init [1; 2; 3]] = [Some [1; 2]]
*)

(* begin hide *)
Fixpoint init {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | h :: t => match init t with
        | None => Some []
        | Some t' => Some (h :: t')
    end
end.
(* end hide *)

Lemma init_None :
  forall (A : Type) (l : list A),
    init l = None -> l = [].
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    reflexivity.
    destruct (init t); inv H.
Qed.
(* end hide *)

Lemma init_snoc :
  forall (A : Type) (x : A) (l : list A),
    init (snoc x l) = Some l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma init_app :
  forall (A : Type) (l1 l2 : list A),
    init (l1 ++ l2) =
    match init l2 with
        | None => init l1
        | Some i => Some (l1 ++ i)
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (init l2); reflexivity.
    rewrite IHt. destruct (init l2); reflexivity.
Qed.
(* end hide *)

Lemma init_spec :
  forall (A : Type) (l : list A) (x : A),
    init (l ++ [x]) = Some l.
(* begin hide *)
Proof.
  intros. rewrite init_app. cbn. rewrite app_nil_r. reflexivity.
Qed.
(* end hide *)

Lemma init_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    init (map f l) =
    match l with
        | [] => None
        | h :: t =>
            match init t with
                | None => Some []
                | Some i => Some (map f (h :: i))
            end
    end.
(* begin hide *)
Proof.
  induction l as [| x [| y t]]; cbn in *.
    1-2: reflexivity.
    rewrite IHl. destruct (init t); cbn; reflexivity.
Qed.
(* end hide *)

Lemma init_replicate :
  forall (A : Type) (n : nat) (x : A),
    init (replicate n x) =
    match n with
        | 0 => None
        | S n' => Some (replicate n' x)
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. destruct n'; cbn; reflexivity.
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

Lemma init_last :
  forall (A : Type) (l l' : list A) (x : A),
    init l = Some l' -> last l = Some x -> l = l' ++ [x].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (init t) eqn: H_init.
      inversion H; subst. destruct (last t) eqn: H_last.
        rewrite (IHt _ _ eq_refl eq_refl). cbn. destruct t; inversion H0.
          inversion H_last.
          reflexivity.
        destruct t.
          inversion H_init.
          inversion H0.
      destruct t.
        inversion H; inversion H0; cbn. reflexivity.
        cbn in *. destruct (init t); inversion H_init.
Qed.
(* end hide *)

(** *** [unsnoc] *)

(** Zdefiniuj funkcję [unsnoc], która rozbija listę na parę złożoną z
    ostatniego elementu oraz całej reszty lub zwraca [None] gdy lista
    jest pusta. Nie używaj funkcji [last] ani [init]. Udowodnij poniższą
    specyfikację.

    Przykład:
    [unsnoc [1; 2; 3]] = [Some (3, [1; 2])]
*)

(* begin hide *)
Fixpoint unsnoc {A : Type} (l : list A) : option (A * list A) :=
match l with
    | [] => None
    | h :: t =>
        match unsnoc t with
            | None => Some (h, [])
            | Some (last, init) => Some (last, h :: init)
        end
end.
(* end hide *)

Lemma unsnoc_None :
  forall (A : Type) (l : list A),
    unsnoc l = None -> l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (unsnoc t); try destruct p; inv H.
Qed.
(* end hide *)

Lemma unsnoc_spec :
  forall (A : Type) (l : list A),
    unsnoc l =
    match last l, init l with
        | Some x, Some l' => Some (x, l')
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (last t) eqn: Hlast, (init t) eqn: Hinit; cbn.
      destruct t; cbn; inversion IHt. reflexivity.
      destruct t; cbn.
        reflexivity.
        cbn in IHt. destruct (unsnoc t).
          destruct p. 1-2: inversion IHt.
      destruct t; cbn in *.
        inversion Hinit.
        destruct (unsnoc t); cbn in *.
          destruct p. 1-2: inversion IHt.
      destruct t; cbn in *.
        reflexivity.
        destruct (unsnoc t); cbn in *.
          destruct p. 1-2: inversion IHt.
Qed.
(* end hide *)

(** *** Dualności [head] i [last], [tail] i [init] oraz ciekawostki *)

Lemma last_rev :
  forall (A : Type) (l : list A),
    last (rev l) = head l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite last_app. cbn. reflexivity.
Qed.
(* end hide *)

Lemma head_rev :
  forall (A : Type) (l : list A),
    head (rev l) = last l.
(* begin hide *)
Proof.
  intros. rewrite <- last_rev, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma tail_rev :
  forall (A : Type) (l : list A),
    tail (rev l) =
    match init l with
        | None => None
        | Some t => Some (rev t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite tail_app. destruct (rev t); cbn in *.
      destruct (init t).
        inversion IHt.
        reflexivity.
      destruct (init t); cbn.
        inversion IHt; subst. reflexivity.
        inversion IHt.
Qed.
(* end hide *)

Lemma init_rev :
  forall (A : Type) (l : list A),
    init (rev l) =
    match tail l with
        | None => None
        | Some t => Some (rev t)
    end.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_inv _ l) at 2. rewrite tail_rev.
  destruct (init (rev l)); rewrite ?rev_inv; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma tail_decomposition :
  forall (A : Type) (l : list A),
    l = [] \/
    exists (h : A) (t : list A),
      tail l = Some t /\ head l = Some h /\ l = h :: t.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    left. reflexivity.
    right. exists h, t. repeat split.
Qed.
(* end hide *)

Lemma init_decomposition :
  forall (A : Type) (l : list A),
    l = [] \/
    exists (h : A) (t : list A),
      init l = Some t /\ last l = Some h /\ l = t ++ [h].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    left. reflexivity.
    destruct IHt; subst; cbn.
      right. exists h, []. repeat split; reflexivity.
      destruct H as (h' & t' & H1 & H2 & H3).
        right. rewrite H1, H2, H3. exists h', (h :: t'). repeat split.
          destruct (t' ++ [h']) eqn: Heq.
            apply (f_equal length) in Heq.
              rewrite length_app, plus_comm in Heq. cbn in Heq. inversion Heq.
            reflexivity.
Qed.
(* end hide *)

(* end hide *)

Lemma bilateral_decomposition :
  forall (A : Type) (l : list A),
    l = [] \/
    (exists x : A, l = [x]) \/
    exists (x y : A) (l' : list A), l = x :: l' ++ [y].
(* begin hide *)
Proof.
  destruct l as [| h t].
    left. reflexivity.
    right. destruct (init_decomposition A t); subst.
      left. exists h. reflexivity.
      right. destruct H as (h' & t' & H1 & H2 & H3).
        exists h, h', t'. rewrite H3. reflexivity.
Qed.
(* end hide *)

(** ** [nth] *)

(** Zdefiniuj funkcję [nth], która zwraca n-ty element listy lub [None],
    gdy nie ma n-tego elementu.

    Przykład:
*)

(** [nth 1 [1; 2; 3]] = [Some 2] *)

(** [nth 42 [1; 2; 3]] = [None] *)

(* begin hide *)
Fixpoint nth {A : Type} (n : nat) (l : list A) {struct l} : option A :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some h
    | h :: t, S n' => nth n' t
end.
(* end hide *)

Lemma nth_nil :
  forall (A : Type) (n : nat),
    nth n (@nil A) = None.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma nth_isEmpty_true :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty l = true -> nth n l = None.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_nth_not_None :
  forall (A : Type) (l : list A) (n : nat),
    nth n l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma nth_length_lt :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A, nth n l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      exists h. reflexivity.
      destruct (IHt _ (lt_S_n _ _ H)) as [x IH]. exists x. assumption.
Qed.
(* end hide *)

Lemma nth_length_ge :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> nth n l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inversion H.
      apply IHt, le_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_snoc_length_lt :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l -> nth n (snoc x l) = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      reflexivity.
      apply IHt, lt_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_snoc_length_eq :
  forall (A : Type) (x : A) (l : list A),
    nth (length l) (snoc x l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma nth_snoc :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    nth n (snoc x l) =
    if n <? length l then nth n l
    else if n =? length l then Some x
    else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma nth_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    nth n (l1 ++ l2) =
    match nth n l1 with
        | None => nth (n - length l1) l2
        | Some x => Some x
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. reflexivity.
    destruct n as [| n'].
      reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma nth_app_l :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n < length l1 -> nth n (l1 ++ l2) = nth n l1.
(* begin hide *)
Proof.
  intros. rewrite nth_app.
  destruct (nth_length_lt _ _ _ H). rewrite H0. reflexivity.
Qed.
(* end hide *)

Lemma nth_app_r :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 <= n -> nth n (l1 ++ l2) = nth (n - length l1) l2.
(* begin hide *)
Proof.
  intros. rewrite nth_app, nth_length_ge.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma nth_rev :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> nth n (rev l) = nth (length l - S n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (length t - n) eqn: Heq.
      assert (n = length t) by lia. rewrite nth_app_r.
        rewrite length_rev, <- H0, minus_diag. cbn. reflexivity.
        rewrite length_rev, <- H0. reflexivity.
      rewrite nth_app_l.
        rewrite IHt.
          f_equal. lia.
          lia.
        rewrite length_rev. lia.
Qed.
(* begin hide *)

Lemma nth_split :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> exists l1 l2 : list A,
      l = l1 ++ x :: l2 /\ length l1 = n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H; subst. exists [], t. cbn. split; reflexivity.
      destruct (IHt _ _ H) as (l1 & l2 & IH1 & IH2); subst.
        exists (h :: l1), l2. cbn. split; reflexivity.
Qed.
(* end hide *)

Lemma nth_None :
  forall (A : Type) (l : list A) (n : nat),
    nth n l = None -> length l <= n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n'].
      inversion H.
      apply le_n_S, IHt, H.
Qed.
(* end hide *)

Lemma nth_Some :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> n < length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      apply le_n_S, le_0_n.
      apply lt_n_S, (IHt _ _ H).
Qed.
(* end hide *)

Lemma nth_spec' :
  forall (A : Type) (l : list A) (n : nat),
    match nth n l with
        | None => length l <= n
        | Some x => exists l1 l2 : list A,
                      l = l1 ++ x :: l2 /\ length l1 = n
    end.
(* begin hide *)
Proof.
  intros. destruct (nth n l) eqn: Heq.
    apply nth_split. assumption.
    apply nth_None. assumption.
Qed.
(* end hide *)

Lemma nth_map_Some :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> nth n (map f l) = Some (f x).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H. reflexivity.
      apply IHt. assumption.
Qed.
(* end hide *)

Lemma nth_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    nth n (map f l) =
    match nth n l with
        | None => None
        | Some x => Some (f x)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma nth_replicate :
  forall (A : Type) (n i : nat) (x : A),
    i < n -> nth i (replicate n x) = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct i; inversion H.
    destruct i as [| i'].
      reflexivity.
      apply IHn', lt_S_n, H.
Qed.
(* end hide *)

Lemma nth_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    nth m (iterate f n x) =
    if leb n m then None else Some (iter f m x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma head_nth :
  forall (A : Type) (l : list A),
    nth 0 l = head l.
(* begin hide *)
Proof. destruct l; reflexivity. Qed.
(* end hide *)

Lemma last_nth :
  forall (A : Type) (l : list A),
    last l = nth (length l - 1) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct t; cbn in *.
      reflexivity.
      rewrite IHt, <- minus_n_O. reflexivity.
Qed.
(* end hide *)

(** ** [take] *)

(** Zdefiniuj funkcję [take], która bierze z listy [n] początkowych
    elementów.

    Przykład:
*)

(** [take 2 [1; 2; 3]] = [[1; 2]] *)

(* begin hide *)
Fixpoint take {A : Type} (n : nat) (l : list A) {struct l} : list A :=
match l, n with
    | [], _ => []
    | _, 0 => []
    | h :: t, S n' => h :: take n' t
end.
(* end hide *)

Lemma take_0 :
  forall (A : Type) (l : list A),
    take 0 l = [].
(* begin hide *)
Proof. destruct l; reflexivity. Qed.
(* end hide *)

Lemma take_nil :
  forall (A : Type) (n : nat),
    take n [] = @nil A.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma take_S_cons :
  forall (A : Type) (n : nat) (h : A) (t : list A),
    take (S n) (h :: t) = h :: take n t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma isEmpty_take :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty (take n l) = orb (beq_nat 0 n) (isEmpty l).
(* begin hide *)
Proof.
  destruct l as [| h t], n as [| n']; cbn; intros; trivial.
Qed.
(* end hide *)

Lemma take_length :
  forall (A : Type) (l : list A),
    take (length l) l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma take_length' :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> take n l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inversion H.
      apply le_S_n in H. rewrite (IHt _ H). reflexivity.
Qed.
(* end hide *)

Lemma length_take :
  forall (A : Type) (l : list A) (n : nat),
    length (take n l) = min (length l) n.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma take_snoc_lt :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l -> take n (snoc x l) = take n l.
(* begin hide *)
(* TODO: zabij take_snoc_lt *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?(IHt _ (lt_S_n _ _ H)). reflexivity.
Qed.
(* end hide *)

Lemma take_snoc_le :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n <= length l -> take n (snoc x l) = take n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      f_equal. apply IHt, le_S_n. assumption.
Qed.
(* end hide *)

Lemma take_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    take n (l1 ++ l2) = take n l1 ++ take (n - length l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; destruct n; cbn;
  rewrite ?IHt, ?take_0; reflexivity.
Qed.
(* end hide *)

Lemma take_app_l :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n <= length l1 -> take n (l1 ++ l2) = take n l1.
(* begin hide *)
Proof.
  induction l1 as [| h t]; destruct n; cbn; rewrite ?take_0.
    1,3: reflexivity.
    inversion 1.
    intro. apply le_S_n in H. rewrite (IHt _ _ H). reflexivity.
Qed.
(* end hide *)

Lemma take_app_r :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 < n ->
      take n (l1 ++ l2) = l1 ++ take (n - length l1) l2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H.
    destruct l1; cbn.
      reflexivity.
      rewrite IHn'.
        reflexivity.
        apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma take_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    take n (map f l) = map f (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: take_join, take_bind (chyba potrzebne będzie decompose) *)

(*Lemma take_join :
  forall (A : Type) (ll : list (list A)) (n : nat),
    exists m1 : nat,
      match nth (S m1) ll with
          | None => m1 = 0
          | Some l =>
              exists m2 : nat,
                take n (join ll) = join (take m1 ll) ++ take m2 l
      end.
Proof.
  induction ll as [| h t]; cbn; intros.
    exists 0. reflexivity.
    induction n as [| n'].
      destruct t; cbn.
        exists 0. cbn. reflexivity.
        destruct (IHt 0) as (m1 & IH). exists (S m1). cbn in *.
          destruct (nth m1 t).
            
    destruct (IHt n) as (m1 & IH). exists (S m1).
      destruct (nth (S m1) t); cbn.
        destruct IH as (m2 & IH). exists m2. rewrite take_app.
    
Qed.*)
(* end hide *)

Lemma take_replicate :
  forall (A : Type) (n m : nat) (x : A),
    take m (replicate n x) = replicate (min n m) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma take_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    take m (iterate f n x) = iterate f (min n m) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma head_take :
  forall (A : Type) (l : list A) (n : nat),
    head (take n l) =
    if beq_nat 0 n then None else head l.
(* begin hide *)
Proof.
  destruct n, l; reflexivity.
Qed.
(* end hide *)

Lemma last_take :
  forall (A : Type) (l : list A) (n : nat),
    last (take (S n) l) = nth (min (length l - 1) n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct t as [| h' t']; cbn in *.
      reflexivity.
      destruct n; cbn.
        reflexivity.
        rewrite IHt, <- minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma tail_take :
  forall (A : Type) (l : list A) (n : nat),
    tail (take n l) =
    match n, l with
        | 0, _ => None
        | _, [] => None
        | S n', h :: t => Some (take n' t)
    end.
(* begin hide *)
Proof.
  destruct l, n; reflexivity.
Qed.
(* end hide *)

Lemma init_take :
  forall (A : Type) (l : list A) (n : nat),
    init (take n l) =
    match n, l with
        | 0, _ => None
        | _, [] => None
        | S n', h :: t => Some (take (min n' (length l - 1)) l)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct n', t; cbn.
        1-3: reflexivity.
        rewrite <- minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma nth_take :
  forall (A : Type) (l : list A) (n m : nat),
    nth m (take n l) =
    if leb (S m) n then nth m l else None.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n'];
  cbn; intros; rewrite ?nth_nil.
    1,3: reflexivity.
    destruct (_ <=? _); reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHt. destruct n'; reflexivity.
Qed.
(* end hide *)

Lemma take_take :
  forall (A : Type) (l : list A) (n m : nat),
    take m (take n l) = take (min n m) l.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n, m; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma take_interesting :
  forall (A : Type) (l1 l2 : list A),
    (forall n : nat, take n l1 = take n l2) -> l1 = l2.
(* begin hide *)
Proof.
  intros. specialize (H (max (length l1) (length l2))).
  rewrite ?take_length' in H.
    assumption.
    apply Max.le_max_r.
    apply Max.le_max_l.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: insert_take, insert_drop, zip, unzip, zipWith, intersperse *)
(* end hide *)

(** ** [drop] *)

(** Zdefiniuj funkcję [drop], która wyrzuca z listy [n] początkowych
    elementów i zwraca to, co zostało.

    Przykład:
*)

(** [drop 2 [1; 2; 3]] = [[3]] *)

(* begin hide *)
Fixpoint drop {A : Type} (n : nat) (l : list A) {struct l} : list A :=
match l, n with
    | [], _ => []
    | _, 0 => l
    | h :: t, S n' => drop n' t
end.
(* end hide *)

Lemma drop_0 :
  forall (A : Type) (l : list A),
    drop 0 l = l.
(* begin hide *)
Proof. destruct l; reflexivity. Qed.
(* end hide *)

Lemma drop_nil :
  forall (A : Type) (n : nat),
    drop n [] = @nil A.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma drop_S_cons :
  forall (A : Type) (n : nat) (h : A) (t : list A),
    drop (S n) (h :: t) = drop n t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma isEmpty_drop :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty (drop n l) = leb (length l) n.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn.
    1-3: reflexivity.
    apply IHt.
Qed.
(* end hide *)

Lemma drop_length :
  forall (A : Type) (l : list A),
    drop (length l) l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma drop_length' :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> drop n l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    1-2: reflexivity.
    inversion H.
    apply IHt, le_S_n. assumption.
Qed.
(* end hide *)

Lemma length_drop :
  forall (A : Type) (l : list A) (n : nat),
    length (drop n l) = length l - n.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma drop_snoc_le :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n <= length l -> drop n (snoc x l) = snoc x (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      apply IHt, le_S_n. assumption.
Qed.
(* end hide *)

Lemma drop_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    drop n (l1 ++ l2) = drop n l1 ++ drop (n - length l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; destruct n; cbn;
  rewrite ?IHt, ?drop_0; reflexivity.
Qed.
(* end hide *)

Lemma drop_app_l :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n <= length l1 -> drop n (l1 ++ l2) = drop n l1 ++ l2.
(* begin hide *)
Proof.
  intros. rewrite <- Nat.sub_0_le in H.
  rewrite drop_app, H, drop_0. reflexivity.
Qed.
(* end hide *)

Lemma drop_app_r :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 < n -> drop n (l1 ++ l2) = drop (n - length l1) l2.
(* begin hide *)
Proof.
  intros. rewrite drop_app, drop_length'.
    cbn. reflexivity.
    apply le_trans with (S (length l1)).
      apply le_S, le_n.
      assumption.
Qed.
(* end hide *)

Lemma drop_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    drop n (map f l) = map f (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: drop_join, drop_bind *)
(* end hide *)

Lemma drop_replicate :
  forall (A : Type) (n m : nat) (x : A),
    drop m (replicate n x) = replicate (n - m) x.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m; cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma drop_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    drop m (iterate f n x) =
    iterate f (n - m) (iter f (min n m) x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma head_drop :
  forall (A : Type) (l : list A) (n : nat),
    head (drop n l) = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n; cbn; trivial.
Qed.
(* end hide *)

Lemma last_drop :
  forall (A : Type) (l : list A) (n : nat),
    last (drop n l) = if leb (S n) (length l) then last l else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct t; reflexivity.
Qed.
(* end hide *)

Lemma tail_drop :
  forall (A : Type) (l : list A) (n : nat),
    tail (drop n l) =
    if leb (S n) (length l) then Some (drop (S n) l) else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      rewrite drop_0. reflexivity.
      rewrite IHt. destruct t; reflexivity.
Qed.
(* end hide *)

Lemma init_drop :
  forall (A : Type) (l : list A) (n : nat),
    init (drop n l) =
    if n <? length l
    then
      match init l with
          | None => None
          | Some l' => Some (drop n l')
      end
    else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      destruct (init t); rewrite drop_0; reflexivity.
      rewrite IHt. destruct t; cbn.
        reflexivity.
        destruct (n' <=? length t).
          destruct (init t); cbn.
            all: reflexivity.
Qed.
(* end hide *)

Lemma nth_drop :
  forall (A : Type) (l : list A) (n m : nat),
    nth m (drop n l) = nth (n + m) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite ?nth_nil. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma nth_spec_Some :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> l = take n l ++ x :: drop (S n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      rewrite drop_0. inv H. reflexivity.
      rewrite (IHt _ _ H) at 1. reflexivity.
Qed.
(* end hide *)

Lemma nth_spec :
  forall (A : Type) (l : list A) (n : nat),
    match nth n l with
        | None => length l <= n
        | Some x => l = take n l ++ x :: drop (S n) l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      rewrite drop_0. reflexivity.
      destruct (nth n' t) eqn: Heq.
        specialize (IHt n'). rewrite Heq in IHt. rewrite IHt at 1.
          reflexivity.
        apply le_n_S. specialize (IHt n'). rewrite Heq in IHt. apply IHt.
Qed.
(* end hide *)

Lemma drop_drop :
  forall (A : Type) (l : list A) (n m : nat),
    drop m (drop n l) = drop (n + m) l.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n, m; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma drop_not_so_interesting :
  forall (A : Type) (l1 l2 : list A),
    (forall n : nat, drop n l1 = drop n l2) -> l1 = l2.
(* begin hide *)
Proof.
  intros.
    specialize (H 0). rewrite ?drop_0 in H. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: zip, unzip, zipWith, intersperse *)
(* end hide *)

(** *** Dualność [take] i [drop] *)

(* begin hide *)
Lemma take_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    take n l = rev (drop (length (rev l) - n) (rev l)).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite <- minus_n_O. rewrite drop_length. cbn. reflexivity.
      rewrite IHt, length_app, plus_comm. cbn. rewrite drop_app_l.
        rewrite rev_app. cbn. reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma take_rev :
  forall (A : Type) (l : list A) (n : nat),
    take n (rev l) = rev (drop (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma rev_take :
  forall (A : Type) (l : list A) (n : nat),
    rev (take n l) = drop (length l - n) (rev l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_inv, length_rev. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma drop_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    drop n l = rev (take (length (rev l) - n) (rev l)).
Proof.
  (* TODO: drop_rev_aux za pomocą [rewrite]'a *)
  intros. rewrite take_rev_aux, ?rev_inv, length_rev.
Restart.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite <- minus_n_O, take_length, rev_app, rev_inv. cbn. reflexivity.
      rewrite IHt, length_app, plus_comm. cbn. rewrite take_app_l.
        reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma drop_rev :
  forall (A : Type) (n : nat) (l : list A),
    drop n (rev l) = rev (take (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite drop_rev_aux, !rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma take_drop :
  forall (A : Type) (l : list A) (n m : nat),
    take m (drop n l) = drop n (take (n + m) l).
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n, m; cbn;
  rewrite ?IHt, ?take_0; reflexivity.
Qed.
(* end hide *)

Lemma drop_take :
  forall (A : Type) (l : list A) (n m : nat),
    drop m (take n l) = take (n - m) (drop m l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n, m; cbn; rewrite ?take_0; trivial.
Qed.
(* end hide *)

Lemma app_take_drop :
  forall (A : Type) (l : list A) (n : nat),
    take n l ++ drop n l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n'];
  cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

(** ** [cycle] *)

(** Zdefiniuj funkcję [cycle : forall A : Type, nat -> list A -> list A],
    która obraca listę cyklicznie. Udowodnij jej właściwości. *)

(* begin hide *)
Fixpoint cycle {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => l
    | S n', [] => []
    | S n', h :: t => cycle n' (snoc h t)
end.
(* end hide *)

Compute cycle 3 [1; 2; 3; 4; 5].
(* ===> [4; 5; 1; 2; 3] : list nat *)

Compute cycle 6 [1; 2; 3; 4; 5].
(* ===> [2; 3; 4; 5; 1] : list nat *)

Lemma cycle_0 :
  forall (A : Type) (l : list A),
    cycle 0 l = l.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma cycle_nil :
  forall (A : Type) (n : nat),
    @cycle A n [] = [].
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_cycle :
  forall (A : Type) (n : nat) (l : list A),
    isEmpty (cycle n l) = isEmpty l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn', isEmpty_snoc. reflexivity.
Qed.
(* end hide *)

Lemma length_cycle :
  forall (A : Type) (n : nat) (l : list A),
    length (cycle n l) = length l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn', length_snoc. reflexivity.
Qed.
(* end hide *)

Lemma cycle_length_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    cycle (length l1 + n) (l1 ++ l2) = cycle n (l2 ++ l1).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    rewrite snoc_app, IHt, app_snoc_l. reflexivity.
Qed.
(* end hide *)

Lemma cycle_length :
  forall (A : Type) (x : A) (l : list A),
    cycle (length l) l = l.
(* begin hide *)
Proof.
  intros.
  rewrite (plus_n_O (length l)).
  rewrite <- (app_nil_r _ l) at 2.
  rewrite cycle_length_app.
  cbn. reflexivity.
Qed.
(* end hide *)

Lemma cycle_plus_length :
  forall (A : Type) (n : nat) (l : list A),
    cycle (length l + n) l = cycle n l.
(* begin hide *)
Proof.
  intros.
  rewrite <- (app_nil_r _ l) at 2.
  rewrite cycle_length_app.
  cbn. reflexivity.
Qed.
(* end hide *)

(** Łamigłówka: jaki jest związek [cycle] ze [snoc], i [rev]? *)

Compute cycle 2 [1; 2; 3; 4; 5; 6].
Compute rev (cycle 4 (rev [1; 2; 3; 4; 5; 6])).

Lemma cycle_map :
  forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
    cycle n (map f l) = map f (cycle n l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite <- IHn', map_snoc. reflexivity.
Qed.
(* end hide *)

(** A z [join] i [bind]? *)

Lemma cycle_replicate :
  forall (A : Type) (n m : nat) (x : A),
    cycle m (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction m as [| m']; cbn.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      intro. cbn in IHm'. rewrite <- IHm'. f_equal.
        rewrite snoc_replicate. cbn. reflexivity.
Qed.
(* end hide *)

Lemma cycle_cycle :
  forall (A : Type) (n m : nat) (l : list A),
    cycle n (cycle m l) = cycle (m + n) l.
(* begin hide *)
Proof.
  induction m as [| m']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn.
      rewrite cycle_nil. reflexivity.
      rewrite IHm'. reflexivity.
Qed.
(* end hide *)

(** ** [splitAt] *)

(** Zdefiniuj funkcję [splitAt], która spełnia poniższą specyfikację.
    Nie używaj take ani drop - użyj rekursji.

    Przykład:
*)

(** [splitAt 2 [1; 2; 3; 4; 5]] = [Some ([1; 2], 3, [4; 5])] *)

(* begin hide *)
Fixpoint splitAt
  {A : Type} (n : nat) (l : list A) {struct l}
  : option (list A * A * list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some ([], h, t)
    | h :: t, S n' =>
        match splitAt n' t with
            | None => None
            | Some (l1, x, l2) => Some (h :: l1, x, l2)
        end
end.
(* end hide *)

Lemma splitAt_spec :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
        | None => length l <= n
        | Some (l1, x, l2) => l = l1 ++ x :: l2
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      reflexivity.
      specialize (IHt n'). destruct (splitAt n' t).
        destruct p, p. cbn. rewrite <- IHt. reflexivity.
        apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma splitAt_spec' :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      l1 = take n l /\ l2 = drop (S n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 2.
    destruct n as [| n']; cbn.
      inversion 1; subst. rewrite drop_0. split; reflexivity.
      destruct (splitAt n' t) eqn: Heq; intros.
        destruct p, p. inversion H; subst; clear H.
          destruct (IHt _ _ _ _ Heq). rewrite H, H0.
            cbn. split; reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma splitAt_megaspec :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
        | None => length l <= n
        | Some (l1, x, l2) =>
            nth n l = Some x /\
            l1 = take n l /\
            l2 = drop (S n) l /\
            l = l1 ++ x :: l2
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      repeat split. rewrite drop_0. reflexivity.
      destruct (splitAt n' t) eqn: Heq.
        destruct p, p. specialize (IHt n'). rewrite Heq in IHt.
          decompose [and] IHt; clear IHt. subst. repeat split.
            assumption.
            rewrite H3 at 1. reflexivity.
        specialize (IHt n'). rewrite Heq in IHt. apply le_n_S, IHt.
Qed.
(* end hide *)

Lemma splitAt_isEmpty_true :
  forall (A : Type) (l : list A),
    isEmpty l = true -> forall n : nat, splitAt n l = None.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_splitAt_false :
  forall (A : Type) (l : list A) (n : nat),
    splitAt n l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma splitAt_length_inv :
  forall (A : Type) (l : list A) (n : nat),
    splitAt n l <> None <-> n < length l.
(* begin hide *)
Proof.
  split; revert n.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct n as [| n'].
        apply le_n_S, le_0_n.
        apply lt_n_S, IHt. destruct (splitAt n' t); congruence.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inversion 1.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. congruence.
          intro. apply (IHt _ (lt_S_n _ _ H)). assumption.
Qed.
(* end hide *)

Lemma splitAt_Some_length :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) -> n < length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      apply Nat.lt_0_succ.
      destruct (splitAt n' t) eqn: Heq.
        destruct p, p. inversion H; subst; clear H.
          apply lt_n_S, (IHt _ _ _ _ Heq).
        inversion H.
Qed.
(* end hide *)

(* begin hide *)
(* TODO *) (*Lemma splitAt_length_inv :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
        | None => length l <= n
        | Some _ => n < length l
    end.
Proof.*)
(* end hide *)

Lemma splitAt_length_lt :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A,
      splitAt n l = Some (take n l, x, drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inv H.
    destruct n as [| n']; cbn.
      exists h. rewrite drop_0. reflexivity.
      apply lt_S_n in H. destruct (IHt _ H) as [x IH].
        exists x. rewrite IH. cbn. reflexivity.
Qed.
(* end hide *)

Lemma splitAt_length_ge :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> splitAt n l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      inversion H.
      apply le_S_n in H. rewrite (IHt _ H). reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO Lemma splitAt_length :
  forall (A : Type) (l : list A) (n : nat),
    splitAt n l =
    if n <? length l
    then
*)
(* end hide *)

Lemma splitAt_snoc :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    splitAt n (snoc x l) =
    if n <? length l
    then
      match splitAt n l with
          | None => None
          | Some (b, y, e) => Some (b, y, snoc x e)
      end
    else
      if beq_nat n (length l)
      then Some (l, x, [])
      else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. unfold ltb. destruct (length t); cbn.
        destruct n'; reflexivity.
        destruct (n' <=? n).
          destruct (splitAt n' t).
            destruct p, p. 1-2: reflexivity.
            destruct (n' =? S n); reflexivity.
Qed.
(* end hide *)

Lemma splitAt_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    splitAt n (l1 ++ l2) =
    match splitAt n l1 with
        | Some (l11, x, l12) => Some (l11, x, l12 ++ l2)
        | None =>
            match splitAt (n - length l1) l2 with
                | Some (l21, x, l22) => Some (l1 ++ l21, x, l22)
                | None => None
            end
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (splitAt n l2).
      destruct p, p. 1-2: reflexivity.
    destruct n as [| n'].
      reflexivity.
      rewrite IHt. destruct (splitAt n' t).
        destruct p, p. reflexivity.
        cbn. destruct (splitAt (n' - length t) l2).
          destruct p, p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma splitAt_app_lt :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n < length l1 ->
      splitAt n (l1 ++ l2) =
      match splitAt n l1 with
          | None => None
          | Some (x, l11, l12) => Some (x, l11, l12 ++ l2)
      end.
(* begin hide *)
Proof.
  intros. rewrite splitAt_app.
  destruct (splitAt_length_lt _ l1 n H).
  rewrite H0. reflexivity.
Qed.
(* end hide *)

Lemma splitAt_app_ge :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 <= n ->
      splitAt n (l1 ++ l2) =
      match splitAt (n - length l1) l2 with
          | None => None
          | Some (l21, x, l22) => Some (l1 ++ l21, x, l22)
      end.
(* begin hide *)
Proof.
  intros. rewrite splitAt_app, splitAt_length_ge.
    destruct (splitAt (n - length l1) l2).
      destruct p, p. 1-2: reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma splitAt_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      splitAt n l =
      match splitAt (length l - S n) (rev l) with
          | None => None
          | Some (l1, x, l2) => Some (rev l2, x, rev l1)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite splitAt_app, splitAt_length_ge.
        1-2: rewrite length_rev, <- minus_n_O.
          cbn. rewrite minus_diag, rev_app, rev_inv. cbn. reflexivity.
        reflexivity.
      rewrite IHt, splitAt_app; clear IHt.
        destruct (splitAt (length t - S n') (rev t)) eqn: Heq.
          destruct p, p. rewrite rev_app. cbn. reflexivity.
          destruct t; cbn in *.
            lia.
            destruct
              (splitAt_length_lt A (rev t ++ [a]) (length t - n'))
            as [x H'].
              rewrite length_app, length_rev. cbn. lia.
              congruence.
        apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma splitAt_rev :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      splitAt n (rev l) =
      match splitAt (length l - S n) l with
          | None => None
          | Some (l1, x, l2) => Some (rev l2, x, rev l1)
      end.
(* begin hide *)
Proof.
  intros. rewrite <- length_rev in H.
  rewrite (splitAt_rev_aux _ _ _ H).
  rewrite length_rev, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma splitAt_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    splitAt n (map f l) =
    match splitAt n l with
        | None => None
        | Some (l1, x, l2) => Some (map f l1, f x, map f l2)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (splitAt n' t).
        destruct p, p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma splitAt_replicate :
  forall (A : Type) (n m : nat) (x : A),
    splitAt m (replicate n x) =
      if m <? n
      then Some (replicate m x, x, replicate (n - S m) x)
      else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. unfold ltb. destruct n' as [| n'']; cbn.
        reflexivity.
        destruct (m' <=? n''); reflexivity.
Qed.
(* end hide *)

Lemma splitAt_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    splitAt m (iterate f n x) =
    if m <? n
    then Some (iterate f m x, iter f m x, iterate f (n - S m) (iter f (S m) x))
    else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. unfold ltb. destruct n' as [| n'']; cbn.
        reflexivity.
        destruct (m' <=? n''); reflexivity.
Qed.
(* end hide *)

Lemma splitAt_head_l :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      head l1 =
      match n with
          | 0 => None
          | _ => head l
      end.
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  rewrite H, ?H0. rewrite head_take. destruct n; reflexivity.
Qed.
(* end hide *)

Lemma splitAt_head_r :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      head l2 = nth (S n) l.
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  rewrite H0. rewrite head_drop. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: tail, uncons *)
(* end hide *)

Lemma splitAt_last_l :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      last l1 =
      match n with
          | 0 => None
          | S n' => nth n' l
      end.
(* begin hide *)
Proof.
  intros. pose (H' := H). apply splitAt_spec' in H'. destruct H'.
  rewrite H0. destruct n.
    rewrite take_0. reflexivity.
    rewrite last_take. apply splitAt_Some_length in H.
    rewrite Min.min_r.
      reflexivity.
      lia.
Qed.
(* end hide *)

Lemma splitAt_last_r :
  forall (A : Type) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n l = Some (l1, x, l2) ->
      last l2 =
      if length l <=? S n
      then None
      else last l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct l2; reflexivity.
      destruct (splitAt n' t) eqn: Heq.
        destruct p, p. inv H. apply (IHt _ _ _ _ Heq).
        inv H.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: splitAt vs init, unsnoc *)
(* end hide *)

Lemma take_splitAt :
  forall (A : Type) (l l1 l2 : list A) (n m : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      take m l1 = take (min n m) l.
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  rewrite H, take_take. reflexivity.
Qed.
(* end hide *)

Lemma take_splitAt' :
  forall (A : Type) (l l1 l2 : list A) (n m : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      take m l2 = take m (drop (S n) l).
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H.
  destruct H. subst. reflexivity.
Qed.
(* end hide *)

Lemma drop_splitAt_l :
  forall (A : Type) (l l1 l2 : list A) (n m : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      drop m l1 = take (n - m) (drop m l).
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  subst. rewrite drop_take. reflexivity.
Qed.
(* end hide *)

Lemma drop_splitAt_r :
  forall (A : Type) (l l1 l2 : list A) (n m : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      drop m l2 = drop (S n + m) l.
(* begin hide *)
Proof.
  intros. apply splitAt_spec' in H. destruct H.
  subst. rewrite drop_drop. reflexivity.
Qed.
(* end hide *)

(** ** [insert] *)

(** Zdefiniuj funkcję [insert], która wstawia do listy [l] na [n]-tą pozycję
    element [x].

    Przykład:
*)

(** [insert [1; 2; 3; 4; 5] 2 42] = [[1; 2; 42; 3; 4; 5]] *)

(* begin hide *)
Fixpoint insert
  {A : Type} (l : list A) (n : nat) (x : A) : list A :=
match l, n with
    | [], _ => [x]
    | _, 0 => x :: l
    | h :: t, S n' => h :: insert t n' x
end.
(* end hide *)

Lemma insert_0 :
  forall (A : Type) (l : list A) (x : A),
    insert l 0 x = x :: l.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    isEmpty (insert l n x) = false.
(* begin hide *)
Proof.
  destruct l, n; reflexivity.
Qed.
(* end hide *)

Lemma length_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    length (insert l n x) = S (length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma insert_length :
  forall (A : Type) (l : list A) (x : A),
    insert l (length l) x = snoc x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma insert_snoc :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    insert (snoc x l) n y =
    if n <=? length l then snoc x (insert l n y) else snoc y (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (n' <=? length t); reflexivity.
Qed.
(* end hide *)

Lemma insert_app :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    insert (l1 ++ l2) n x =
    if leb n (length l1)
    then insert l1 n x ++ l2
    else l1 ++ insert l2 (n - length l1) x.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct n, l2; reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?IHt. destruct (n' <=? length t); reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma insert_rev_aux :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    insert l n x = rev (insert (rev l) (length l - n) x).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      replace (S (length t)) with (length (rev t ++ [h])).
        rewrite insert_length, snoc_app, rev_app, rev_snoc, rev_inv.
          cbn. reflexivity.
        rewrite length_app, length_rev, plus_comm. cbn. reflexivity.
      rewrite ?IHt, insert_app, length_rev.
        assert (length t - n' <= length t).
          apply Nat.le_sub_l.
          apply leb_correct in H. rewrite H.
            rewrite rev_app. cbn. reflexivity.
Qed.
(* end hide *)

Lemma insert_rev :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    insert (rev l) n x = rev (insert l (length l - n) x).
(* begin hide *)
Proof.
  intros. rewrite insert_rev_aux. rewrite rev_inv, length_rev.
  reflexivity.
Qed.
(* end hide *)

Lemma rev_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    rev (insert l n x) = insert (rev l) (length l - n) x.
(* begin hide *)
Proof.
  intros. pose (insert_rev _ (rev l)).
  rewrite rev_inv in e.
  rewrite e, rev_inv, length_rev. reflexivity.
Qed.
(* end hide *)

Lemma map_insert :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat) (x : A),
    map f (insert l n x) = insert (map f l) n (f x).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?IHt. reflexivity.
Qed.
(* end hide *)

Lemma insert_join :
  forall (A : Type) (ll : list (list A)) (n : nat) (x : A) (l : list A),
    join (insert ll n [x]) = l ->
      exists m : nat, l = insert (join ll) m x.
(* begin hide *)
Proof.
  induction ll as [| hl tl]; cbn; intros.
    exists 42. rewrite H. reflexivity.
    destruct n as [| n']; cbn in *.
      exists 0. rewrite insert_0. symmetry. assumption.
      edestruct (IHtl n' x (drop (length hl) l)) as (m & IH).
        apply (f_equal (drop (length hl))) in H.
          rewrite drop_app, drop_length, minus_diag, drop_0 in H.
            cbn in H. assumption.
        exists (length hl + m). rewrite <- H, insert_app.
          destruct (Nat.leb_spec (length hl + m) (length hl)).
            assert (m = 0) by lia. subst.
              rewrite drop_app, drop_length, minus_diag, drop_0, insert_0 in IH.
              rewrite plus_0_r, insert_length, app_snoc_l, <- IH. reflexivity.
            rewrite <- H, drop_app, drop_length, minus_diag, drop_0 in IH.
              replace (length hl + m - length hl) with m by lia.
                rewrite <- IH. reflexivity.
Qed.
(* end hide *)

Lemma insert_replicate :
  forall (A : Type) (n m : nat) (x : A),
    insert (replicate n x) m x = replicate (S n) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite ?IHn'. reflexivity.
Qed.
(* end hide *)

Lemma head_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    head (insert l n x) =
    match l, n with
        | [], _ => Some x
        | _, 0 => Some x
        | _, _ => head l
    end.
(* begin hide *)
Proof.
  destruct l, n; reflexivity.
Qed.
(* end hide *)

Lemma tail_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    tail (insert l n x) =
    match l, n with
        | [], _ => Some []
        | _, 0 => Some l
        | h :: t, S n' => Some (insert t n' x)
    end.
(* begin hide *)
Proof.
  destruct l, n; reflexivity.
Qed.
(* end hide *)

Lemma last_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    last (insert l n x) =
    if isEmpty l
    then Some x
    else if leb (S n) (length l) then last l else Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn in *.
      reflexivity.
      specialize (IHt n' x). rewrite ?IHt.
        destruct (insert t n' x) eqn: Heq; cbn in *.
          apply (f_equal isEmpty) in Heq.
            rewrite isEmpty_insert in Heq. inversion Heq.
          destruct t; reflexivity.
Qed.
(* end hide *)

Lemma nth_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n <= length l -> nth n (insert l n x) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; [reflexivity | inversion H].
    destruct n as [| n']; cbn.
      reflexivity.
      apply IHt, le_S_n, H.
Qed.
(* end hide *)

Lemma nth_insert' :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n (insert l n x) =
    if leb n (length l) then Some x else None.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    1-3: reflexivity.
    apply IHt.
Qed.
(* end hide *)

Lemma insert_spec :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    insert l n x = take n l ++ x :: drop n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma insert_take :
  forall (A : Type) (l : list A) (n m : nat) (x : A),
    insert (take n l) m x =
    if leb m n
    then take (S n) (insert l m x)
    else snoc x (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct (m <=? n); reflexivity.
    destruct n as [| n']; cbn.
      destruct m as [| m']; reflexivity.
      destruct m as [| m']; cbn.
        reflexivity.
        destruct (m' <=? n') eqn: Heq.
          f_equal. rewrite IHt, Heq. reflexivity.
          rewrite IHt, Heq. reflexivity.
Qed.
(* end hide *)

Lemma take_S_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    take (S n) (insert l n x) = snoc x (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma take_insert :
  forall (A : Type) (l : list A) (n m : nat) (x : A),
    take m (insert l n x) =
    if m <=? n then take m l else snoc x l.
(* begin hide *)
(* TODO take_insert *)
Proof.
  intros. rewrite insert_spec. rewrite take_app.
  rewrite take_take. rewrite length_take. 
  induction l as [| h t]; cbn; intros.
    destruct m, n; cbn.
      Focus 4.
Abort.
(* end hide *)

Lemma drop_S_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    drop (S n) (insert l n x) = drop n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma insert_drop :
  forall (A : Type) (l : list A) (n m : nat) (x : A),
    insert (drop n l) m x =
    drop (n - 1) (insert l (n + m) x).
(* begin hide *)
Proof.
  intros A l n. revert l.
  induction n as [| n']; cbn; intros.
    rewrite ?drop_0. reflexivity.
    destruct l as [| h t]; cbn.
Admitted.
(* end hide *)

(* begin hide *)
(* TODO: take_remove *)
(* end hide *)

(** ** [replace] *)

(** Zdefiniuj funkcję [replace], która na liście [l] zastępuje element z
    pozycji [n] elementem [x].

    Przykład:
*)

(** [replace [1; 2; 3; 4; 5] 2 42] = [[1; 2; 42; 4; 5]] *)

(* begin hide *)
Fixpoint replace
  {A : Type} (l : list A) (n : nat) (x : A) : option (list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some (x :: t)
    | h :: t, S n' =>
        match replace t n' x with
            | None => None
            | Some l => Some (h :: l)
        end
end.
(* end hide *)

Lemma isEmpty_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      isEmpty l' = isEmpty l.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    inversion H.
    destruct n; cbn in *.
      inversion H. cbn. reflexivity.
      destruct (replace l n x); inversion H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma length_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> length l' = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inversion H. cbn. rewrite (IHt _ _ _ Heq). reflexivity.
        inversion H.
Qed.
(* end hide *)

(* begin hide *)
(*
Lemma replace_length :
  forall (A : Type) (l : list A) (x : A) (n : nat),
    n = length l -> replace l n x = None.
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite H, IHt; reflexivity.
Qed.
*)
(* end hide *)

Lemma replace_length_lt :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      exists l' : list A, replace l n x = Some l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      exists (x :: t). reflexivity.
      destruct (IHt _ x (lt_S_n _ _ H)) as [l' IH].
        exists (h :: l'). rewrite IH. reflexivity.
Qed.
(* end hide *)

Lemma replace_length_ge :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    length l <= n -> replace l n x = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inversion H.
      rewrite (IHt _ _ (le_S_n _ _ H)). reflexivity.
Qed.
(* end hide *)

Lemma replace_snoc_eq :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    n = length l -> replace (snoc x l) n y = Some (snoc y l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite H. reflexivity.
    destruct n as [| n']; cbn.
      inversion H.
      apply eq_add_S in H. rewrite IHt.
        reflexivity.
        assumption.
Qed.
(* end hide *)

Lemma replace_snoc_neq :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    n <> length l ->
      replace (snoc x l) n y =
      match replace l n y with
          | None => None
          | Some l' => Some (snoc x l')
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    contradiction H. 1-3: reflexivity.
    rewrite Nat.succ_inj_wd_neg in H. rewrite (IHt _ _ _ H).
      destruct (replace t n' y); reflexivity.
Qed.
(* end hide *)

Lemma replace_snoc :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    replace (snoc x l) n y =
    if beq_nat n (length l)
    then Some (snoc y l)
    else
      match replace l n y with
          | None => None
          | Some l' => Some (snoc x l')
      end.
(* begin hide *)
Proof.
  intros. destruct (n =? length l) eqn: Heq.
    apply beq_nat_true in Heq. rewrite Heq.
      apply replace_snoc_eq. reflexivity.
    apply beq_nat_false in Heq.
      apply replace_snoc_neq. assumption.
Qed.
(* end hide *)

Lemma replace_app :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    replace (l1 ++ l2) n x =
    match replace l1 n x, replace l2 (n - length l1) x with
        | None, None => None
        | Some l', _ => Some (l' ++ l2)
        | _, Some l' => Some (l1 ++ l')
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (replace l2 n x); reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (replace t n' x); cbn.
        reflexivity.
        destruct (replace l2 (n' - length t) x); reflexivity.
Qed.
(* end hide *)

Lemma replace_spec :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    replace l n x =
    if n <? length l
    then Some (take n l ++ x :: drop (S n) l)
    else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      rewrite drop_0. reflexivity.
      rewrite IHt. destruct (length t); cbn.
        reflexivity.
        destruct (n' <=? n); reflexivity.
Qed.
(* end hide *)

Lemma replace_spec' :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      replace l n x = Some (take n l ++ x :: drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec.
  apply leb_correct in H. unfold ltb. rewrite H. reflexivity.
Qed.
(* end hide *)

Lemma replace_spec'' :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> l' = take n l ++ x :: drop (S n) l.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (n <? length l) eqn: Heq.
    inv H. reflexivity.
    inv H.
Qed.
(* end hide *)

Lemma replace_rev_aux :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      replace l n x =
      match replace (rev l) (length l - S n) x with
          | None => None
          | Some l' => Some (rev l')
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite <- snoc_app_singl, <- minus_n_O, replace_snoc,
        length_rev, <- beq_nat_refl, rev_snoc, rev_inv. reflexivity.
      rewrite replace_app, (IHt _ _ (lt_S_n _ _ H)).
        destruct (replace (rev t) (length t - S n') x) eqn: Heq.
          rewrite rev_app. cbn. reflexivity.
          rewrite replace_spec' in Heq.
            inv Heq.
            rewrite length_rev. unfold lt. lia.
Qed.
(* end hide *)

Definition omap {A B: Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Lemma replace_rev :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      replace (rev l) n x = omap rev (replace l (length l - S n) x).
(* begin hide *)
Proof.
  intros. rewrite (replace_rev_aux _ (rev l));
  rewrite ?rev_inv, length_rev.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma map_replace :
  forall (A B : Type) (f : A -> B) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Some (map f l') = replace (map f l) n (f x).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq.
        rewrite <- (IHt _ _ _ Heq). inv H. cbn. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma replace_join :
  forall (A : Type) (ll : list (list A)) (n : nat) (x : A) (l : list A),
    replace (join ll) n x = Some l ->
      exists n m : nat,
        match nth n ll with
            | None => False
            | Some l' =>
                match replace l' m x with
                    | None => False
                    | Some l'' =>
                        match replace ll n l'' with
                            | None => False
                            | Some ll' => join ll' = l
                        end
                end
        end.
(* begin hide *)
Proof.
  induction ll as [| hl tl]; cbn; intros.
    inv H.
    rewrite replace_app in H. destruct (replace hl n x) eqn: Heq.
      inv H. exists 0. cbn. exists n. rewrite Heq. reflexivity.
      destruct (replace (join tl) (n - length hl) x) eqn: Heq'; inv H.
        destruct (IHtl _ _ _ Heq') as (n' & m & IH).
          exists (S n'), m. cbn. destruct (nth n' tl).
            destruct (replace l m x).
              destruct (replace tl n' l1).
                cbn. rewrite IH. reflexivity.
                contradiction.
              contradiction.
            contradiction.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: replace vs bind *)
(* end hide *)

Lemma replace_replicate :
  forall (A : Type) (l l' : list A) (n m : nat) (x y : A),
    replace (replicate n x) m y =
    if n <=? m
    then None
    else Some (replicate m x ++ y :: replicate (n - S m) x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. destruct (n' <=? m'); reflexivity.
Qed.
(* end hide *)

Lemma replace_iterate :
  forall (A : Type) (f : A -> A) (l : list A) (n m : nat) (x y : A),
    replace (iterate f n x) m y =
    if n <=? m
    then None
    else Some (iterate f m x ++
               y :: iterate f (n - S m) (iter f (S m) x)).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. destruct (n' <=? m'); reflexivity.
Qed.
(* end hide *)

Lemma head_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    replace l n x = Some l' ->
      head l' =
      match n with
          | 0 => Some x
          | _ => head l
      end.
(* begin hide *)
Proof.
  destruct l, n; cbn; intros; inv H.
    cbn. reflexivity.
    destruct (replace l n x); inv H1. cbn. reflexivity.
Qed.
(* end hide *)

Lemma tail_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      tail l' =
      match n with
          | 0 => tail l
          | S n' =>
              match tail l with
                  | None => None
                  | Some t => replace t n' x
              end
      end.
(* begin hide *)
Proof.
  destruct l, n; cbn; intros; inv H.
    cbn. reflexivity.
    destruct (replace l n x); inv H1. cbn. reflexivity.
Qed.
(* end hide *)

Lemma replace_length_aux :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> length l = length l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H.
        cbn. f_equal. apply (IHt _ _ _ Heq).
Qed.
(* end hide *)

(* begin hide *)
(* TODO: replace vs uncons, unsnoc *)
(* end hide *)

Lemma nth_replace :
  forall (A : Type) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' ->
      nth m l' = if n =? m then Some x else nth m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct m as [| m']; reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. destruct m as [| m']; cbn.
          reflexivity.
          apply IHt. assumption.
        inv H.
Qed.
(* end hide *)

Lemma replace_nth_eq :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      l = l' <-> nth n l = Some x.
(* begin hide *)
Proof.
  split; revert l' n x H.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. inv H2. cbn. reflexivity.
        destruct (replace t n' x) eqn: Heq; inv H.
          inv H2. cbn. apply (IHt _ _ _ Heq eq_refl).
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n']; cbn in *.
        inv H. inv H0. reflexivity.
        destruct (replace t n' x) eqn: Heq; inv H.
          rewrite (IHt _ _ _ Heq H0). reflexivity.
Qed.
(* end hide *)

Lemma last_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      last l' =
      if n =? length l - 1
      then Some x
      else last l.
(* begin hide *)
Proof.
  intros. rewrite (last_nth A l).
  rewrite <- (nth_replace A l l').
    rewrite last_nth. do 2 f_equal.
      apply replace_length_aux in H. rewrite H. reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma init_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      init l' =
      match init l with
          | None => None
          | Some i => if length i <=? n then Some i else replace i n x
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. destruct t; cbn.
        reflexivity.
        destruct (init t); reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H.
        specialize (IHt _ _ _ Heq). destruct (init t) eqn: Heq'; cbn.
          rewrite IHt. destruct (_ <=? _).
            reflexivity.
            destruct (replace l0 n' x) eqn: Heq''.
              reflexivity.
              destruct l; cbn in *.
                destruct t; cbn in *.
                  inv Heq.
                  destruct n'.
                    inv Heq.
                    destruct (replace t n' x); inv Heq.
                destruct (init l); inv IHt.
          rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma take_replace :
  forall (A : Type) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' ->
      take m l' =
      if m <=? n
      then take m l
      else take n l ++ x :: take (m - S n) (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct m; cbn.
        reflexivity.
        rewrite <- minus_n_O, drop_0. reflexivity.
      destruct m as [| m']; cbn.
        rewrite take_0. reflexivity.
        destruct (replace t n' x) eqn: Heq; inv H.
          cbn. rewrite (IHt _ _ _ _ Heq). destruct (m' <=? n'); reflexivity.
Qed.
(* end hide *)

Lemma drop_replace :
  forall (A : Type) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' ->
      drop m l' =
      if n <? m
      then drop m l
      else take (n - m) (drop m l) ++ x :: drop (S n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct m as [| m']; cbn.
        rewrite drop_0. reflexivity.
        reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H.
        destruct m as [| m']; cbn.
          specialize (IHt _ n' 0 _ Heq). cbn in IHt.
            rewrite ?drop_0 in IHt. rewrite IHt, <- minus_n_O. reflexivity.
          rewrite (IHt _ _ _ _ Heq). destruct m' as [| m']; cbn.
            reflexivity.
            destruct (n' <=? m'); cbn; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: replace vs w drugą stronę dla [take] i [drop], splitAt *)
(* end hide *)

Lemma replace_insert :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    n <= length l ->
      replace (insert l n x) n y = Some (insert l n y).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt.
        reflexivity.
        apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma replace_plus :
  forall (A : Type) (l : list A) (n m : nat) (x : A),
    replace l (n + m) x =
    match replace (drop n l) m x with
        | None => None
        | Some l' => Some (take n l ++ l')
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      destruct m as [| m'].
        reflexivity.
        destruct (replace t m' x); reflexivity.
      rewrite IHt. destruct (replace (drop n' t) m x); reflexivity.
Qed.
(* end hide *)

(** ** [remove] *)

(** Zdefiniuj funkcję [remove], która bierze liczbę naturalną [n] oraz listę
    [l] i zwraca parę składającą się z [n]-tego elementu listy [l] oraz
    tego, co pozostanie na liście po jego usunięciu. Jeżeli lista jest za
    krótka, funkcja ma zwracać [None].

    Przykład:
*)

(** [remove 2 [1; 2; 3; 4; 5]] = [Some (3, [1; 2; 4; 5])] *)

(** [remove 42 [1; 2; 3; 4; 5]] = [None] *)

(** Uwaga TODO: w ćwiczeniach jest burdel. *)

(* begin hide *)
Fixpoint remove
  {A : Type} (n : nat) (l : list A) {struct l} : option (A * list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some (h, t)
    | h :: t, S n' =>
        match remove n' t with
            | None => None
            | Some (x, l') => Some (x, h :: l')
        end
end.

Definition remove'
  {A : Type} (n : nat) (l : list A) : list A :=
match remove n l with
    | None => l
    | Some (_, l') => l'
end.

Definition remove''
  {A : Type} (n : nat) (l : list A) : option (list A) :=
match remove n l with
    | None => None
    | Some (_, l') => Some l'
end.
(* end hide *)

Lemma remove'_S_cons :
  forall (A : Type) (n : nat) (h : A) (t : list A),
    remove' (S n) (h :: t) = h :: remove' n t.
(* begin hide *)
Proof.
  intros. unfold remove'. cbn. destruct (remove n t).
    destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_isEmpty_true :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty l = true -> remove n l = None.
(* begin hide *)
Proof.
  destruct l.
    reflexivity.
    inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_remove_not_None :
  forall (A : Type) (l : list A) (n : nat),
    remove n l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_remove :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    remove n l = Some (x, l') ->
      isEmpty l' = isEmpty l || ((length l <=? 1) && isZero n).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in H.
      inv H. destruct l'; reflexivity.
      destruct (remove n' t) eqn: Heq.
        destruct p. inv H. cbn. rewrite Bool.andb_false_r. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma length_remove :
  forall (A : Type) (h : A) (l t : list A) (n : nat),
    remove n l = Some (h, t) -> length l = S (length t).
(* begin hide *)
Proof.
  induction l as [| h' t']; cbn; intros.
    inversion H.
    destruct n as [| n'].
      inversion H; subst. reflexivity.
      destruct (remove n' t') eqn: Heq.
        destruct p. inversion H; subst. cbn.
          rewrite (IHt' _ _ Heq). reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma remove_length_lt :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      nth n l =
      match remove n l with
          | None => None
          | Some (h, _) => Some h
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      reflexivity.
      rewrite (IHt _ (lt_S_n _ _ H)). destruct (remove n' t).
        destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_length_lt' :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> remove n l <> None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inversion 1.
      destruct (remove n' t) eqn: Heq.
        destruct p. inversion 1.
        specialize (IHt _ (lt_S_n _ _ H)). contradiction.
Qed.
(* end hide *)

Lemma remove_length_ge :
  forall (A : Type) (l : list A) (n : nat),
    length l <= n -> remove n l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inversion H.
      apply le_S_n in H. rewrite (IHt _ H). reflexivity.
Qed.
(* end hide *)

Lemma remove_length_snoc :
  forall (A : Type) (x : A) (l : list A),
    remove (length l) (snoc x l) = Some (x, l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma remove_snoc_lt :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l ->
      remove n (snoc x l) =
      match remove n l with
          | None => None
          | Some (h, t) => Some (h, snoc x t)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n'].
      reflexivity.
      rewrite (IHt _ (lt_S_n _ _ H)). destruct (remove n' t).
        destruct p. cbn. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_app :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    remove n (l1 ++ l2) =
    match remove n l1 with
        | Some (h, t) => Some (h, t ++ l2)
        | None =>
            match remove (n - length l1) l2 with
                | Some (h, t) => Some (h, l1 ++ t)
                | None => None
            end
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (remove n l2).
      destruct p. 1-2: reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (remove n' t).
        destruct p. reflexivity.
        destruct (remove (n' - length t) l2).
          destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_app_lt :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    n < length l1 ->
      remove n (l1 ++ l2) =
      match remove n l1 with
          | None => None
          | Some (h, t) => Some (h, t ++ l2)
      end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n'].
      reflexivity.
      apply lt_S_n in H. rewrite (IHt _ _ H).
        destruct (remove n' t).
          destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove_app_ge :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 <= n ->
      remove n (l1 ++ l2) =
      match remove (n - length l1) l2 with
          | None => None
          | Some (h, t) => Some (h, l1 ++ t)
      end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. destruct (remove n l2).
      destruct p. 1-2: reflexivity.
    destruct n as [| n'].
      inversion H.
      apply le_S_n in H. rewrite (IHt _ _ H).
        destruct (remove (n' - length t) l2) eqn: Heq; cbn; rewrite Heq.
          destruct p. all: reflexivity.
Qed.
(* end hide *)

Lemma remove'_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    n < length l1 ->
      remove' n (l1 ++ l2) = remove' n l1 ++ l2.
(* begin hide *)
Proof.
  intros. unfold remove'. rewrite remove_app_lt.
    destruct (remove n l1).
      destruct p. 1-2: reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma remove_app' :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 <= n ->
      remove' n (l1 ++ l2) = l1 ++ remove' (n - length l1) l2.
(* begin hide *)
Proof.
  intros. unfold remove'. rewrite remove_app_ge.
    destruct (remove (n - length l1) l2).
      destruct p. 1-2: reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma remove_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      remove n l =
      match remove (length l - S n) (rev l) with
          | None => None
          | Some (h, t) => Some (h, rev t)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      rewrite <- minus_n_O. rewrite remove_app, remove_length_ge.
        rewrite length_rev, minus_diag. cbn. rewrite app_nil_r, rev_inv.
          reflexivity.
        rewrite length_rev. reflexivity.
      rewrite IHt. rewrite remove_app.
        destruct (remove (length t - S n') (rev t)) eqn: Heq.
          destruct p. rewrite rev_app. cbn. reflexivity.
          apply remove_length_lt' in Heq.
            contradiction.
            rewrite length_rev. lia.
        apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma remove_rev :
  forall (A : Type) (l : list A) (n : nat),
    n < length l ->
      remove n (rev l) =
      match remove (length l - S n) l with
          | None => None
          | Some (h, t) => Some (h, rev t)
      end.
(* begin hide *)
Proof.
  intros. rewrite remove_rev_aux, rev_inv; rewrite length_rev.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma remove_map :
  forall (A B : Type) (f : A -> B) (l : list A) (n : nat),
    remove n (map f l) =
    match remove n l with
        | None => None
        | Some (x, l') => Some (f x, map f l')
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      reflexivity.
      rewrite IHt. destruct (remove n' t).
        destruct p. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma remove_replicate :
  forall (A : Type) (n m : nat) (x : A),
    m < n -> remove m (replicate n x) = Some (x, replicate (n - 1) x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct m; inversion H.
    destruct m as [| m'].
      rewrite <- minus_n_O. reflexivity.
      apply lt_S_n in H. rewrite (IHn' _ _ H). destruct n'; cbn.
        destruct m'; inversion H.
        rewrite <- minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma remove_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    m < n ->
      remove m (iterate f n x) =
      Some (iter f m x,
            iterate f m x ++
            (iterate f (n - S m) (iter f (S m) x))).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct m; inversion H.
    destruct m as [| m']; cbn.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'.
        cbn. reflexivity.
        apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma remove_nth_take_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x <->
    remove n l = Some (x, take n l ++ drop (S n) l).
(* begin hide *)
Proof.
  split; revert n x.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n']; cbn in *.
        inv H. rewrite drop_0. reflexivity.
        rewrite (IHt _ _ H). reflexivity.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. reflexivity.
        apply IHt. destruct (remove n' t).
          destruct p. inv H. destruct t; reflexivity.
          inv H.
Qed.
(* end hide *)

Lemma remove_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      remove n (insert l n x) = Some (x, l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt.
        reflexivity.
        apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma remove'_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      remove' n l' = remove' n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      inv H. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. rewrite ?remove'_S_cons. f_equal. apply IHt with x.
          assumption.
          inv H.
Qed.
(* end hide *)

(** ** [zip] *)

(** Zdefiniuj funkcję [zip], która bierze dwie listy i skleja je w listę par.
    Wywnioskuj z poniższej specyfikacji, jak dokładnie ma się zachowywać
    ta funkcja.

    Przykład:
*)

(** [zip [1; 3; 5; 7] [2; 4; 6]] = [[(1, 2); (3, 4); (5, 6)]] *)

(* begin hide *)
Fixpoint zip {A B : Type} (la : list A) (lb : list B) : list (A * B) :=
match la, lb with
    | [], _ => []
    | _, [] => []
    | ha :: ta, hb :: tb => (ha, hb) :: zip ta tb
end.
(* end hide *)

Lemma zip_nil_l :
  forall (A B : Type) (l : list B), zip (@nil A) l = [].
(* begin hide *)
Proof. cbn. trivial. Qed.
(* end hide *)

Lemma zip_nil_r :
  forall (A B : Type) (l : list A), zip l (@nil B) = [].
(* begin hide *)
Proof. destruct l; cbn; trivial. Qed.
(* end hide *)

Lemma isEmpty_zip :
  forall (A B : Type) (la : list A) (lb : list B),
    isEmpty (zip la lb) = orb (isEmpty la) (isEmpty lb).
(* begin hide *)
Proof.
  destruct la, lb; reflexivity.
Qed.
(* end hide *)

Lemma length_zip :
  forall (A B : Type) (la : list A) (lb : list B),
    length (zip la lb) = min (length la) (length lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; intros.
    cbn. trivial.
    destruct lb as [| hb tb]; cbn.
      trivial.
      rewrite IHta. trivial.
Qed.
(* end hide *)

Lemma zip_not_rev :
  exists (A B : Type) (la : list A) (lb : list B),
    zip (rev la) (rev lb) <> rev (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists [true; false; true], [false; true].
  cbn. inversion 1.
Qed.
(* end hide *)

Lemma head_zip :
  forall (A B : Type) (la : list A) (lb : list B) (a : A) (b : B),
    head la = Some a -> head lb = Some b ->
      head (zip la lb) = Some (a, b).
(* begin hide *)
Proof.
  induction la as [| ha ta]; destruct lb as [| hb tb]; cbn; intros;
  inversion H; inversion H0; trivial.
Qed.
(* end hide *)

Lemma tail_zip :
  forall (A B : Type) (la ta : list A) (lb tb : list B),
    tail la = Some ta -> tail lb = Some tb ->
      tail (zip la lb) = Some (zip ta tb).
(* begin hide *)
Proof.
  induction la as [| ha ta']; cbn.
    inversion 1.
    destruct lb as [| hb tb']; cbn.
      inversion 2.
      do 2 inversion 1. trivial.
Qed.
(* end hide *)

Lemma zip_not_app :
  exists (A B : Type) (la la' : list A) (lb lb' : list B),
    zip (la ++ la') (lb ++ lb') <> zip la lb ++ zip la' lb'.
(* begin hide *)
Proof.
  exists bool, bool. exists [true], [false], [true; false; true], [].
  cbn. inversion 1.
Qed.
(* end hide *)

Lemma zip_map :
  forall (A B A' B' : Type) (f : A -> A') (g : B -> B')
  (la : list A) (lb : list B),
    zip (map f la) (map g lb) =
    map (fun x => (f (fst x), g (snd x))) (zip la lb).
(* begin hide *)
Proof.
  induction la; destruct lb; cbn; trivial.
    rewrite IHla. trivial.
Qed.
(* end hide *)

Lemma zip_replicate :
  forall (A B : Type) (n m : nat) (a : A) (b : B),
    zip (replicate n a) (replicate m b) =
    replicate (min n m) (a, b).
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'];
  cbn; intros; rewrite ?IHn'; trivial.
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

Lemma nth_zip :
  forall (A B : Type) (la : list A) (lb : list B) (n : nat),
    nth n (zip la lb) =
    if n <=? min (length la) (length lb)
    then
      match nth n la, nth n lb with
          | Some a, Some b => Some (a, b)
          | _, _ => None
      end
    else None.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    destruct n; reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n; reflexivity.
      destruct n as [| n']; cbn.
        reflexivity.
        apply IHta.
Qed.
(* end hide *)

Lemma nth_zip' :
  forall (A B : Type) (la : list A) (lb : list B) (n : nat),
    nth n (zip la lb) =
    match nth n la, nth n lb with
        | Some a, Some b => Some (a, b)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb], n as [| n']; cbn.
      reflexivity.
      destruct (nth n' ta); reflexivity.
      reflexivity.
      apply IHta.
Qed.
(* end hide *)

Lemma zip_take :
  forall (A B : Type) (la : list A) (lb : list B) (n : nat),
    zip (take n la) (take n lb) = take n (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      rewrite zip_nil_r. reflexivity.
      destruct n as [| n']; cbn.
        reflexivity.
        rewrite IHta. reflexivity.
Qed.
(* end hide *)

Lemma zip_drop :
  forall (A B : Type) (la: list A) (lb : list B) (n : nat),
    zip (drop n la) (drop n lb) = drop n (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      rewrite zip_nil_r. reflexivity.
      destruct n as [| n']; cbn.
        reflexivity.
        apply IHta.
Qed.
(* end hide *)

Lemma splitAt_zip :
  forall (A B : Type) (la : list A) (lb : list B) (n : nat),
    splitAt n (zip la lb) =
    match splitAt n la, splitAt n lb with
        | Some (la1, a, la2), Some (lb1, b, lb2) =>
            Some (zip la1 lb1, (a, b), zip la2 lb2)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  intros. assert (H := splitAt_megaspec A la n). destruct (splitAt n la).
    Focus 2. apply splitAt_length_ge. rewrite length_zip.
      apply Nat.min_case_strong; intros.
        assumption.
        apply le_trans with (length la); assumption.
    destruct p, p. decompose [and] H; clear H; subst.
      assert (H := splitAt_megaspec B lb n). destruct (splitAt n lb).
        Focus 2. apply splitAt_length_ge. rewrite length_zip.
          apply Nat.min_case_strong; intros.
            apply le_trans with (length lb); assumption.
            assumption.
        destruct p, p. decompose [and] H; clear H; subst.
          rewrite H4, H6.
Restart.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (splitAt n' ta).
          destruct p, p. 1-2: reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (splitAt n' ta), (splitAt n' tb).
          destruct p, p, p0, p. cbn. reflexivity.
          destruct p, p. 1-3: reflexivity.
Qed.
(* end hide *)

Lemma insert_zip :
  forall (A B : Type) (la : list A) (lb : list B) (a : A) (b : B) (n : nat),
    insert (zip la lb) n (a, b) =
    if n <=? min (length la) (length lb)
    then zip (insert la n a) (insert lb n b)
    else snoc (a, b) (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    destruct n; cbn.
      rewrite insert_0. reflexivity.
      reflexivity.
    destruct lb as [| hb tb]; cbn; intros.
      destruct n; reflexivity.
      destruct n as [| n']; cbn.
        reflexivity.
        rewrite IHta. destruct (n' <=? min (length ta) (length tb)).
          1-2: reflexivity.
Qed.
(* end hide *)

Lemma replace_zip :
  forall
    (A B : Type) (la la' : list A) (lb lb' : list B)
    (n : nat) (a : A) (b : B),
      replace la n a = Some la' ->
      replace lb n b = Some lb' ->
        replace (zip la lb) n (a, b) = Some (zip la' lb').
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct lb; inv H0. cbn. reflexivity.
      destruct (replace ta n' a) eqn: Heqa; inv H.
        destruct lb as [| hb tb]; cbn in *.
          inv H0.
          destruct (replace tb n' b) eqn: Heqb; inv H0.
            rewrite (IHta _ _ _ _ _ _ Heqa Heqb). reflexivity.
Qed.
(* end hide *)

Lemma replace_zip' :
  forall
    (A B : Type) (la  : list A) (lb : list B) (n : nat) (a : A) (b : B),
      replace (zip la lb) n (a, b) =
      match replace la n a, replace lb n b with
          | Some la', Some lb' => Some (zip la' lb')
          | _, _ => None
      end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb], n as [| n']; cbn.
      reflexivity.
      destruct (replace ta n' a); reflexivity.
      reflexivity.
      rewrite IHta. destruct (replace ta n' a).
        destruct (replace tb n' b); cbn.
          1-3: reflexivity.
Qed.
(* end hide *)

Lemma remove_zip :
  forall (A B : Type) (la : list A) (lb : list B) (n : nat),
    remove n (zip la lb) =
    match remove n la, remove n lb with
        | Some (a, la'), Some (b, lb') => Some ((a, b), zip la' lb')
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (remove n' ta); try destruct p; reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (remove n' ta), (remove n' tb);
          try destruct p; try destruct p0; cbn; reflexivity.
Qed.
(* end hide *)

(** ** [unzip] *)

(** Zdefiniuj funkcję [unzip], która rozdziela listę par na dwie listy:
    lewa lista zawiera lewe komponenty par, a prawa lista - prawe
    komponenty par.

    Przykład:
*)

(** [unzip [(1, 2); (3, 4); (5, 6)]] = [([1; 3; 5], [2; 4; 6])] *)

(* begin hide *)
Fixpoint unzip {A B : Type} (l : list (A * B)) : list A * list B :=
match l with
    | [] => ([], [])
    | (ha, hb) :: t =>
        let (ta, tb) := unzip t in (ha :: ta, hb :: tb)
end.
(* end hide *)

Lemma zip_unzip :
  forall (A B : Type) (l : list (A * B)),
    zip (fst (unzip l)) (snd (unzip l)) = l.
(* begin hide *)
Proof.
  induction l as [| [ha hb] t]; cbn.
    trivial.
    destruct (unzip t). cbn in *. rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma unzip_zip :
  exists (A B : Type) (la : list A) (lb : list B),
    unzip (zip la lb) <> (la, lb).
(* begin hide *)
Proof.
  exists unit, unit, [], [tt]. cbn. inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_unzip :
  forall (A B : Type) (l : list (A * B)) (la : list A) (lb : list B),
    unzip l = (la, lb) -> isEmpty l = orb (isEmpty la) (isEmpty lb).
(* begin hide *)
Proof.
  destruct l as [| [ha hb] t]; cbn; intros.
    inversion H; subst. cbn. reflexivity.
    destruct (unzip t). inversion H; subst. cbn. reflexivity.
Qed.
(* end hide *)

Lemma unzip_snoc :
  forall (A B : Type) (x : A * B) (l : list (A * B)),
    unzip (snoc x l) =
      let (la, lb) := unzip l in (snoc (fst x) la, snoc (snd x) lb).
(* begin hide *)
Proof.
  induction l as [| [ha hb] t]; cbn; intros.
    destruct x. cbn. reflexivity.
    destruct (unzip t). rewrite IHt. cbn. reflexivity.
Qed.
(* end hide *)

(** ** [zipWith] *)

(** Zdefiniuj funkcję [zipWith], która zachowuje się jak połączenie [zip]
    i [map]. Nie używaj [zip] ani [map] - użyj rekursji.

    Przykład:
*)

(** [zipWith plus [1; 2; 3] [4; 5; 6]] = [[5; 7; 9]] *)

(* begin hide *)
Fixpoint zipWith {A B C : Type} (f : A -> B -> C)
  (la : list A) (lb : list B) : list C :=
match la, lb with
    | [], _ => []
    | _, [] => []
    | ha :: ta, hb :: tb => f ha hb :: zipWith f ta tb
end.
(* end hide *)

Lemma zipWith_spec :
  forall (A B C : Type) (f : A -> B -> C)
  (la : list A) (lb : list B),
    zipWith f la lb =
    map (fun '(a, b) => f a b) (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; destruct lb as [| hb tb];
  cbn; intros; rewrite ?IHta; reflexivity.
Qed.
(* end hide *)

Lemma zipWith_pair :
  forall (A B : Type) (la : list A) (lb : list B),
    zipWith pair la lb = zip la lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn; intros.
      reflexivity.
      rewrite IHta. reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_zipWith :
  forall (A B C : Type) (f : A -> B -> C) (la : list A) (lb : list B),
    isEmpty (zipWith f la lb) = orb (isEmpty la) (isEmpty lb).
(* begin hide *)
Proof.
  destruct la, lb; reflexivity.
Qed.
(* end hide *)

Lemma zipWith_snoc :
  forall
    (A B C : Type) (f : A -> B -> C)
    (a : A) (b : B) (la : list A) (lb : list B),
      length la = length lb ->
        zipWith f (snoc a la) (snoc b lb) =
        snoc (f a b) (zipWith f la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; destruct lb as [| hb tb]; cbn in *; intros.
    reflexivity.
    all: inversion H. rewrite (IHta _ H1). reflexivity.
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

Lemma take_zipWith :
  forall
    (A B C : Type) (f : A -> B -> C) (la : list A) (lb : list B) (n : nat),
      take n (zipWith f la lb) = zipWith f (take n la) (take n lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    rewrite ?take_nil. cbn. reflexivity.
    destruct lb as [| hb tb]; cbn.
      rewrite ?take_nil, zipWith_spec, zip_nil_r. cbn. reflexivity.
      destruct n as [| n']; cbn.
        reflexivity.
        rewrite IHta. reflexivity.
Qed.
(* end hide *)

Lemma drop_zipWith :
  forall
    (A B C : Type) (f : A -> B -> C) (la : list A) (lb : list B) (n : nat),
      drop n (zipWith f la lb) = zipWith f (drop n la) (drop n lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    rewrite ?drop_nil. cbn. reflexivity.
    destruct lb as [| hb tb]; cbn.
      rewrite ?drop_nil, zipWith_spec, zip_nil_r. cbn. reflexivity.
      destruct n as [| n']; cbn.
        reflexivity.
        rewrite IHta. reflexivity.
Qed.
(* end hide *)

Lemma splitAt_zipWith :
  forall (A B C : Type) (f : A -> B -> C)
    (la : list A) (lb : list B) (n : nat),
      splitAt n (zipWith f la lb) =
      match splitAt n la, splitAt n lb with
          | Some (la1, a, la2), Some (lb1, b, lb2) =>
              Some (zipWith f la1 lb1, f a b, zipWith f la2 lb2)
          | _, _ => None
      end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (splitAt n' ta).
          destruct p, p. 1-2: reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (splitAt n' ta), (splitAt n' tb).
          destruct p, p, p0, p. cbn. reflexivity.
          destruct p, p. 1-3: reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO : zipWith vs insert *)
(* end hide *)

Lemma replace_zipWith :
  forall
    (A B C : Type) (f : A -> B -> C) (la la' : list A) (lb lb' : list B)
    (n : nat) (a : A) (b : B),
      replace la n a = Some la' ->
      replace lb n b = Some lb' ->
        replace (zipWith f la lb) n (f a b) = Some (zipWith f la' lb').
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. destruct lb; inv H0. cbn. reflexivity.
      destruct (replace ta n' a) eqn: Heqa; inv H.
        destruct lb as [| hb tb]; cbn in *.
          inv H0.
          destruct (replace tb n' b) eqn: Heqb; inv H0.
            rewrite (IHta _ _ _ _ _ _ Heqa Heqb). reflexivity.
Qed.
(* end hide *)

Lemma remove_zipWith :
  forall (A B C : Type) (f : A -> B -> C)
    (la : list A) (lb : list B) (n : nat),
      remove n (zipWith f la lb) =
      match remove n la, remove n lb with
          | Some (a, la'), Some (b, lb') =>
              Some (f a b, zipWith f la' lb')
          | _, _ => None
      end.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct n as [| n'].
        reflexivity.
        destruct (remove n' ta); try destruct p; reflexivity.
      destruct n as [| n'].
        reflexivity.
        rewrite IHta. destruct (remove n' ta), (remove n' tb);
          try destruct p; try destruct p0; cbn; reflexivity.
Qed.
(* end hide *)

(** ** [unzipWith] *)

(** Zdefiniuj funkcję [unzipWith], która ma się tak do [zipWith], jak
    [unzip] do [zip]. Oczywiście użyj rekursji i nie używaj żadnych
    funkcji pomocniczych. *)

(* begin hide *)
Fixpoint unzipWith
  {A B C : Type} (f : A -> B * C) (l : list A) : list B * list C :=
match l with
    | [] => ([], [])
    | h :: t =>
        let
          '(l1, l2) := unzipWith f t
        in let
          '(b, c) := f h
        in
          (b :: l1, c :: l2)
end.
(* ende hide *)

Lemma zipWith_unzipWith :
  forall (A B C D : Type) (f : A -> B * C) (g : B -> C -> D)
  (l : list A),
    zipWith g (fst (unzipWith f l)) (snd (unzipWith f l)) =
    map (fun x : A => g (fst (f x)) (snd (f x))) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite <- IHt.
    destruct (unzipWith f t), (f h); cbn. reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_unzipWith :
  forall (A B C : Type) (f : A -> B * C) (l : list A)
  (lb : list B) (lc : list C),
    unzipWith f l = (lb, lc) ->
      isEmpty l = orb (isEmpty lb) (isEmpty lc).
(* begin hide *)
Proof.
  destruct l as [| h t]; inversion 1; cbn.
    reflexivity.
    destruct (unzipWith f t), (f h). inversion H1; subst. cbn. reflexivity.
Qed.
(* end hide *)

Lemma unzipWith_spec :
  forall (A B C : Type) (f : A -> B * C) (l : list A),
    unzipWith f l = unzip (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (unzip (map f t)), (f h). reflexivity.
Qed.
(* end hide *)

Lemma unzipWith_id :
  forall (A B : Type) (l : list (A * B)),
    unzipWith id l = unzip l.
(* begin hide *)
Proof.
  intros. rewrite unzipWith_spec, map_id. reflexivity.
Restart.
  induction l as [| [ha ta] t]; cbn.
    reflexivity.
    rewrite IHt. destruct (unzip t). reflexivity.
Qed.
(* end hide *)

(** * Funkcje z predykatem boolowskim *)

(** ** [any] *)

(** Zdefiniuj funkcję [any], która sprawdza, czy lista [l] zawiera jakiś
    element, który spełnia predykat boolowski [p].

    Przykład:
    [any even [3; 5; 7; 11]] = [false]
*)

(* begin hide *)
Fixpoint any {A : Type} (p : A -> bool) (l : list A) : bool :=
match l with
    | [] => false
    | h :: t => orb (p h) (any p t)
end.
(* end hide *)

Lemma any_isEmpty_true :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty l = true -> any p l = false.
(* begin hide *)
Proof.
  destruct l; cbn.
    reflexivity.
    inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_any_true :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p l = true -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn.
    inversion 1.
    reflexivity.
Qed.
(* end hide *)

Lemma any_length :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p l = true -> 1 <= length l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    inversion 1.
    intro. apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma any_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    any p (snoc x l) = orb (any p l) (p x).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    rewrite Bool.orb_false_r. reflexivity.
    destruct (p h); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma any_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    any p (l1 ++ l2) = orb (any p l1) (any p l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intro.
    reflexivity.
    destruct (p h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma any_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p (rev l) = any p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite any_app, IHt. cbn. rewrite ?Bool.orb_assoc, Bool.orb_comm.
      cbn. rewrite Bool.orb_comm. reflexivity.
Qed.
(* end hide *)

Lemma any_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    any p (map f l) = any (fun x : A => p (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p (f h)); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma any_join :
  forall (A : Type) (p : A -> bool) (l : list (list A)),
    any p (join l) = any (any p) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite any_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma any_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    any p (replicate n x) = andb (leb 1 n) (p x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intro.
    reflexivity.
    destruct (p x) eqn: Hpx; cbn.
      reflexivity.
      destruct n'; cbn in *.
        reflexivity.
        rewrite IHn'. assumption.
Qed.
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

Lemma any_nth :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p l = true <->
    exists (n : nat) (x : A), nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intro.
      inversion H.
      destruct (p h) eqn: Hph; cbn in *.
        exists 0, h. split; [reflexivity | assumption].
        destruct (IHt H) as (n & x & H1 & H2).
          exists (S n), x. split; assumption.
    destruct 1 as (n & x & H1 & H2).
    revert x n H1 H2.
    induction l as [| h t]; cbn; intros.
      inversion H1.
      destruct n as [| n'].
        inversion H1. rewrite H2. cbn. reflexivity.
        rewrite (IHt _ _ H1 H2). rewrite Bool.orb_true_r. reflexivity.
Qed.
(* end hide *)

Lemma any_take :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    any p (take n l) = true -> any p l = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in *.
      inv H.
      destruct (p h); cbn in *.
        reflexivity.
        apply IHt with n'. assumption.
Qed.
(* end hide *)

Lemma any_take_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    any p l = false -> any p (take n l) = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      destruct (p h); cbn in *.
        assumption.
        apply IHt. assumption.
Qed.
(* end hide *)

Lemma any_drop :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    any p (drop n l) = true -> any p l = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in *.
      assumption.
      rewrite (IHt _ H). rewrite Bool.orb_true_r. reflexivity.
Qed.
(* end hide *)

Lemma any_drop_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    any p l = false -> any p (drop n l) = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      assumption.
      apply IHt. destruct (p h); cbn in H.
        inv H.
        assumption.
Qed.
(* end hide *)

Lemma any_cycle :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    any p (cycle n l) = any p l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn', any_snoc. cbn.
        rewrite orb_comm. reflexivity.
Qed.
(* end hide *)

Lemma any_insert :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    any p (insert l n x) = orb (p x) (any p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. destruct (p h), (p x); reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: any vs replace *)
(* end hide *)

Lemma any_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      any p l' = any p (take n l) || p x || any p (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H; cbn in *. rewrite drop_0. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H; cbn.
        rewrite (IHt _ _ _ Heq). rewrite ?Bool.orb_assoc. reflexivity.
Qed.
(* end hide *)

Lemma any_replace' :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      any p l = true -> p x = true -> any p l' = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H; cbn in *. rewrite H1. cbn. reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. cbn. destruct (p h); cbn in *.
          reflexivity.
          apply (IHt _ _ _ Heq H0 H1).
        inv H.
Qed.
(* end hide *)

Lemma any_true :
  forall (A : Type) (l : list A),
    any (fun _ => true) l = negb (isEmpty l).
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; reflexivity.
Qed.
(* end hide *)

Lemma any_false :
  forall (A : Type) (l : list A),
    any (fun _ => false) l = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma any_orb :
  forall (A : Type) (p q : A -> bool) (l : list A),
    any (fun x : A => orb (p x) (q x)) l =
    orb (any p l) (any q l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. destruct (q h); cbn.
      rewrite ?Bool.orb_true_r. cbn. reflexivity.
      rewrite ?Bool.orb_false_r. apply Bool.orb_assoc.
Qed.
(* end hide *)

Lemma any_andb :
  forall (A : Type) (p q : A -> bool) (l : list A),
    any (fun x : A => andb (p x) (q x)) l = true ->
      any p l = true /\ any q l = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h); cbn in *.
      split; trivial. destruct (q h); cbn in *.
        reflexivity.
        destruct (IHt H). assumption.
      destruct (IHt H). rewrite H0, H1. split.
        reflexivity.
        rewrite Bool.orb_true_r. reflexivity.
Qed.
(* end hide *)

(** ** [all] *)

(** Zdefiniuj funkcję [all], która sprawdza, czy wszystkie wartości na liście
    [l] spełniają predykat boolowski [p].

    Przykład:
    [all even [2; 4; 6]] = [true]
*)

(* begin hide *)
Fixpoint all {A : Type} (p : A -> bool) (l : list A) : bool :=
match l with
    | [] => true
    | h :: t => andb (p h) (all p t)
end.
(* end hide *)

Lemma all_isEmpty_true :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty l = true -> all p l = true.
(* begin hide *)
Proof.
  destruct l; cbn.
    reflexivity.
    inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_all_false :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p l = false -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn.
    inversion 1.
    reflexivity.
Qed.
(* end hide *)

Lemma all_length :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p l = false -> 1 <= length l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intro.
    inversion H.
    apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma all_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all p (snoc x l) = andb (all p l) (p x).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    rewrite Bool.andb_true_r. reflexivity.
    destruct (p h); cbn.
      assumption.
      reflexivity.
Qed.
(* end hide *)

Lemma all_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    all p (l1 ++ l2) = andb (all p l1) (all p l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intro.
    reflexivity.
    destruct (p h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma all_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p (rev l) = all p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite all_app, IHt. cbn. rewrite Bool.andb_true_r, Bool.andb_comm.
      reflexivity.
Qed.
(* end hide *)

Lemma all_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    all p (map f l) = all (fun x : A => p (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p (f h)); cbn.
      assumption.
      reflexivity.
Qed.
(* end hide *)

Lemma all_join :
  forall (A : Type) (p : A -> bool) (l : list (list A)),
    all p (join l) = all (all p) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite all_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma all_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    all p (replicate n x) = orb (n <=? 0) (p x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intro.
    reflexivity.
    destruct (p x) eqn: Hpx; cbn.
      destruct n'; cbn in *.
        reflexivity.
        rewrite IHn'. assumption.
      reflexivity.
Qed.
(* end hide *)

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

Lemma all_nth :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p l = true <->
    forall n : nat, n < length l -> exists x : A,
      nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H0.
      destruct (p h) eqn: Hph; cbn in *.
        destruct n as [| n']; cbn.
          exists h. split; [reflexivity | assumption].
          apply lt_S_n in H0. destruct (IHt H _ H0) as (x & H1 & H2).
            exists x. split; assumption.
        congruence.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h) eqn: Hph; cbn in *.
        apply IHt. intros. destruct t as [| h' t'].
          cbn in H0. inversion H0.
          destruct (H 1 ltac:(lia)) as (x & H1 & H2); cbn in *.
            destruct n as [| n']; cbn in *.
              exists h'. inversion H1; subst. split; trivial.
              destruct (H (S (S n')) ltac:(lia)) as (x' & H1' & H2').
                cbn in H1'. exists x'. split; trivial.
        destruct (H 0 ltac:(lia)) as (x & H1 & H2); cbn in *.
          inversion H1; subst. congruence.
Qed.
(* end hide *)

Lemma all_take :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    all p (take n l) = false -> all p l = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in H.
      inv H.
      destruct (p h); cbn in *.
        apply IHt with n'. assumption.
        reflexivity.
Qed.
(* end hide *)

Lemma all_take_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    all p l = true -> all p (take n l) = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      destruct (p h); cbn in *.
        apply (IHt _ H).
        assumption.
Qed.
(* end hide *)

Lemma all_drop :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    all p (drop n l) = false -> all p l = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in *.
      assumption.
      rewrite (IHt _ H), Bool.andb_false_r. reflexivity.
Qed.
(* end hide *)

Lemma all_drop_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    all p l = true -> all p (drop n l) = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      assumption.
      apply IHt. destruct (p h); cbn in H.
        assumption.
        inv H.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: all vs splitAt *)
(* end hide *)

Lemma all_insert :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    all p (insert l n x) = andb (p x) (all p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?IHt. destruct (p h), (p x); reflexivity.
Qed.
(* end hide *)

Lemma all_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      all p l' = all p (take n l) && p x && all p (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H; cbn in *. rewrite drop_0. reflexivity.
      destruct (replace t n' x) eqn: Heq; inv H; cbn.
        rewrite (IHt _ _ _ Heq), ?Bool.andb_assoc. reflexivity.
Restart.
  intros. rewrite replace_spec in H.
  destruct (n <? length l); inv H.
  rewrite all_app. cbn. rewrite Bool.andb_assoc. reflexivity.
Qed.
(* end hide *)

Lemma all_replace' :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      all p l = true -> p x = true -> all p l' = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H; cbn in *. rewrite H1. cbn. destruct (p h); cbn in H0.
        assumption.
        congruence.
      destruct (replace t n' x) eqn: Heq; inv H; cbn.
        destruct (p h); cbn in *.
          apply (IHt _ _ _ Heq H0 H1).
          assumption.
Qed.
(* end hide *)

Lemma all_true :
  forall (A : Type) (l : list A),
    all (fun _ => true) l = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma all_false :
  forall (A : Type) (l : list A),
    all (fun _ => false) l = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; reflexivity.
Qed.
(* end hide *)

Lemma all_orb :
  forall (A : Type) (p q : A -> bool) (l : list A),
    orb (all p l) (all q l) = true ->
    all (fun x : A => orb (p x) (q x)) l = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt.
      rewrite Bool.andb_true_r. destruct (p h), (q h); cbn in *; trivial.
      destruct (p h), (q h); cbn in *.
        assumption.
        rewrite Bool.orb_false_r in H. rewrite H. cbn. reflexivity.
        rewrite H, Bool.orb_true_r. reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma all_andb :
  forall (A : Type) (p q : A -> bool) (l : list A),
    all (fun x : A => andb (p x) (q x)) l =
    andb (all p l) (all q l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h), (q h); cbn in *.
      assumption.
      rewrite Bool.andb_false_r. all: reflexivity.
Qed.
(* end hide *)

Lemma any_all :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p l = negb (all (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma all_any :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p l = negb (any (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      assumption.
      reflexivity.
Qed.
(* end hide *)

Lemma all_cycle :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    all p (cycle n l) = all p l.
(* begin hide *)
Proof.
  intros. rewrite !all_any.
  f_equal. rewrite any_cycle.
  reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_join :
  forall (A : Type) (l : list (list A)),
    isEmpty (join l) = all isEmpty l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite isEmpty_app, IHt. reflexivity.
Qed.
(* end hide *)

(** ** [find]  i [findLast] *)

(** Zdefiniuj funkcję [find], która znajduje pierwszy element na liście,
    który spełnia podany predykat boolowski.

    Przykład:
    [find even [1; 2; 3; 4]] = [Some 2]
*)

(** Zdefiniuj też funkcję [findLast], która znajduje ostatni element na
    liście, który spełnia podany predykat boolowski.

    Przykład:
    [findLast even [1; 2; 3; 4]] = [Some 4]
*)

(* begin hide *)
Function find {A : Type} (p : A -> bool) (l : list A) : option A :=
match l with
    | [] => None
    | h :: t => if p h then Some h else find p t
end.

Fixpoint findLast {A : Type} (p : A -> bool) (l : list A) : option A :=
match l with
    | [] => None
    | h :: t =>
        match findLast p t with
            | None => if p h then Some h else None
            | Some x => Some x
        end
end.
(* end hide *)

Lemma find_false :
  forall (A : Type) (l : list A),
    find (fun _ => false) l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma find_true :
  forall (A : Type) (l : list A),
    find (fun _ => true) l = head l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma find_isEmpty_true :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty l = true -> find p l = None.
(* begin hide *)
Proof.
  destruct l; cbn.
    reflexivity.
    inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_find_not_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    find p l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma find_length :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    find p l = Some x -> 1 <= length l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    inversion H.
    apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma find_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    find p (snoc x l) =
    match find p l with
        | None => if p x then Some x else None
        | Some y => Some y
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma findLast_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    findLast p (snoc x l) =
    if p x then Some x else findLast p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma find_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    find p (l1 ++ l2) =
    match find p l1 with
        | Some x => Some x
        | None => find p l2
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h); rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma find_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    find p (rev l) = findLast p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite find_app, IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma find_findLast :
  forall (A : Type) (p : A -> bool) (l : list A),
    find p l = findLast p (rev l).
(* begin hide *)
Proof.
  intros. rewrite <- rev_inv at 1. apply find_rev.
Qed.
(* end hide *)

Lemma find_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    find p (map f l) =
    match find (fun x : A => p (f x)) l with
        | None => None
        | Some a => Some (f a)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p (f h)); rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma find_join :
  forall (A : Type) (p : A -> bool) (l : list (list A)),
    find p (join l) =
    (fix aux (l : list (list A)) : option A :=
    match l with
        | [] => None
        | h :: t =>
            match find p h with
                | None => aux t
                | Some x => Some x
            end
    end) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite find_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma find_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    find p (replicate n x) =
    match n, p x with
        | 0, _ => None
        | _, false => None
        | _, true => Some x
    end.
(* begin hide *)
Proof.
  induction n; cbn; intros.
    reflexivity.
    destruct (p x) eqn: Hpx.
      reflexivity.
      rewrite IHn. destruct n; rewrite ?Hpx; reflexivity.
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

Lemma find_nth :
  forall (A : Type) (p : A -> bool) (l : list A),
    (exists (n : nat) (x : A), nth n l = Some x /\ p x = true) <->
    find p l <> None.
(* begin hide *)
Proof.
  split.
    destruct 1 as (n & x & H1 & H2). revert n x H1 H2.
      induction l as [| h t]; cbn; intros.
        inv H1.
        destruct (p h) eqn: Hph.
          inversion 1.
          destruct n as [| n'].
            inv H1. congruence.
            apply (IHt _ _ H1 H2).
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct (p h) eqn: Hph.
        exists 0, h. split; [reflexivity | assumption].
        destruct (IHt H) as (n & x & H1 & H2). exists (S n), x.
          split; assumption.
Qed.
(* end hide *)

Lemma find_tail :
  forall (A : Type) (p : A -> bool) (l t : list A),
    tail l = Some t -> find p t <> None -> find p l <> None.
(* begin hide *)
Proof.
  induction l as [| h t']; cbn; intros; inversion H; subst; clear H.
  destruct (p h).
    inversion 1.
    assumption.
Qed.
(* end hide *)

Lemma find_init :
  forall (A : Type) (p : A -> bool) (l t : list A),
    init l = Some t -> find p t <> None -> find p l <> None.
(* begin hide *)
Proof.
  induction l as [| h t']; cbn; intros.
    inversion H.
    destruct (p h) eqn: Hph.
      inversion 1.
      destruct (init t').
        inversion H; subst; clear H. cbn in H0. rewrite Hph in H0.
          apply IHt' with l.
            reflexivity.
            assumption.
        inversion H; subst; clear H. cbn in H0.
          contradiction H0. reflexivity.
Qed.
(* end hide *)

Lemma find_take_Some :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    find p (take n l) = Some x -> find p l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in H.
      inv H.
      destruct (p h).
        assumption.
        apply IHt with n'. assumption.
Qed.
(* end hide *)

Lemma find_take_None :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    find p l = None -> find p (take n l) = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      destruct (p h) eqn: Hph.
        assumption.
        apply IHt. assumption.
Qed.
(* end hide *)
 
Lemma find_drop_not_None :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    find p (drop n l) <> None -> find p l <> None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in H.
      assumption.
      intro. destruct (p h).
        inv H0.
        apply IHt with n'; assumption.
Qed.
(* end hide *)

Lemma find_drop_None :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    find p l = None -> find p (drop n l) = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      assumption.
      apply IHt. destruct (p h).
        inv H.
        assumption.
Qed.
(* end hide *)

Lemma findLast_take :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findLast p (take n l) <> None -> findLast p l <> None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in H.
      contradiction.
      destruct (findLast p t).
        inversion 1.
        destruct (p h).
          inversion 1.
          apply IHt with n'. destruct (findLast p (take n' t)); assumption.
Qed.
(* end hide *)

Lemma findLast_drop :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    findLast p (drop n l) = Some x -> findLast p l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn in H.
      assumption.
      rewrite (IHt _ _ H). reflexivity.
Qed.
(* end hide *)

Lemma find_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      find p l' =
      match find p (take n l), p x with
          | Some y, _ => Some y
          | _, true => Some x
          | _, _ => find p (drop (S n) l)
      end.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (n <? length l); inv H.
  rewrite find_app. cbn. reflexivity.
Qed.
(* end hide *)

Lemma replace_findLast :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
    findLast p l' =
    match findLast p (drop (S n) l), p x with
        | Some y, _ => Some y
        | _, true => Some x
        | _, _ => findLast p (take n l)
    end.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (n <? length l); inv H.
  rewrite <- find_rev, rev_app, find_app, ?find_rev.
  destruct l; cbn.
    destruct (p x); reflexivity.
    destruct (findLast p (drop n l)), (p x); reflexivity.
Qed.
(* end hide *)

(** ** [removeFirst] i [removeLast] *)

(** Zdefiniuj funkcje [removeFirst] i [removeLast] o sygnaturach,
    które zwracają pierwszy/ostatni element z listy spełniający
    predykat boolowski [p] oraz resztę listy bez tego elementu.

    Przykład:
*)

(** [removeFirst even [1; 2; 3; 4]] = [Some (2, [1; 3; 4])] *)

(** [removeLast even [1; 2; 3; 4]] = [Some (4, [1; 2; 3])] *)

(* begin hide *)
Function removeFirst
  {A : Type} (p : A -> bool) (l : list A) : option (A * list A) :=
match l with
    | [] => None
    | h :: t =>
        if p h
        then Some (h, t)
        else
          match removeFirst p t with
              | None => None
              | Some (x, l) => Some (x, h :: l)
          end
end.

Function removeLast
  {A : Type} (p : A -> bool) (l : list A) : option (A * list A) :=
match l with
    | [] => None
    | h :: t =>
        match removeLast p t with
            | Some (x, l) => Some (x, h :: l)
            | None => if p h then Some (h, t) else None
        end
end.
(* end hide *)

Lemma removeFirst_isEmpty_true :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty l = true -> removeFirst p l = None.
(* begin hide *)
Proof.
  destruct l; cbn.
    reflexivity.
    inversion 1.
Qed.
(* end hide *)

Lemma isEmpty_removeFirst_not_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_satisfies :
  forall (A : Type) (p : A -> bool) (l l' : list A) (x : A),
    removeFirst p l = Some (x, l') -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. assumption.
      destruct (removeFirst p t) eqn: Heq.
        destruct p0. inv H. apply (IHt _ _ eq_refl).
        inv H.
Qed.
(* end hide *)

Lemma removeFirst_length :
  forall (A : Type) (p : A -> bool) (l : list A),
    length l = 0 -> removeFirst p l = None.
(* begin hide *)
Proof.
  destruct l; cbn.
    reflexivity.
    inversion 1.
Qed.
(* end hide *)

Lemma removeFirst_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    removeFirst p (snoc x l) =
    match removeFirst p l with
        | None => if p x then Some (x, l) else None
        | Some (h, t) => Some (h, snoc x t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      rewrite IHt. destruct (removeFirst p t).
        destruct p0. reflexivity.
        destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma removeLast_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    removeLast p (snoc x l) =
    if p x
    then Some (x, l)
    else
      match removeLast p l with
          | None => None
          | Some (h, t) => Some (h, snoc x t)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (p x).
      reflexivity.
      destruct (removeLast p t).
        destruct p0. reflexivity.
        destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    removeFirst p (l1 ++ l2) =
    match removeFirst p l1, removeFirst p l2 with
        | Some (h, t), _ => Some (h, t ++ l2)
        | _, Some (h, t) => Some (h, l1 ++ t)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (removeFirst p l2). destruct p0. 1-2: reflexivity.
    destruct (p h) eqn: Hph.
      reflexivity.
      rewrite IHt. destruct (removeFirst p t).
        destruct p0; cbn. reflexivity.
        destruct (removeFirst p l2).
          destruct p0. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma removeLast_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    removeLast p (l1 ++ l2) =
    match removeLast p l2, removeLast p l1 with
        | Some (y, l'), _ => Some (y, l1 ++ l')
        | _, Some (y, l') => Some (y, l' ++ l2)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (removeLast p l2).
      destruct p0. 1-2: reflexivity.
    rewrite IHt. destruct (removeLast p l2) eqn: Heq.
      destruct p0. reflexivity.
      destruct (removeLast p t).
        destruct p0. cbn. reflexivity.
        destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p (rev l) =
    match removeLast p l with
        | Some (x, l) => Some (x, rev l)
        | None => None
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite removeFirst_app, IHt; cbn. destruct (removeLast p t).
      destruct p0; cbn. reflexivity.
      destruct (p h); rewrite ?app_nil_r; reflexivity.
Qed.
(* end hide *)

Lemma removeLast_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeLast p (rev l) =
    match removeFirst p l with
        | None => None
        | Some (x, l) => Some (x, rev l)
    end.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_inv _ l) at 2. rewrite removeFirst_rev.
  destruct (removeLast p (rev l)); cbn.
    destruct p0. rewrite rev_inv. all: reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_map :
  forall (A B : Type) (p : B -> bool) (f : A -> B) (l : list A),
    removeFirst p (map f l) =
    match removeFirst (fun x => p (f x)) l with
        | Some (x, l) => Some (f x, map f l)
        | None => None
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p (f h)) eqn: Heq.
      reflexivity.
      rewrite IHt. destruct (removeFirst _ t).
        destruct p0. cbn. 1-2: reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_join :
  forall (A : Type) (p : A -> bool) (l : list (list A)),
    removeFirst p (join l) =
    (fix f (l : list (list A)) : option (A * list A) :=
    match l with
        | [] => None
        | hl :: tl =>
            match removeFirst p hl with
                | Some (x, l') => Some (x, join (l' :: tl))
                | None =>
                    match f tl with
                        | Some (x, l) => Some (x, hl ++ l)
                        | None => None
                    end
            end
    end) l.
(* begin hide *)
Proof.
  induction l as [| hl tl]; cbn.
    reflexivity.
    rewrite removeFirst_app, IHtl. reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    removeFirst p (replicate n x) =
    if p x
    then
        match n with
            | 0 => None
            | S n' => Some (x, replicate n' x)
        end
    else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct (p x); reflexivity.
    destruct (p x) eqn: Hpx.
      reflexivity.
      rewrite IHn', Hpx. reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_nth_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p l = None <->
      forall (n : nat) (x : A), nth n l = Some x -> p x = false.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inv H0.
      destruct (p h) eqn: Hph.
        inv H.
        destruct (removeFirst p t) eqn: Heq.
          destruct p0. inv H.
          destruct n as [| n'].
            inv H0. assumption.
            apply (IHt eq_refl n' _). assumption.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h) eqn: Hph.
        specialize (H 0 h eq_refl). congruence.
        rewrite IHt.
          reflexivity.
          intros. apply (H (S n)). assumption.
Qed.
(* end hide *)

Lemma removeFirst_nth_Some :
  forall (A : Type) (p : A -> bool) (x : A) (l l' : list A),
    removeFirst p l = Some (x, l') ->
    exists n : nat, nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 1.
    intros. destruct (p h) eqn: Hph.
      inversion H; subst. exists 0. cbn. split; trivial.
      destruct (removeFirst p t) eqn: Heq.
        destruct p0. inversion H; subst.
          destruct (IHt _ eq_refl) as (n & H1 & H2).
            exists (S n). cbn. split; assumption.
        inversion H.
Qed.
(* end hide *)

Lemma removeFirst_nth_Some' :
  exists (A : Type) (p : A -> bool) (n : nat) (x y : A) (l l' : list A),
    removeFirst p l = Some (x, l') /\
    nth n l = Some y /\ p y = true.
(* begin hide *)
Proof.
  exists bool, (fun _ => true), 1, true, false, [true; false], [false].
  cbn. auto.
Qed.
(* end hide *)

Lemma head_removeFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l l' : list A),
    removeFirst p l = Some (x, l') ->
    head l' =
    match l with
        | [] => None
        | h :: t => if p h then head t else Some h
   end.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h).
      inversion H; subst. reflexivity.
      destruct (removeFirst p t).
        destruct p0. inversion H; subst. cbn. reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma removeFirst_take_None :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    removeFirst p l = None -> removeFirst p (take n l) = None.
(* begin hide *)
Proof.
  intros A p n l. revert n.
  functional induction @removeFirst A p l; intros.
    rewrite take_nil. cbn. reflexivity.
    destruct n; cbn.
      reflexivity.
      inversion H.
    destruct n; cbn.
      reflexivity.
      rewrite e0, IHo; trivial.
    inversion H.
Qed.
(* end hide *)

Lemma removeFirst_take :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A) (l l' : list A),
    removeFirst p (take n l) = Some (x, l') ->
      removeFirst p l = Some (x, l' ++ drop n l).
(* begin hide *)
Proof.
  intros A p n x l. revert n x.
  functional induction @removeFirst A p l; intros.
    rewrite take_nil in H. inv H.
    destruct n; cbn in H.
      inv H.
      rewrite e0 in H. inv H. cbn. rewrite app_take_drop. reflexivity.
    destruct n as [| n']; cbn in H.
      inv H.
      rewrite e0 in H. cbn. destruct (removeFirst p (take n' t)) eqn: Heq.
        apply (removeFirst_take_None _ _ n' _) in e1. congruence.
        inv H.
    destruct n as [| n']; cbn in *.
      inv H.
      rewrite e0 in H. destruct (removeFirst p (take n' t)) eqn: Heq.
        destruct p0. inv H. rewrite (IHo _ _ _ Heq) in e1. inv e1.
          reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma removeLast_drop :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A) (l l' : list A),
    removeLast p (drop n l) = Some (x, l') ->
      removeLast p l = Some (x, take n l ++ l').
(* begin hide *)
Proof.
  intros A p n x l. revert n x.
  functional induction @removeLast A p l; intros.
    rewrite drop_nil in H. inv H.
    destruct n; cbn in H.
      rewrite e0 in H. inv H. cbn. reflexivity.
      rewrite (IHo _ _ _ H) in e0. inv e0. cbn. reflexivity.
    destruct n; cbn in H.
      rewrite e0 in H. destruct (p h); inv H. cbn. reflexivity.
      rewrite (IHo _ _ _ H) in e0. inv e0.
    destruct n; cbn in H.
      rewrite e0 in H. destruct (p h); inv H. congruence.
      rewrite (IHo _ _ _ H) in e0. inv e0.
Qed.
(* end hide *)

Lemma removeFirst_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      removeFirst p l' =
      match removeFirst p (take n l), p x, removeFirst p (drop (S n) l) with
          | Some (y, l''), _, _ => Some (y, l'' ++ x :: drop (S n) l)
          | _, true, _ => Some (x, take n l ++ drop (S n) l)
          | _, _, Some (y, l'') => Some (y, take n l ++ x :: l'')
          | _, _, _ => None
      end.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (n <? length l); inv H.
  rewrite removeFirst_app. cbn.
    destruct (removeFirst p (take n l)).
      reflexivity.
      destruct (p x).
        reflexivity.
        destruct l; cbn.
          reflexivity.
          destruct (removeFirst p (drop n l)).
            destruct p0. cbn. all: reflexivity.
Qed.
(* end hide *)

Lemma removeLast_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
    removeLast p l' =
    match removeLast p (drop (S n) l), p x, removeLast p (take n l) with
        | Some (y, l''), _ , _ => Some (y, take n l ++ x :: l'')
        | _, true, _ => Some (x, take n l ++ drop (S n) l)
        | _, _, Some (y, l'') => Some (y, l'' ++ x :: drop (S n) l)
        | _, _, _ => None
    end.
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (n <? length l); inv H.
  rewrite removeLast_app. cbn. destruct l; cbn.
    destruct (p x); reflexivity.
    destruct (removeLast p (drop n l)); cbn.
      destruct p0. reflexivity.
      destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_any_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p l = None <-> any p l = false.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h); cbn.
        inv H.
        destruct (removeFirst p t).
          destruct p0. inv H.
          apply IHt. assumption.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h); cbn in H.
        inv H.
        rewrite (IHt H). reflexivity.
Qed.
(* end hide *)

Lemma removeFirst_not_None_any :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p l <> None <-> any p l = true.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction H. reflexivity.
      destruct (p h); cbn.
        reflexivity.
        destruct (removeFirst p t).
          apply IHt. inversion 1.
          contradiction H. reflexivity.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (p h); cbn in H.
        inversion 1.
        destruct (removeFirst p t).
          destruct p0. inversion 1.
          apply IHt, H.
Qed.
(* end hide *)

Lemma removeFirst_None_iff_all :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p l = None <->
    all (fun x : A => negb (p x)) l = true.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h); cbn in *.
        inv H.
        destruct (removeFirst p t).
          destruct p0. inversion H.
          apply (IHt H).
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h); cbn in *.
        inversion H.
        rewrite (IHt H). reflexivity.
Qed.
(* end hide *)

(** ** [findIndex] *)

(** Zdefiniuj funkcję [findIndex], która znajduje indeks pierwszego elementu,
    który spełnia predykat boolowski [p]. Pamiętaj, że indeksy liczone są
    od 0.

    Przykład:
*)

(** [findIndex even [1; 3; 4; 5; 7]] = [2] *)

(* begin hide *)
Function findIndex {A : Type} (p : A -> bool) (l : list A) : option nat :=
match l with
    | [] => None
    | h :: t =>
        if p h
        then Some 0
        else match findIndex p t with
            | None => None
            | Some n => Some (S n)
        end
end.
(* end hide *)

Lemma findIndex_false :
  forall (A : Type) (l : list A),
    findIndex (fun _ => false) l = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma findIndex_true :
  forall (A : Type) (l : list A),
    findIndex (fun _ => true) l =
    match l with
        | [] => None
        | _ => Some 0
    end.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma findIndex_orb :
  forall (A : Type) (p q : A -> bool) (l : list A),
    findIndex (fun x : A => orb (p x) (q x)) l =
    match findIndex p l, findIndex q l with
        | Some n, Some m => Some (min n m)
        | Some n, None => Some n
        | None, Some m => Some m
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph, (q h) eqn: Hqh; cbn; rewrite ?IHt.
      reflexivity.
      1-3: destruct (findIndex p t), (findIndex q t); trivial.
Qed.
(* end hide *)

Lemma findIndex_isEmpty_true :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty l = true -> findIndex p l = None.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_findIndex_not_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndex p l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma findIndex_length :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n -> n < length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intros; rewrite H0 in *.
      inversion H; subst; clear H. apply le_n_S, le_0_n.
      case_eq (findIndex p t); intros; rewrite H1 in *.
        inversion H; subst; clear H. apply lt_n_S, IHt. reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma findIndex_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    findIndex p (snoc x l) =
    match findIndex p l with
        | None => if p x then Some (length l) else None
        | Some n => Some n
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      rewrite ?IHt. destruct (findIndex p t).
        reflexivity.
        destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma findIndex_app_l :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A) (n : nat),
    findIndex p l1 = Some n -> findIndex p (l1 ++ l2) = Some n.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    inversion H.
    destruct (p h).
      assumption.
      destruct (findIndex p t).
        rewrite (IHt _ _ eq_refl). assumption.
        inversion H.
Qed.
(* end hide *)

Lemma findIndex_app_r :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A) (n : nat),
    findIndex p l1 = None -> findIndex p l2 = Some n ->
      findIndex p (l1 ++ l2) = Some (length l1 + n).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    destruct (p h1).
      inversion H.
      destruct (findIndex p t1).
        inversion H.
        rewrite (IHt1 _ _ eq_refl H0). reflexivity.
Qed.
(* end hide *)

Lemma findIndex_app_None :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    findIndex p l1 = None -> findIndex p l2 = None ->
      findIndex p (l1 ++ l2) = None.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    destruct (p h1).
      inversion H.
      destruct (findIndex p t1).
        inversion H.
        rewrite (IHt1 _ eq_refl H0). reflexivity.
Qed.
(* end hide *)

Lemma findIndex_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    findIndex p (l1 ++ l2) =
    match findIndex p l1, findIndex p l2 with
        | Some n, _ => Some n
        | _, Some n => Some (length l1 + n)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  intros. case_eq (findIndex p l1); intros.
    apply findIndex_app_l. assumption.
    case_eq (findIndex p l2); intros.
      apply findIndex_app_r; assumption.
      apply findIndex_app_None; assumption.
Qed.
(* end hide *)

Lemma findIndex_map :
  forall (A B : Type) (p : B -> bool) (f : A -> B) (l : list A) (n : nat),
    findIndex (fun x : A => p (f x)) l = Some n ->
      findIndex p (map f l) = Some n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p (f h)).
      assumption.
      destruct (findIndex _ t).
        rewrite (IHt _ eq_refl). assumption.
        inversion H.
Qed.
(* end hide *)

Lemma findIndex_map_conv :
  forall (A B : Type) (p : B -> bool) (f : A -> B) (l : list A) (n : nat),
    (forall x y : A, f x = f y -> x = y) ->
    findIndex p (map f l) = Some n ->
      findIndex (fun x : A => p (f x)) l = Some n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p (f h)).
      assumption.
      destruct (findIndex _ (map f t)).
        rewrite (IHt _ H eq_refl). assumption.
        inversion H0.
Qed.
(* end hide *)

Lemma findIndex_join :
  forall (A : Type) (p : A -> bool) (ll : list (list A)),
    findIndex p (join ll) =
    match ll with
        | [] => None
        | h :: t =>
            match findIndex p h, findIndex p (join t) with
                | Some n, _ => Some n
                | _, Some n => Some (length h + n)
                | _, _ => None
            end
    end.
(* begin hide *)
Proof.
  induction ll as [| h t]; cbn; intros; rewrite ?findIndex_app; reflexivity.
Qed.
(* end hide *)

Lemma findIndex_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    findIndex p (replicate n x) =
    match n with
        | 0 => None
        | _ => if p x then Some 0 else None
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    case_eq (p x); intros.
      reflexivity.
      rewrite IHn'. destruct n'; rewrite ?H; reflexivity.
Qed.
(* end hide *)

Lemma findIndex_nth :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n ->
      exists x : A, nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. exists h. split; [reflexivity | assumption].
      destruct (findIndex p t).
        inv H. destruct (IHt _ eq_refl) as (x & IH1 & IH2).
          exists x. split; assumption.
        inv H.
Qed.
(* end hide *)

Lemma findIndex_nth_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> p x = true ->
      exists m : nat, findIndex p l = Some m /\ m <= n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      exists 0. split; [reflexivity | apply le_0_n].
      destruct n as [| n'].
        inv H. congruence.
        destruct (IHt _ _ H H0) as (m & IH1 & IH2).
          rewrite IH1. exists (S m). split.
            reflexivity.
            apply le_n_S, IH2.
Qed.
(* end hide *)

Lemma findIndex_nth' :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n -> find p l = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. reflexivity.
      destruct (findIndex p t); inv H.
        apply IHt. reflexivity.
Qed.
(* end hide *)

Lemma findIndex_head :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndex p l = Some 0 <->
    exists x : A, head l = Some x /\ p x = true.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      case_eq (p h); intros.
        exists h. split; trivial.
        destruct (findIndex p t); rewrite H0 in *; inversion H.
    destruct 1 as (x & H1 & H2). destruct l as [| h t]; cbn in *.
      inversion H1.
      inversion H1; subst; clear H1. rewrite H2. reflexivity.
Qed.
(* end hide *)

Lemma findIndex_last :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndex p l = Some (length l - 1) <->
    exists x : A,
      last l = Some x /\
      p x = true /\
      forall (n : nat) (y : A),
        n < length l - 1 -> nth n l = Some y -> p y = false.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (p h) eqn: Hph; intros.
        exists h. inversion H; subst. destruct t; cbn in H1; inversion H1.
          repeat split; trivial. intros. destruct n; inversion H0.
        destruct (findIndex p t) eqn: Heq.
          destruct t; cbn in *; inversion H; subst; clear H.
            rewrite <- minus_n_O in IHt. specialize (IHt eq_refl).
            destruct IHt as (x & H1 & H2 & H3). exists x.
              repeat split; trivial. intros. destruct n as [| n']; cbn in *.
                inversion H0; subst. assumption.
                apply (H3 n').
                  apply lt_S_n. assumption.
                  assumption.
          inversion H.
    destruct 1 as (x & H1 & H2 & H3).
    induction l as [| h t]; cbn in *.
      inversion H1.
      destruct (p h) eqn: Hph.
        destruct t; inversion H1; subst; clear H1; cbn in *.
          reflexivity.
          specialize (H3 0 h ltac:(lia) eq_refl); cbn in H3. congruence.
        destruct t; inversion H1; subst; clear H1; cbn in *.
          congruence.
          destruct (p a) eqn: Hpa.
            destruct t; inversion H0; subst; cbn in *.
              reflexivity.
              specialize (H3 1 a ltac:(lia) eq_refl). congruence.
            rewrite IHt.
              rewrite <- minus_n_O. reflexivity.
              assumption.
              intros. apply H3 with (S n).
                apply lt_n_S. rewrite minus_n_O. assumption.
                cbn. assumption.
Qed.
(* end hide *)

Lemma findIndex_spec :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n ->
      forall m : nat, m < n ->
        exists x : A, nth m l = Some x /\ p x = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. inv H0.
      destruct m as [| m']; cbn.
        exists h. split; [reflexivity | assumption].
        destruct (findIndex p t); inv H.
          apply (IHt _ eq_refl _ (lt_S_n _ _ H0)).
Qed.
(* end hide *)

Lemma findIndex_take :
  forall (A : Type) (p : A -> bool) (l : list A) (n m : nat),
    findIndex p (take n l) = Some m ->
      findIndex p l = Some m /\ m <= n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in H.
      inv H.
      destruct (p h).
        inv H. split; [reflexivity | apply le_0_n].
        destruct (findIndex p (take n' t)) eqn: Heq.
          inv H. destruct (IHt _ _ Heq). rewrite H. split.
            reflexivity.
            apply le_n_S. assumption.
          inv H.
Qed.
(* end hide *)

Lemma findIndex_drop :
  forall (A : Type) (p : A -> bool) (l : list A) (n m : nat),
    findIndex p l = Some m -> n <= m ->
      findIndex p (drop n l) = Some (m - n).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      rewrite <- minus_n_O. assumption.
      destruct (p h).
        inv H. inv H0.
        destruct (findIndex p t) eqn: Heq.
          inv H. cbn. apply IHt.
            reflexivity.
            apply le_S_n. assumption.
          inv H.
Qed.
(* end hide *)

Lemma findIndex_zip :
  forall (A B : Type) (pa : A -> bool) (pb : B -> bool)
  (la : list A) (lb : list B) (n : nat),
    findIndex pa la = Some n -> findIndex pb lb = Some n ->
      findIndex (fun '(a, b) => andb (pa a) (pb b)) (zip la lb) = Some n.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H.
    destruct lb as [| hb tb]; cbn in *; rewrite ?H1.
      assumption.
      destruct (pa ha); cbn.
        inversion H; subst; clear H. destruct (pb hb); cbn.
          reflexivity.
          destruct (findIndex pb tb); congruence.
        case_eq (findIndex pa ta); case_eq (findIndex pb tb); intros;
        rewrite ?H1, ?H2 in *; try congruence.
          destruct (pb hb); inversion H0; subst; clear H0.
            congruence.
            inversion H; subst; clear H. rewrite (IHta _ _ eq_refl H1).
              reflexivity.
          destruct (pb hb); congruence.
Restart.
  induction la as [| ha ta]; cbn; intros;
  repeat (cbn in *; match goal with
      | H : None = Some _ |- _ => inversion H; subst; clear H
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      | |- context [match ?x with _ => _ end] =>
          is_var x; let H := fresh "H" in destruct x eqn: H
      | H : context [match ?x with _ => _ end] |- _ =>
          let H := fresh "H" in
            destruct x eqn: H
      | H : _ = true |- _ => rewrite ?H in *
      | H : _ = false |- _ => rewrite ?H in *
  end).
    reflexivity.
    rewrite (IHta _ _ eq_refl H3). reflexivity.
Qed.
(* end hide *)

Lemma findIndex_zip_conv :
  forall (A B : Type) (pa : A -> bool) (pb : B -> bool)
  (la : list A) (lb : list B) (n : nat),
    findIndex (fun '(a, b) => andb (pa a) (pb b)) (zip la lb) = Some n ->
    exists na nb : nat,
      findIndex pa la = Some na /\
      findIndex pb lb = Some nb /\
      na <= n /\
      nb <= n.
(* begin hide *)
Proof.
  Functional Scheme zip_ind := Induction for zip Sort Prop.
  intros A B pa pb la lb.
  functional induction @zip A B la lb; cbn.
    1-2: inversion 1.
    destruct (pa ha) eqn: Hpaha; cbn; intros.
      destruct (pb hb) eqn: Hpbhb; cbn.
        inv H. exists 0, 0. repeat split; apply le_0_n.
        destruct (findIndex _ (zip ta tb)).
          destruct (IHl _ eq_refl) as (na & nb & H1 & H2 & H3 & H4).
            rewrite H2. exists 0, (S nb). inv H. repeat split; lia.
          inv H.
      destruct (findIndex _ (zip ta tb)).
        destruct (IHl _ eq_refl) as (na & nb & H1 & H2 & H3 & H4).
          rewrite H1, H2. destruct (pb hb).
            exists (S na), 0. inv H. repeat split; lia.
            exists (S na), (S nb). inv H. repeat split; lia.
        inv H.
Qed.
(* end hide *)

(** ** [count] *)

(** Zdefiniuj funkcję [count], która liczy, ile jest na liście [l] elementów
    spełniających predykat boolowski [p].

    Przykład:
*)

(** [count even [1; 2; 3; 4]] = [2] *)

(* begin hide *)
Fixpoint count {A : Type} (p : A -> bool) (l : list A) : nat :=
match l with
    | [] => 0
    | h :: t => if p h then S (count p t) else count p t
end.
(* end hide *)

Lemma count_isEmpty :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty l = true -> count p l = 0.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_count_not_0 :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p l <> 0 -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma count_length :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p l <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply le_0_n.
    destruct (p h) eqn: Hph.
      apply le_n_S. assumption.
      apply le_S. assumption.
Qed.
(* end hide *)

Lemma count_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    count p (snoc x l) = count p l + if p x then 1 else 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma count_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    count p (l1 ++ l2) = count p l1 + count p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite IHt1. destruct (p h1); cbn; reflexivity.
Qed.
(* end hide *)

Lemma count_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p (rev l) = count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite count_app, IHt. cbn. destruct (p h); cbn.
      rewrite plus_comm. cbn. reflexivity.
      apply plus_0_r.
Qed.
(* end hide *)

Lemma count_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    count p (map f l) = count (fun x : A => p (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p (f h)); rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

(* Lemma count_join *)

Lemma count_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    count p (replicate n x) =
    if p x then n else 0.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct (p x); reflexivity.
    rewrite IHn'. destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma count_insert :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    count p (insert l n x) =
    (if p x then 1 else 0) + count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite plus_0_r. reflexivity.
    destruct n as [| n']; cbn;
      rewrite ?IHt; destruct (p x), (p h); reflexivity.
Qed.
(* end hide *)

Lemma count_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      count p l' = count p (take n l) + count p [x] + count p (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. destruct (p x); rewrite drop_0; reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. cbn. rewrite (IHt _ _ _ Heq). cbn.
          destruct (p h), (p x); cbn; reflexivity.
        inv H. 
Qed.
(* end hide *)

Lemma count_remove :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    remove n l = Some (x, l') ->
      S (count p l') = if p x then count p l else S (count p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n']; cbn.
      inversion H; subst; clear H. destruct (p x); reflexivity.
      destruct (remove n' t) eqn: Heq; cbn in H.
        Focus 2. inversion H.
        destruct p0. inversion H; subst; clear H.
          cbn. destruct (p h), (p x) eqn: Hpx; cbn;
          rewrite (IHt _ _ _ Heq), Hpx; reflexivity.
Qed.
(* end hide *)

Lemma count_take :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    count p (take n l) <= n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      apply le_n.
      destruct (p h).
        apply le_n_S. apply IHt.
        apply le_S. apply IHt.
Qed.
(* end hide *)

Lemma count_take' :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    count p (take n l) <= min n (count p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      apply le_n.
      destruct (p h).
        apply le_n_S, IHt.
        apply le_trans with (min n' (count p t)).
          apply IHt.
          destruct (count p t).
            rewrite Nat.min_0_r. apply le_n.
            apply le_trans with (min (S n') (S n)).
              apply Nat.min_le_compat_r. apply le_S, le_n.
              cbn. reflexivity.
Qed.
(* end hide *)

Lemma count_drop :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    count p (drop n l) <= length l - n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_n.
    destruct n as [| n']; cbn.
      destruct (p h).
        apply le_n_S. specialize (IHt 0).
          rewrite <- minus_n_O, drop_0 in IHt. assumption.
        apply le_S. specialize (IHt 0).
          rewrite <- minus_n_O, drop_0 in IHt. assumption.
      apply IHt.
Qed.
(* end hide *)

Lemma count_cycle :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    count p (cycle n l) = count p l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn', count_snoc. cbn. destruct (p h).
        rewrite plus_comm. cbn. reflexivity.
        rewrite <- plus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma count_splitAt :
  forall (A : Type) (p : A -> bool) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      count p l = (if p x then 1 else 0) + count p l1 + count p l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct n as [| n']; cbn.
      inversion H; subst; clear H. destruct (p x); reflexivity.
      destruct (splitAt n' t) eqn: Heq; cbn in H.
        destruct p0, p0. inversion H; subst; clear H.
          cbn. destruct (p h), (p x) eqn: Hpx; cbn;
          rewrite (IHt _ _ _ _ Heq), Hpx; reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma count_false :
  forall (A : Type) (l : list A),
    count (fun _ => false) l = 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma count_true :
  forall (A : Type) (l : list A),
    count (fun _ => true) l = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma count_negb :
  forall (A : Type) (p : A -> bool) (l : list A),
    count (fun x : A => negb (p x)) l = length l - count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      assumption.
      rewrite IHt. destruct (count p t) eqn: Heq.
        rewrite <- minus_n_O. reflexivity.
        rewrite minus_Sn_m; cbn.
          reflexivity.
          rewrite <- Heq. apply count_length.
Qed.
(* end hide *)

Lemma count_andb_le_l :
  forall (A : Type) (p q : A -> bool) (l : list A),
    count (fun x : A => andb (p x) (q x)) l <= count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply le_0_n.
    destruct (p h); cbn.
      destruct (q h).
        apply le_n_S. assumption.
        apply le_S. assumption.
        assumption.
Qed.
(* end hide *)

Lemma count_andb_le_r :
  forall (A : Type) (p q : A -> bool) (l : list A),
    count (fun x : A => andb (p x) (q x)) l <= count q l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply le_0_n.
    destruct (p h), (q h); cbn.
      apply le_n_S. assumption.
      assumption.
      apply le_S. assumption.
      assumption.
Qed.
(* end hide *)

Lemma count_orb :
  forall (A : Type) (p q : A -> bool) (l : list A),
    count (fun x : A => orb (p x) (q x)) l =
    (count p l + count q l) - count (fun x : A => andb (p x) (q x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph, (q h) eqn: Hqh; cbn; rewrite IHt.
      rewrite <- plus_n_Sm, minus_Sn_m.
        reflexivity.
        apply le_plus_trans, count_andb_le_l.
      rewrite minus_Sn_m; cbn.
        reflexivity.
        apply le_plus_trans, count_andb_le_l.
      rewrite <- plus_n_Sm, minus_Sn_m; cbn.
        reflexivity.
        apply le_plus_trans, count_andb_le_l.
      reflexivity.
Restart.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    pose (count_andb_le_l A p q).
      destruct (p h) eqn: Hph, (q h) eqn: Hqh; cbn;
      rewrite IHt, <- ?plus_n_Sm, ?minus_Sn_m; auto.
        all: apply le_plus_trans; auto.
Qed.
(* end hide *)

Lemma count_orb_le :
  forall (A : Type) (p q : A -> bool) (l : list A),
    count (fun x : A => orb (p x) (q x)) l <=
    count p l + count q l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply le_0_n.
    destruct (p h) eqn: Hph, (q h) eqn: Hqh; cbn; rewrite <- ?plus_n_Sm.
      apply le_n_S, le_S. assumption.
      1-2: apply le_n_S; assumption.
      assumption.
Qed.
(* end hide *)

Lemma count_andb :
  forall (A : Type) (p q : A -> bool) (l : list A),
    count (fun x : A => andb (p x) (q x)) l =
    count p l + count q l - count (fun x : A => orb (p x) (q x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph, (q h) eqn: Hqh; cbn; rewrite IHt.
      rewrite <- plus_n_Sm, minus_Sn_m.
        reflexivity.
        apply count_orb_le.
      reflexivity.
      rewrite <- plus_n_Sm. cbn. reflexivity.
      reflexivity.
Qed.
(* end hide *)

(** ** [filter] *)

(** Zdefiniuj funkcję [filter], która zostawia na liście elementy, dla których
    funkcja [p] zwraca [true], a usuwa te, dla których zwraca [false].

    Przykład: *)

(** [filter even [1; 2; 3; 4]] = [[2; 4]] *)

(* begin hide *)
Fixpoint filter {A : Type} (f : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if f h then h :: filter f t else filter f t
end.
(* end hide *)

Lemma filter_false :
  forall (A : Type) (l : list A),
    filter (fun _ => false) l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; trivial.
Qed.
(* end hide *)

Lemma filter_true :
  forall (A : Type) (l : list A),
    filter (fun _ => true) l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma filter_andb :
  forall (A : Type) (f g : A -> bool) (l : list A),
    filter (fun x : A => andb (f x) (g x)) l =
    filter f (filter g l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    case_eq (g h); case_eq (f h); cbn; intros; rewrite ?H, ?H0, ?IHt; auto.
Qed.
(* end hide *)

Lemma isEmpty_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty (filter p l) = all (fun x : A => negb (p x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn; trivial.
Qed.
(* end hide *)

Lemma length_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    length (filter p l) <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct (p h).
      cbn. apply le_n_S. assumption.
      apply le_trans with (length t).
        assumption.
        apply le_S. apply le_n.
Qed.
(* end hide *)

Lemma filter_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    filter p (snoc x l) =
    if p x then snoc x (filter p l) else filter p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. destruct (p h), (p x); reflexivity.
Qed.
(* end hide *)

Lemma filter_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    destruct (p h1); rewrite IHt1; trivial.
Qed.
(* end hide *)

Lemma filter_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    filter p (rev l) = rev (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    rewrite filter_app; cbn. destruct (p h); cbn.
      rewrite IHt. trivial.
      rewrite app_nil_r. rewrite IHt. trivial.
Qed.
(* end hide *)

Lemma filter_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    filter p (map f l) = map f (filter (fun x : A => p (f x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    destruct (p (f h)); cbn; rewrite IHt; trivial.
Qed.
(* end hide *)

Lemma filter_join :
  forall (A : Type) (p : A -> bool) (lla : list (list A)),
    filter p (join lla) = join (map (filter p) lla).
(* begin hide *)
Proof.
  induction lla as [| hl tl]; cbn.
    reflexivity.
    rewrite filter_app, IHtl. reflexivity.
Qed.
(* end hide *)

Lemma filter_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    filter p (replicate n x) =
    if p x then replicate n x else [].
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros;
  destruct (p x) eqn: Hpx; cbn;
  rewrite ?(IHn' x), ?Hpx; reflexivity.
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

Lemma head_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    head (filter p l) = find p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma last_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    last (filter p l) = findLast p l.
(* begin hide *)
Proof.
  intros.
  rewrite <- find_rev, <- head_rev, <- filter_rev.
  apply head_filter.
Qed.
(* end hide *)

Lemma filter_nth :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> p x = true ->
      exists m : nat, m <= n /\ nth m (filter p l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. exists 0. rewrite H0. cbn. split; reflexivity.
      destruct (IHt _ _ H H0) as (m & IH1 & IH2).
        destruct (p h); cbn.
          exists (S m). split.
            apply le_n_S, IH1.
            assumption.
          exists m. split.
            apply le_trans with (S m).
              apply le_S, le_n.
              apply le_n_S. assumption.
            assumption.
Qed.
(* end hide *)

Lemma splitAt_filter :
  forall (A : Type) (p : A -> bool) (l l1 l2 : list A) (x : A) (n : nat),
    splitAt n (filter p l) = Some (l1, x, l2) ->
      exists m : nat,
      match splitAt m l with
          | None => False
          | Some (l1', y, l2') =>
              x = y /\ l1 = filter p l1' /\ l2 = filter p l2'
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h) eqn: Hph.
      destruct n as [| n']; cbn in *.
        inversion H; subst; clear H. exists 0. repeat split.
        destruct (splitAt n' (filter p t)) eqn: Heq.
          destruct p0, p0. inversion H; subst; clear H.
            destruct (IHt _ _ _ _ Heq) as [m IH].
              exists (S m). destruct (splitAt m t).
                destruct p0, p0, IH as (IH1 & IH2 & IH3); subst.
                  cbn. rewrite Hph. repeat split.
                assumption.
          inversion H.
      destruct (IHt _ _ _ _ H) as (m & IH). exists (S m).
        destruct (splitAt m t).
          destruct p0, p0. cbn. rewrite Hph. assumption.
          assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: intersperse_splitAt *)
(* end hide *)

Lemma filter_insert :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    filter p (insert l n x) =
      filter p (take n l) ++
      (if p x then [x] else []) ++
      filter p (drop n l).
(* begin hide *)
Proof.
  intros. rewrite insert_spec, filter_app. cbn.
  destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma replace_filter :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      filter p l' =
      filter p (take n l) ++ filter p [x] ++ filter p (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. destruct (p x); cbn; rewrite drop_0; reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. cbn. rewrite (IHt _ _ _ Heq). cbn.
          destruct (p h), (p x); cbn; reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma remove_filter :
  forall (A : Type) (p : A -> bool) (l l' : list A) (x : A) (n : nat),
    remove n (filter p l) = Some (x, l') ->
      exists m : nat,
      match remove m l with
          | None => False
          | Some (y, l'') => x = y /\ l' = filter p l''
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h) eqn: Hph.
      destruct n as [| n']; cbn in *.
        inversion H; subst; clear H. exists 0. split; reflexivity.
        destruct (remove n' (filter p t)) eqn: Heq.
          destruct p0. inversion H; subst; clear H.
            destruct (IHt _ _ _ Heq) as [m IH].
              exists (S m). destruct (remove m t).
                destruct p0, IH. cbn. rewrite Hph, H0. split; trivial.
                assumption.
          inversion H.
      destruct (IHt _ _ _ H) as (m & IH). exists (S m).
        destruct (remove m t).
          destruct p0. cbn. rewrite Hph. assumption.
          assumption.
Qed.
(* end hide *)

Lemma filter_idempotent :
  forall (A : Type) (f : A -> bool) (l : list A),
    filter f (filter f l) = filter f l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    case_eq (f h); cbn; intro; try rewrite H, IHt; trivial.
Qed.
(* end hide *)

Lemma filter_comm :
  forall (A : Type) (f g : A -> bool) (l : list A),
    filter f (filter g l) = filter g (filter f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    case_eq (f h); case_eq (g h); cbn; intros;
      rewrite ?H, ?H0, IHt; trivial.
Qed.
(* end hide *)

Lemma zip_not_filter :
  exists (A B : Type) (pa : A -> bool) (pb : B -> bool)
  (la : list A) (lb : list B),
    zip (filter pa la) (filter pb lb) <>
    filter (fun x => andb (pa (fst x)) (pb (snd x))) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (fun a : bool => if a then true else false). exists negb.
  exists [false; true], [false; true].
  cbn. inversion 1.
Qed.
(* end hide *)

Lemma any_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p l = negb (isEmpty (filter p l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (p h); cbn; reflexivity.
Qed.
(* end hide *)

Lemma all_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p (filter p l) = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; cbn; assumption.
Qed.
(* end hide *)

Lemma all_filter' :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p l = isEmpty (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (p h); cbn; reflexivity.
Qed.
(* end hide *)

Lemma filter_all :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p l = true -> filter p l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn in *; rewrite IHt; congruence.
Qed.
(* end hide *)

Lemma removeFirst_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p (filter p l) =
    match filter p l with
        | [] => None
        | h :: t => Some (h, t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph.
      reflexivity.
      exact IHt.
Qed.
(* end hide *)

Lemma removeFirst_negb_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst (fun x : A => negb (p x)) (filter p l) = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; cbn.
      rewrite IHt. reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma findIndex_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndex p (filter p l) = None \/
    findIndex p (filter p l) = Some 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    left. reflexivity.
    case_eq (p h); cbn; intros; rewrite ?H.
      right. reflexivity.
      destruct IHt; [left | right]; assumption.
Qed.
(* end hide *)

Lemma count_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p (filter p l) = length (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite Hph, IHt. reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma count_filter' :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p (filter p l) = count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite Hph, IHt. reflexivity.
      assumption.
Qed.
(* end hide *)

(** ** [partition] *)

(** Zdefiniuj funkcję [partition], która dzieli listę [l] na listy
    elementów spełniających i niespełniających pewnego warunku
    boolowskiego.

    Przykład:
*)

(** [partition even [1; 2; 3; 4]] = [([2; 4], [1; 3])] *)

(* begin hide *)
Fixpoint partition {A : Type} (p : A -> bool) (l : list A)
    : list A * list A :=
match l with
    | [] => ([], [])
    | h :: t => let (l1, l2) := partition p t in
        if p h then (h :: l1, l2) else (l1, h :: l2)
end.
(* end hide *)

Lemma partition_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    partition p l = (filter p l, filter (fun x => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    destruct (partition p t). destruct (p h); cbn; inversion IHt; trivial.
Qed.
(* end hide *)

Lemma partition_true :
  forall (A : Type) (p : A -> bool) (l : list A),
    partition (fun _ => true) l = (l, []).
(* begin hide *)
Proof.
  intros. rewrite partition_spec, filter_true, filter_false. reflexivity.
Qed.
(* end hide *)

Lemma partition_false :
  forall (A : Type) (p : A -> bool) (l : list A),
    partition (fun _ => false) l = ([], l).
(* begin hide *)
Proof.
  intros. rewrite partition_spec, filter_true, filter_false. reflexivity.
Qed.
(* end hide *)

Lemma partition_cons_true :
  forall (A : Type) (p : A -> bool) (h : A) (t l1 l2 : list A),
    p h = true -> partition p t = (l1, l2) ->
      partition p (h :: t) = (h :: l1, l2).
(* begin hide *)
Proof.
  intros. rewrite partition_spec in *.
  inversion H0; subst; clear H0. cbn.
  destruct (p h) eqn: Hph; cbn.
    reflexivity.
    congruence.
Qed.
(* end hide *)

Lemma partition_cons_false :
  forall (A : Type) (p : A -> bool) (h : A) (t l1 l2 : list A),
    p h = false -> partition p t = (l1, l2) ->
      partition p (h :: t) = (l1, h :: l2).
(* begin hide *)
Proof.
  intros. rewrite partition_spec in *.
  inversion H0; subst; clear H0. cbn.
  destruct (p h) eqn: Hph; cbn.
    congruence.
    reflexivity.
Qed.
(* end hide *)

(** ** [findIndices] *)

(** Zdefiniuj funkcję [findIndices], która znajduje indeksy wszystkich
    elementów listy, które spełniają predykat boolowski [p].

    Przykład: *)

(** [findIndices even [1; 1; 2; 3; 5; 8; 13; 21; 34]] = [[2; 5; 8]] *)

(* begin hide *)
Fixpoint findIndices {A : Type} (p : A -> bool) (l : list A) : list nat :=  
match l with
    | [] => []
    | h :: t =>
        if p h
        then 0 :: map S (findIndices p t)
        else map S (findIndices p t)
end.

Fixpoint findIndices'_aux
  {A : Type} (p : A -> bool) (l : list A) (n : nat) : list nat :=
match l with
    | [] => []
    | h :: t =>
        let x := findIndices'_aux p t (S n) in
          if p h then n :: x else x
end.

Definition findIndices'
  {A : Type} (p : A -> bool) (l : list A) : list nat :=
    findIndices'_aux p l 0.

Axiom ext :
  forall (A B : Type) (f g : A -> B),
    (forall x : A, f x = g x) -> f = g.

Lemma findIndices'_aux_spec :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndices'_aux p l n = map (plus n) (findIndices p l).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h); cbn.
      rewrite plus_0_r, IHt, map_map. do 2 f_equal.
        cbn. apply ext. intro. apply plus_n_Sm.
      rewrite IHt, map_map. do 2 f_equal.
        cbn. apply ext. intro. apply plus_n_Sm.
Qed.

Lemma findIndices'_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndices p l = findIndices' p l.
Proof.
  intros. unfold findIndices'. symmetry. rewrite <- map_id.
  change id with (add 0). apply findIndices'_aux_spec.
Qed.
(* end hide *)

Lemma findIndices_false :
  forall (A : Type) (l : list A),
    findIndices (fun _ => false) l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma findIndices_true :
  forall (A : Type) (l : list A),
    findIndices (fun _ => true) l =
    if isEmpty l then [] else iterate S (length l) 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct t; cbn.
      reflexivity.
      rewrite map_iterate. reflexivity.
Qed.
(* end hide *)

Lemma findIndices_isEmpty_true :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty l = true -> findIndices p l = [].
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_findIndices_not_nil :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndices p l <> [] -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    contradiction.
    reflexivity.
Qed.
(* end hide *)

Lemma length_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    length (findIndices p l) = count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn; rewrite length_map, ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma findIndices_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    findIndices p (snoc x l) =
    if p x
    then snoc (length l) (findIndices p l)
    else findIndices p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h), (p x); cbn; rewrite IHt, ?map_snoc; reflexivity.
Qed.
(* end hide *)

Lemma findIndices_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    findIndices p (l1 ++ l2) =
    findIndices p l1 ++ map (plus (length l1)) (findIndices p l2).
(* begin hide *)
Proof.
  induction l1 as [| h t ]; cbn; intros.
    rewrite map_id. reflexivity.
    rewrite IHt, map_app, map_map. destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma findIndices_rev_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    rev (findIndices p (rev l)) =
    map (fun n : nat => length l - S n) (findIndices p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite findIndices_app, ?rev_app, ?IHt, ?length_rev, <- ?map_rev.
      cbn. destruct (p h); cbn.
        rewrite <- map_map, plus_0_r, <- minus_n_O. reflexivity.
        rewrite <- map_map. reflexivity.
Qed.
(* end hide *)

Lemma findIndices_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndices p (rev l) =
    rev (map (fun n : nat => length l - S n) (findIndices p l)).
(* begin hide *)
Proof.
  intros. rewrite <- findIndices_rev_aux, rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma rev_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    rev (findIndices p l) =
    map (fun n : nat => length l - S n) (findIndices p (rev l)).
(* begin hide *)
Proof.
  intros. rewrite <- (rev_inv _ l) at 1.
  rewrite findIndices_rev_aux, length_rev.
  reflexivity.
Qed.
(* end hide *)

Lemma findIndices_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    findIndices p (map f l) =
    findIndices (fun x : A => p (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma findIndices_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    findIndices p (replicate n x) =
    match n with
        | 0 => []
        | S n' => if p x then iterate S n 0 else []
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. destruct (p x).
      destruct n'; cbn.
        reflexivity.
        rewrite map_iterate. reflexivity.
      destruct n'; reflexivity.
Qed.
(* end hide *)

Lemma map_nth_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    map (fun n : nat => nth n l) (findIndices p l) =
    map Some (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      1-2: rewrite map_map; cbn; rewrite IHt; reflexivity.
Qed.
(* end hide *)

Lemma head_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    head (findIndices p l) = findIndex p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      rewrite head_map, <- IHt. destruct (findIndices p t); reflexivity.
Qed.
(* end hide *)

Lemma tail_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    tail (findIndices p l) =
    match removeFirst p l with
        | None => None
        | Some (_, l') => Some (map S (findIndices p l'))
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      reflexivity.
      destruct (findIndices p t); cbn in *.
        destruct (removeFirst p t).
          destruct p0. inversion IHt.
          reflexivity.
        destruct (removeFirst p t).
          destruct p0. inversion IHt; subst. cbn. rewrite Hph. reflexivity.
          inversion IHt.
Restart.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      reflexivity.
      destruct (findIndices p t), (removeFirst p t);
      try destruct p0; inversion IHt; subst; cbn;
      rewrite ?Hph; reflexivity.
Qed.
(* end hide *)

Lemma last_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    last (findIndices p l) =
    match findIndex p (rev l) with
        | None => None
        | Some n => Some (length l - S n)
    end.
(* begin hide *)
Proof.
  intros.
  rewrite <- head_rev, <- (rev_inv _ l) at 1.
  rewrite findIndices_rev_aux. rewrite <- head_findIndices.
  destruct (findIndices p (rev l)); cbn.
    reflexivity.
    rewrite length_rev. reflexivity.
Qed.
(* end hide *)

Lemma init_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    init (findIndices p l) =
    match removeLast p l with
        | None => None
        | Some (_, l') => Some (findIndices p l')
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite init_map. destruct (findIndices p t) eqn: Heq; cbn in *.
        destruct (removeLast p t).
          destruct p0. inv IHt.
          rewrite Heq. reflexivity.
        destruct (init l), (removeLast p t); cbn.
          destruct p0. cbn. rewrite Hph. inv IHt. reflexivity.
          inv IHt.
          destruct p0. cbn. rewrite Hph. inv IHt. reflexivity.
          inv IHt.
      rewrite init_map. destruct (findIndices p t) eqn: Heq; cbn in *.
        destruct (removeLast p t).
          destruct p0. inv IHt.
          reflexivity.
        destruct (init l), (removeLast p t); cbn.
          destruct p0. cbn. rewrite Hph. inv IHt. reflexivity.
          inv IHt.
          destruct p0. cbn. rewrite Hph. inv IHt. reflexivity.
          inv IHt.
Qed.
(* end hide *)

Lemma findIndices_take :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndices p (take n l) =
    take (count p (take n l)) (findIndices p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      rewrite take_0. reflexivity.
      destruct (p h); cbn; rewrite IHt, take_map; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: findIndices vs drop, splitAt *)
(* end hide *)

Lemma findIndices_insert :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    findIndices p (insert l n x) =
      findIndices p (take n l) ++
      (if p x then [min (length l) n] else []) ++
      map (plus (S n)) (findIndices p (drop n l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    destruct n as [| n']; cbn.
      destruct (p x), (p h); reflexivity.
      rewrite ?IHt, ?map_app, map_map.
        destruct (p h), (p x); reflexivity.
Qed.
(* end hide *)

Lemma findIndices_replace :
  forall (A : Type) (p : A -> bool) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
    findIndices p l' =
    findIndices p (take n l) ++
    map (plus n) (findIndices p [x]) ++
    map (plus (S n)) (findIndices p (drop (S n) l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. cbn. destruct (p x); cbn; rewrite drop_0; reflexivity.
      destruct (replace t n' x) eqn: Heq.
        inv H. cbn. rewrite (IHt _ _ _ Heq). cbn.
          destruct (p h), (p x); cbn; rewrite ?map_app, ?plus_0_r.
            do 2 f_equal. cbn. rewrite map_map. reflexivity.
            do 2 f_equal. rewrite map_map. reflexivity.
            do 2 f_equal. cbn. rewrite map_map. reflexivity.
            f_equal. rewrite map_map. reflexivity.
          inv H.
Qed.
(* end hide *)

(** ** [takeWhile] i [dropWhile] *)

(** Zdefiniuj funkcje [takeWhile] oraz [dropWhile], które, dopóki
    funkcja [p] zwraca [true], odpowiednio biorą lub usuwają elementy
    z listy.

    Przykład:
*)

(** [takeWhile even [2; 4; 6; 1; 8; 10; 12]] = [[2; 4; 6]] *)

(** [dropWhile even [2; 4; 6; 1; 8; 10; 12]] = [[1; 8; 10; 12]] *)

(* begin hide *)
Fixpoint takeWhile {A : Type} (p : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if p h then h :: takeWhile p t else []
end.

Fixpoint dropWhile {A : Type} (p : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if p h then dropWhile p t else l
end.
(* end hide *)

Lemma takeWhile_dropWhile_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    takeWhile p l ++ dropWhile p l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h); cbn.
      rewrite IHt. reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma takeWhile_false :
  forall (A : Type) (l : list A),
    takeWhile (fun _ => false) l = [].
(* begin hide *)
Proof.
  destruct l; cbn; trivial.
Qed.
(* end hide *)

Lemma dropWhile_false :
  forall (A : Type) (l : list A),
    dropWhile (fun _ => false) l = l.
(* begin hide *)
Proof.
  destruct l; cbn; trivial.
Qed.
(* end hide *)

Lemma takeWhile_andb :
  forall (A : Type) (p q : A -> bool) (l : list A),
    takeWhile (fun x : A => andb (p x) (q x)) l =
    takeWhile p (takeWhile q l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph, (q h) eqn: Hqh; cbn; rewrite ?Hph.
      rewrite IHt. all: reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty (takeWhile p l) =
    match l with
        | [] => true
        | h :: t => negb (p h)
    end.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn; reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    isEmpty (dropWhile p l) = all p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn; trivial.
Qed.
(* end hide *)

Lemma takeWhile_snoc_all :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all p l = true ->
      takeWhile p (snoc x l) = if p x then snoc x l else l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h); cbn in *.
      rewrite (IHt H). destruct (p x); reflexivity.
      inversion H.
Qed.
(* end hide *)

(* begin hide *)
Lemma dropWhile_snoc_all :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all p l = true ->
      dropWhile p (snoc x l) = if p x then [] else [x].
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt.
      destruct (p x), (p h); cbn in *; congruence || reflexivity.
      destruct (p h); cbn in H.
        assumption.
        congruence.
Qed.
(* end hide *)

Lemma takeWhile_idempotent :
  forall (A : Type) (p : A -> bool) (l : list A),
    takeWhile p (takeWhile p l) = takeWhile p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    case_eq (p h); cbn; intro.
      rewrite H. rewrite IHt. trivial.
      trivial.
Qed.
(* end hide *)

Lemma dropWhile_idempotent :
  forall (A : Type) (p : A -> bool) (l : list A),
    dropWhile p (dropWhile p l) = dropWhile p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    case_eq (p h); cbn; intro; [rewrite IHt | rewrite H]; trivial.
Qed.
(* end hide *)

Lemma takeWhile_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    takeWhile p (replicate n x) =
    if p x then replicate n x else [].
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros;
  rewrite ?IHn'; destruct (p x); reflexivity.
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

Lemma dropWhile_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    dropWhile p (replicate n x) =
    if p x then [] else replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros;
  rewrite ?IHn'; destruct (p x); reflexivity.
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

Lemma any_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p (takeWhile p l) = negb (isEmpty (takeWhile p l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; cbn; reflexivity.
Qed.
(* end hide *)

Lemma any_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    any (fun x : A => negb (p x)) (dropWhile p l) =
    negb (isEmpty (dropWhile p l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; cbn.
      rewrite IHt. reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma any_takeWhile_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    any p l = orb (any p (takeWhile p l)) (any p (dropWhile p l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; cbn; reflexivity.
Qed.
(* end hide *)

Lemma all_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p (takeWhile p l) = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; cbn; trivial.
Qed.
(* end hide *)

Lemma all_takeWhile' :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p l = true -> takeWhile p l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn in *.
      rewrite IHt; trivial.
      congruence.
Qed.
(* end hide *)

Lemma all_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p (dropWhile p l) = all p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; cbn.
      assumption.
      reflexivity.
Qed.
(* end hide *)

Lemma takeWhile_app_all :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    all p l1 = true -> takeWhile p (l1 ++ l2) = l1 ++ takeWhile p l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h); cbn in *.
      rewrite IHt; trivial.
      inversion H.
Qed.
(* end hide *)

Lemma removeFirst_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p (takeWhile p l) =
    match takeWhile p l with
        | [] => None
        | h :: t => Some (h, t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; reflexivity.
Qed.
(* end hide *)

Lemma removeLast_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p (dropWhile (fun x : A => negb (p x)) l) =
    match dropWhile (fun x : A => negb (p x)) l with
        | [] => None
        | h :: t => Some (h, t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph.
      reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma findIndex_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (n m : nat),
    findIndex p (takeWhile p l) = Some n ->
      findIndex p l = Some n -> n <= m.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intros; repeat (cbn in *; rewrite ?H1 in *).
      inversion H0. apply le_0_n.
      inversion H.
Qed.
(* end hide *)

Lemma findIndex_spec' :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n ->
      takeWhile (fun x : A => negb (p x)) l = take n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h); cbn.
      inv H. cbn. reflexivity.
      destruct (findIndex p t); inv H.
        cbn. f_equal. apply IHt. reflexivity.
Qed.
(* end hide *)

Lemma findIndex_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (n m : nat),
    findIndex p (dropWhile p l) = Some m ->
      findIndex p l = Some n -> n <= m.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intros; repeat (cbn in *; rewrite ?H1 in *).
      inversion H0. apply le_0_n.
      rewrite H in H0. inversion H0. apply le_n.
Qed.
(* end hide *)

Lemma count_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p (takeWhile p l) = length (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite Hph, IHt. reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma count_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p (dropWhile p l) <= count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply le_0_n.
    destruct (p h) eqn: Hph; cbn.
      apply le_S, IHt.
      rewrite Hph. reflexivity.
Qed.
(* end hide *)

Lemma count_takeWhile_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p (takeWhile p l) + count p (dropWhile p l) = count p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite Hph.
      rewrite <- IHt. cbn. reflexivity.
      reflexivity.
Restart.
  intros. rewrite <- (takeWhile_dropWhile_spec A p l) at 3.
  rewrite count_app. reflexivity.
Qed.
(* end hide *)

(** ** [span] *)

(** Zdefiniuj funkcję [span], która dzieli listę [l] na listę [b], której
    elementy nie spełniają predykatu [p], element [x], który spełnia [p]
    oraz listę [e] zawierającą resztę elementów [l]. Jeżeli na liście nie
    ma elementu spełniającego [p], funkcja zwraca [None].

    Przykład:
*)

(** [span even [1; 1; 2; 3; 5; 8]] = [Some ([1; 1], 2, [3; 5; 8])] *)

(** [span even [1; 3; 5]] = [None] *)

(* begin hide *)
Fixpoint span
  {A : Type} (p : A -> bool) (l : list A) : option (list A * A * list A) :=
match l with
    | [] => None
    | h :: t =>
        if p h
        then Some ([], h, t)
        else
          match span p t with
              | None => None
              | Some (b, x, e) => Some (h :: b, x, e)
          end
end.

Lemma span_spec :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) -> l = b ++ x :: e.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (span p t).
        destruct p0, p0. inv H. cbn. f_equal. apply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma isEmpty_span :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    inv H.
    reflexivity.
Qed.
(* end hide *)

Lemma length_span :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) -> length b + length e < length l.
(* begin hide *)
Proof.
  intros. apply span_spec in H. subst. rewrite length_app. cbn.
  rewrite <- plus_n_Sm. apply le_n.
Qed.
(* end hide *)

Lemma length_span' :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      length b < length l /\
      length e < length l.
(* begin hide *)
Proof.
  intros. apply length_span in H. lia.
Qed.
(* end hide *)

Lemma span_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    span p (snoc x l) =
    match span p l with
        | None => if p x then Some (l, x, []) else None
        | Some (b, y, e) => Some (b, y, snoc x e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h).
      reflexivity.
      rewrite IHt. destruct (span p t).
        destruct p0, p0. reflexivity.
        destruct (p x); reflexivity.
Qed.
(* end hide *)

Lemma span_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    span p (l1 ++ l2) =
    match span p l1, span p l2 with
        | Some (b, x, e), _ => Some (b, x, e ++ l2)
        | _, Some (b, x, e) => Some (l1 ++ b, x, e)
        | _, _ => None
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct (span p l2).
      destruct p0, p0. 1-2: reflexivity.
    destruct (p h).
      reflexivity.
      rewrite IHt. destruct (span p t).
        destruct p0, p0. reflexivity.
        destruct (span p l2).
          destruct p0, p0. all: reflexivity.
Qed.
(* end hide *)

Lemma span_map :
  forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
    span p (map f l) =
    match span (fun x : A => p (f x)) l with
        | None => None
        | Some (b, x, e) => Some (map f b, f x, map f e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p (f h)).
      reflexivity.
      rewrite IHt. destruct (span _ t).
        destruct p0, p0. cbn. all: reflexivity.
Qed.
(* end hide *)

Lemma span_join :
  forall (A : Type) (p : A -> bool) (lla : list (list A)),
    span p (join lla) =
    match span (any p) lla with
        | None => None
        | Some (bl, l, el) =>
            match span p l with
                | None => None
                | Some (b, x, e) => Some (join bl ++ b, x, e ++ join el)
            end
    end.
(* begin hide *)
Proof.
  induction lla as [| hl tl]; cbn.
    reflexivity.
    rewrite span_app, IHtl. induction hl as [| h t]; cbn.
      destruct (span (any p) tl).
        destruct p0, p0. destruct (span p l1).
          destruct p0, p0. 1-3: reflexivity.
      destruct (p h) eqn: Hph; cbn.
        rewrite Hph. reflexivity.
        destruct (span p t).
          destruct p0, p0. destruct (any p t); cbn.
            rewrite Hph. destruct (span p t).
              destruct p0, p0. inv IHt. reflexivity.
              inv IHt.
            destruct (span (any p) tl).
              destruct p0, p0. destruct (span p l3).
                destruct p0, p0. inv IHt. cbn. reflexivity.
                inv IHt.
              inv IHt.
          destruct (span (any p) tl).
            destruct p0, p0. destruct (span p l1).
              destruct p0, p0. destruct (any p t).
                cbn. rewrite Hph. destruct (span p t).
                  destruct p0, p0. inv IHt. reflexivity.
                  inv IHt.
                destruct (span p l1).
                  destruct p0, p0. inv IHt. cbn. rewrite H0. reflexivity.
                  inv IHt.
              destruct (any p t).
                cbn. rewrite Hph. destruct (span p t).
                  destruct p0, p0. inv IHt.
                  reflexivity.
                destruct (span p l1).
                  destruct p0, p0. inv IHt.
                  reflexivity.
            destruct (any p t).
              cbn. rewrite Hph. destruct (span p t).
                destruct p0, p0. inv IHt.
                1-2: reflexivity.
Restart.
  Ltac rec_destr x :=
  match x with
      | context [match ?y with _ => _ end] => rec_destr y
      | _ => let H := fresh "H" in destruct x eqn: H
  end.
  induction lla as [| hl tl]; cbn.
    reflexivity.
    rewrite span_app, IHtl. induction hl as [| h t]; cbn.
      all: repeat (match goal with
          | H : context [match ?x with _ => _ end] |- _ => rec_destr x
          | |- context [match ?x with _ => _ end] => rec_destr x
      end; cbn in *); try congruence.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: span vs bind *)
(* end hide *)

Lemma span_replicate :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    span p (replicate n x) =
    if andb (1 <=? n) (p x)
    then Some ([], x, replicate (n - 1) x)
    else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct (p x) eqn: Hpx.
      rewrite <- minus_n_O. reflexivity.
      rewrite IHn'. cbn. destruct n'; cbn; rewrite ?Hpx; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: span vs iterate *)
(* end hide *)

Lemma span_any :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) -> any p l = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      reflexivity.
      destruct (span p t).
        destruct p0, p0. inv H. eapply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma span_all :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      all p l = andb (beq_nat (length b) 0) (all p e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. cbn. reflexivity.
      destruct (span p t).
        destruct p0, p0. all: inv H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma span_find :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) -> find p l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. reflexivity.
      destruct (span p t).
        destruct p0, p0. all: inv H. eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma span_removeFirst :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      removeFirst p l = Some (x, b ++ e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. cbn. reflexivity.
      destruct (span p t).
        destruct p0, p0. all: inv H. erewrite IHt; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: span vs findIndex *)
(* end hide *)

Lemma count_span_l :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) -> count p b = 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (span p t).
        destruct p0, p0. all: inv H. cbn. rewrite Hph.
          eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma count_span_r :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      count p e < length l - length b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. cbn. apply le_n_S. apply count_length.
      destruct (span p t).
        destruct p0, p0. all: inv H. cbn. apply IHt. reflexivity.
Qed.
(* end hide *)

Lemma span_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    span p (filter p l) =
    match filter p l with
        | [] => None
        | h :: t => Some ([], h, t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite Hph. reflexivity.
      apply IHt.
Qed.
(* end hide *)

Lemma filter_span_l :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) -> filter p b = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      inv H. cbn. reflexivity.
      destruct (span p t).
        destruct p0, p0. all: inv H. cbn. rewrite Hph.
          eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma takeWhile_span :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      takeWhile (fun x : A => negb (p x)) l = b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. reflexivity.
      destruct (span p t).
        destruct p0, p0. all: inv H. f_equal. eapply IHt. reflexivity.
Qed.
(* end hide *)

Lemma dropWhile_span :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      dropWhile (fun x : A => negb (p x)) l = x :: e.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h); cbn.
      inv H. reflexivity.
      destruct (span p t).
        destruct p0, p0. all: inv H. eapply IHt. reflexivity.
Qed.
(* end hide *)

(** *** Związki [span] i [rev] *)

(** Zdefiniuj funkcję [naps], która działa tak jak [span], tyle że
    "od tyłu". Udowodnij twierdzenie [span_rev]. *)

(* begin hide *)
Fixpoint naps
  {A : Type} (p : A -> bool) (l : list A) : option (list A * A * list A) :=
match l with
    | [] => None
    | h :: t =>
        match naps p t with
            | None => if p h then Some ([], h, t) else None
            | Some (b, x, e) => Some (h :: b, x, e)
        end
end.
(* end hide *)

(* begin hide *)
Lemma naps_snoc' :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    naps p (l ++ [x]) =
    if p x
    then Some (l, x, [])
    else
      match naps p l with
          | None => None
          | Some (b, y, e) => Some (b, y, e ++ [x])
      end.
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. destruct (p x) eqn: Hpx.
      reflexivity.
      destruct (naps p t) eqn: Heq.
        destruct p0, p0. reflexivity.
        destruct (p h); reflexivity.
Qed.
(* end hide *)

Lemma span_rev_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    span p l =
    match naps p (rev l) with
        | None => None
        | Some (b, x, e) => Some (rev e, x, rev b)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn.
      rewrite naps_snoc', Hph, rev_inv. cbn. reflexivity.
      rewrite naps_snoc', Hph, IHt. destruct (naps p (rev t)).
        destruct p0, p0. rewrite rev_app. cbn. all: reflexivity.
Qed.
(* end hide *)

Lemma span_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    span p (rev l) =
    match naps p l with
        | None => None
        | Some (b, x, e) => Some (rev e, x, rev b)
    end.
(* begin hide *)
Proof.
  intros. rewrite span_rev_aux, rev_inv. reflexivity.
Qed.
(* end hide *)

(** * Sekcja mocno ad hoc *)

(** ** [pmap] *)

(** Zdefiniuj funkcję [pmap], która mapuje funkcję [f : A -> option B]
    po liście [l], ale odpakowuje wyniki zawinięte w [Some], a wyniki
    równe [None] usuwa.

    Przykład:
*)

(** [pmap (fun n : nat => if even n then None else Some (n + 42)) [1; 2; 3]]
    = [[43; 45]] *)

(* begin hide *)
Fixpoint pmap {A B : Type} (f : A -> option B) (l : list A) : list B :=
match l with
    | [] => []
    | h :: t =>
        match f h with
            | None => pmap f t
            | Some x => x :: pmap f t
        end
end.
(* end hide *)

Lemma isEmpty_pmap_false :
  forall (A B : Type) (f : A -> option B) (l : list A),
    isEmpty (pmap f l) = false -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    assumption.
    reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_pmap_true :
  forall (A B : Type) (f : A -> option B) (l : list A),
    isEmpty l = true -> isEmpty (pmap f l) = true.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma length_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    length (pmap f l) <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply le_0_n.
    destruct (f h); cbn.
      apply le_n_S. assumption.
      apply le_S. assumption.
Qed.
(* end hide *)

Lemma pmap_snoc :
  forall (A B : Type) (f : A -> option B) (a : A) (l : list A),
    pmap f (snoc a l) =
    match f a with
        | None => pmap f l
        | Some b => snoc b (pmap f l)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (f h), (f a); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_app :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    pmap f (l1 ++ l2) = pmap f l1 ++ pmap f l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_rev :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f (rev l) = rev (pmap f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_app. cbn. destruct (f h); cbn; rewrite ?IHt, ?app_nil_r.
      all: reflexivity.
Qed.
(* end hide *)

Lemma pmap_map :
  forall (A B C : Type) (f : A -> B) (g : B -> option C) (l : list A),
    pmap g (map f l) = pmap (fun x : A => g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (g (f h)); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_join :
  forall (A B : Type) (f : A -> option B) (l : list (list A)),
    pmap f (join l) = join (map (pmap f) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_app. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma pmap_bind :
  forall (A B C : Type) (f : A -> list B) (g : B -> option C) (l : list A),
    pmap g (bind f l) = bind (fun x : A => pmap g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_app. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma pmap_replicate :
  forall (A B : Type) (f : A -> option B) (n : nat) (x : A),
    pmap f (replicate n x) =
    match f x with
        | None => []
        | Some y => replicate n y
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct (f x); reflexivity.
    rewrite IHn'. destruct (f x); reflexivity.
Qed.
(* end hide *)

Definition isSome {A : Type} (x : option A) : bool :=
match x with
    | None => false
    | _ => true
end.

Lemma head_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    head (pmap f l) =
    match find isSome (map f l) with
        | None => None
        | Some x => x
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_zip :
  exists
    (A B C : Type)
    (fa : A -> option C) (fb : B -> option C)
    (la : list A) (lb : list B),
      pmap
        (fun '(a, b) =>
        match fa a, fb b with
            | Some a', Some b' => Some (a', b')
            | _, _ => None
        end)
        (zip la lb) <>
      zip (pmap fa la) (pmap fb lb).
(* begin hide *)
Proof.
  exists
    bool, bool, bool,
    (fun b : bool => if b then Some b else None),
    (fun b : bool => if b then None else Some b),
    [true; true; false], [true; false; false].
  cbn. inversion 1.
Qed.
(* end hide *)

Lemma any_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    any p (pmap f l) =
    any
      (fun x : A =>
      match f x with
          | Some b => p b
          | None => false
      end)
      l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma all_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    all p (pmap f l) =
    all
      (fun x : A =>
      match f x with
          | Some b => p b
          | None => true
      end)
      l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma find_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    find p (pmap f l) =
    let oa :=
      find (fun x : A => match f x with Some b => p b | _ => false end) l
    in
    match oa with
        | Some a => f a
        | None => None
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Heq; cbn.
      destruct (p b); cbn.
        symmetry. assumption.
        destruct (find _ t); cbn in *; assumption.
      destruct (find _ t); cbn in *; assumption.
Qed.
(* end hide *)

Lemma findLast_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    findLast p (pmap f l) =
    let oa :=
      findLast
        (fun x : A => match f x with Some b => p b | _ => false end) l
    in
    match oa with
        | Some a => f a
        | None => None
    end.
(* begin hide *)
Proof.
  intros. rewrite <- ?find_rev, <- pmap_rev, find_pmap. reflexivity.
Qed.
(* end hide *)

Lemma count_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    count p (pmap f l) =
    count
      (fun x : A =>
      match f x with
          | Some b => p b
          | None => false
      end)
      l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: higiena dla pmap_filter i jego aux *)
(* end hide *)

Definition aux {A B : Type} (p : B -> bool) (f : A -> option B)
  (dflt : bool) (x : A) : bool :=
match f x with
    | Some b => p b
    | None => dflt
end.

Lemma pmap_filter :
  forall (A B : Type) (p : B -> bool) (f : A -> option B) (l : list A),
    filter p (pmap f l) =
    pmap f (filter (aux p f false) l).
(* begin hide *)
Proof.
unfold aux.  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Hfh; cbn; rewrite ?IHt.
      destruct (p b); cbn; rewrite ?Hfh; reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma pmap_takeWhile :
  forall (A B : Type) (p : B -> bool) (f : A -> option B) (l : list A),
    takeWhile p (pmap f l) =
    pmap f
      (takeWhile
        (fun x : A => match f x with | Some b => p b | _ => true end)
        l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Hfh; cbn; rewrite ?Hfh, ?IHt.
      destruct (p b); cbn; rewrite ?Hfh; reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma pmap_dropWhile :
  forall (A B : Type) (p : B -> bool) (f : A -> option B) (l : list A),
    dropWhile p (pmap f l) =
    pmap f
      (dropWhile
        (fun x : A => match f x with | Some b => p b | _ => true end)
        l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Hfh; cbn; rewrite ?Hfh, ?IHt.
      destruct (p b); cbn; rewrite ?Hfh; reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma pmap_span :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    match
      span
        (fun x : A => match f x with None => false | Some b => p b end)
        l
    with
        | None => True
        | Some (b, x, e) =>
            exists y : B, f x = Some y /\
              span p (pmap f l) = Some (pmap f b, y, pmap f e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    destruct (f h) eqn: Heq.
      destruct (p b) eqn: Hpb; cbn; rewrite ?Hpb.
        exists b. split; trivial.
        destruct (span _ t); trivial.
          destruct p0, p0; cbn in *.
            destruct IHt as (y & IH1 & IH2).
              exists y. rewrite IH1, IH2, Heq. split; reflexivity.
      destruct (span _ t); trivial.
        destruct p0, p0, IHt as (y & IH1 & IH2).
          exists y. cbn. rewrite IH1, IH2, Heq. split; reflexivity.
Qed.
(* end hide *)

Lemma pmap_nth_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    pmap (fun n : nat => nth n l) (findIndices p l) =
    filter p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn; rewrite pmap_map, IHt; reflexivity.
Qed.
(* end hide *)

(** * Bardziej skomplikowane funkcje *)

(** ** [intersperse] *)

(** Zdefiniuj funkcję [intersperse], który wstawia element [x : A] między
    każde dwa elementy z listy [l : list A]. Zastanów się dobrze nad
    przypadkami bazowymi.

    Przykład:
*)

(** [intersperse 42 [1; 2; 3]] = [[1; 42; 2; 42; 3]] *)

(* begin hide *)
Function intersperse {A : Type} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t =>
        match intersperse x t with
            | [] => [h]
            | h' :: t' => h :: x :: h' :: t'
        end
end.
(* end hide *)

Lemma isEmpty_intersperse :
  forall (A : Type) (x : A) (l : list A),
    isEmpty (intersperse x l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma length_intersperse :
  forall (A : Type) (x : A) (l : list A),
    length (intersperse x l) = 2 * length l - 1.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; cbn in *.
    1-2: reflexivity.
    destruct (intersperse x t); cbn in *.
      rewrite <- minus_n_O, plus_0_r, <- ?plus_n_Sm in *.
        destruct t; inversion IHl. cbn. reflexivity.
      rewrite IHl. rewrite <- ?plus_n_Sm. rewrite <- minus_n_O.
        reflexivity.
Qed.
(* end hide *)

Lemma intersperse_snoc :
  forall (A : Type) (x y : A) (l : list A),
    intersperse x (snoc y l) =
    if isEmpty l then [y] else snoc y (snoc x (intersperse x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct t; cbn.
      reflexivity.
      destruct (intersperse x t); cbn; reflexivity.
Qed.
(* end hide *)

Lemma intersperse_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    intersperse x (l1 ++ l2) =
    match l1, l2 with
        | [], _ => intersperse x l2
        | _, [] => intersperse x l1
        | h1 :: t1, h2 :: t2 =>
            intersperse x l1 ++ x :: intersperse x l2
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. destruct t, l2; cbn.
      1,3: reflexivity.
      destruct (intersperse x l2); reflexivity.
      destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma intersperse_app_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    l1 <> [] -> l2 <> [] ->
      intersperse x (l1 ++ l2) = intersperse x l1 ++ x :: intersperse x l2.
(* begin hide *)
Proof.
  intros. rewrite intersperse_app. destruct l1.
    contradiction.
    destruct l2.
      contradiction.
      reflexivity.
Qed.
(* end hide *)

Lemma intersperse_rev :
  forall (A : Type) (x : A) (l : list A),
    intersperse x (rev l) = rev (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite intersperse_app. destruct (rev t) eqn: Heq.
      apply (f_equal rev) in Heq. rewrite rev_inv in Heq.
        cbn in Heq. rewrite Heq. cbn. reflexivity.
      rewrite IHt. destruct (intersperse x t); cbn.
        cbn in IHt. destruct (intersperse x l); inversion IHt.
        rewrite <- ?app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma intersperse_map :
  forall (A B : Type) (f : A -> B) (l : list A) (a : A) (b : B),
    f a = b -> intersperse b (map f l) = map f (intersperse a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite (IHt _ _ H). destruct (intersperse a t); cbn.
      reflexivity.
      rewrite H. reflexivity.
Qed.
(* end hide *)

Lemma head_intersperse :
  forall (A : Type) (x : A) (l : list A),
    head (intersperse x l) = head l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma last_intersperse :
  forall (A : Type) (x : A) (l : list A),
    last (intersperse x l) = last l.
(* begin hide *)
Proof.
  intros. pose (H := intersperse_rev _ x (rev l)).
  rewrite rev_inv in H.
  rewrite H, last_rev, head_intersperse, head_rev.
  reflexivity.
Qed.
(* end hide *)

Lemma tail_intersperse :
  forall (A : Type) (x : A) (l : list A),
    tail (intersperse x l) =
    match tail l with
        | None => None
        | Some [] => Some []
        | Some (h :: t) => tail (intersperse x l)
    end.
(* begin hide *)
Proof.
  intros A x l. functional induction @intersperse A x l; cbn.
    reflexivity.
    destruct t; reflexivity.
    destruct t; cbn in *.
      inv e0.
      reflexivity.
Qed.
(* end hide *)

Lemma nth_intersperse_even :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l ->
      nth (2 * n) (intersperse x l) = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      destruct (intersperse x t); reflexivity.
      destruct (intersperse x t).
        cbn. destruct t; cbn in *.
          reflexivity.
          apply lt_S_n in H. specialize (IHt _ H).
            destruct n'; cbn in *; inversion IHt.
              reflexivity.
        rewrite <- plus_n_Sm. cbn. rewrite <- IHt.
          cbn. reflexivity.
          apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_intersperse_odd :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    0 < n -> n < length l ->
      nth (2 * n - 1) (intersperse x l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H0.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        destruct n; cbn in *.
          inversion H.
          destruct n; cbn in *.
            inversion H0. inversion H2.
            inversion H0. inversion H2.
        destruct (intersperse x t); inversion Heq.
      destruct t; cbn in *.
        inversion Heq.
        destruct n as [| n']; cbn.
          inversion H.
          destruct n' as [| n'']; cbn.
            reflexivity.
            rewrite <- IHt with (S n'').
              cbn. rewrite <- ?plus_n_Sm, <- minus_n_O, ?plus_0_r.
                cbn. reflexivity.
              apply le_n_S, le_0_n.
              apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma intersperse_take :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    intersperse x (take n l) =
    take (2 * n - 1) (intersperse x l).
(* begin hide *)
Proof.
  intros A x l. functional induction @intersperse A x l; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite <- plus_n_Sm. cbn. destruct t; cbn in *.
        reflexivity.
        destruct (intersperse x t); inv e0.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite <- plus_n_Sm, IHl0. destruct n' as [| n'']; cbn.
        rewrite take_0. reflexivity.
        rewrite <- plus_n_Sm, plus_0_r. cbn. destruct t; cbn in *.
          inv e0.
          destruct (intersperse x t); inv e0; reflexivity.
Qed.
(* end hide *)

Lemma any_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    any p (intersperse x l) =
    orb (any p l) (andb (2 <=? length l) (p x)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn.
      destruct t; cbn in *.
        rewrite ?Bool.orb_false_r. reflexivity.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t) eqn: Heq'; inv Heq.
          destruct t; cbn in *.
            rewrite ?Bool.orb_false_r.
              destruct (p h), (p a), (p x); reflexivity.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (any p t);
              reflexivity.
          destruct t; cbn in *.
            inv Heq'.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (any p t);
              reflexivity.
Qed.
(* end hide *)

Lemma all_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all p (intersperse x l) =
    all p l && ((length l <=? 1) || p x).
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn in *.
    reflexivity.
    destruct t; cbn in *.
      rewrite ?Bool.andb_true_r. reflexivity.
      rewrite e0 in *. cbn in *. destruct t; cbn in *.
        inversion e0.
        rewrite IHl0. rewrite Bool.andb_assoc. reflexivity.
    rewrite e0 in *. cbn in *. rewrite IHl0. destruct t; cbn.
      inversion e0.
      destruct t; cbn.
        rewrite ?Bool.andb_true_r.
          destruct (p h), (p x), (p a); reflexivity.
        destruct (p h), (p x), (p a), (p a0), (all p t); reflexivity.
Restart.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn.
      destruct t; cbn in *.
        rewrite ?Bool.andb_true_r. reflexivity.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t) eqn: Heq'; inv Heq.
          destruct t; cbn in *.
            rewrite ?Bool.andb_true_r.
              destruct (p h), (p a), (p x); reflexivity.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (all p t);
              reflexivity.
          destruct t; cbn in *.
            inv Heq'.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (all p t);
              reflexivity.
Qed.
(* end hide *)

Lemma findIndex_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    findIndex p (intersperse x l) =
    if p x
    then
      match l with
          | [] => None
          | [h] => if p h then Some 0 else None
          | h :: t => if p h then Some 0 else Some 1
      end
    else
      match findIndex p l with
          | None => None
          | Some n => Some (2 * n)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct (p x); reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn in *.
      destruct t; cbn in *.
        destruct (p h), (p x); reflexivity.
        destruct (intersperse x t); inversion Heq.
      destruct (p h), (p x), (p a) eqn: Hpa, t;
      cbn in *; try reflexivity; try inversion Heq.
        destruct (p a0); cbn.
          reflexivity.
          destruct (findIndex p t); inversion IHt.
        destruct (findIndex p l); cbn in *.
          destruct (intersperse x t); inversion Heq; subst.
            rewrite Hpa in *. destruct (findIndex p t).
              inversion IHt; cbn. f_equal. lia.
              inversion IHt.
            rewrite Hpa in *.
              destruct (findIndex p t); inversion IHt.
                f_equal. lia.
          destruct (intersperse x t); inversion Heq; subst;
          rewrite Hpa in *.
            destruct (findIndex p t); inversion IHt. reflexivity.
            destruct (findIndex p t); inversion IHt. reflexivity.
Qed.
(* end hide *)

Lemma count_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    count p (intersperse x l) =
    count p l + if p x then length l - 1 else 0.
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn.
    destruct (p x); reflexivity.
    destruct t; cbn in *.
      rewrite <- IHl0, plus_0_r. reflexivity.
      destruct (intersperse x t); inv e0.
    rewrite e0 in IHl0. cbn in IHl0.
      destruct (p x), (p h), (p h'); rewrite IHl0; try lia.
        1-4: destruct t; inv e0; cbn; destruct (p a); lia.
Qed.
(* end hide *)

Lemma filter_intersperse_false :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = false -> filter p (intersperse x l) = filter p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite <- (IHt H). destruct (intersperse x t); cbn in *.
      destruct (p h); reflexivity.
      destruct (p h), (p x), (p a); congruence.
Qed.
(* end hide *)

Lemma pmap_intersperse :
  forall (A B : Type) (f : A -> option B) (x : A) (l : list A),
    f x = None -> pmap f (intersperse x l) = pmap f l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (intersperse x t); cbn.
      rewrite <- (IHt H). cbn. reflexivity.
      rewrite H, <- (IHt H). destruct (f h); cbn; destruct (f a); reflexivity.
Qed.
(* end hide *)

(** * Proste predykaty *)

(** ** [elem] *)

(** Zdefiniuj induktywny predykat [elem]. [elem x l] jest spełniony, gdy
    [x] jest elementem listy [l]. *)

(* begin hide *)
Inductive elem {A : Type} : A -> list A -> Prop :=
    | elem_head : forall (x : A) (l : list A),
        elem x (x :: l)
    | elem_cons : forall (x h : A) (t : list A),
        elem x t -> elem x (h :: t).
(* end hide *)

Lemma elem_not_nil :
  forall (A : Type) (x : A), ~ elem x [].
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma elem_not_cons :
  forall (A : Type) (x h : A) (t : list A),
    ~ elem x (h :: t) -> x <> h /\ ~ elem x t.
(* begin hide *)
Proof.
  split; intro; apply H; subst; constructor; auto.
Qed.
(* end hide *)

Lemma elem_cons' :
  forall (A : Type) (x h : A) (t : list A),
    elem x (h :: t) <-> x = h \/ elem x t.
(* begin hide *)
Proof.
  split; (inversion 1; subst; [left | right]; trivial).
Qed.
(* end hide *)

Lemma elem_snoc :
  forall (A : Type) (x y : A) (l : list A),
    elem x (snoc y l) <-> elem x l \/ x = y.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros; inversion H; subst; clear H.
      right. reflexivity.
      inversion H2.
      do 2 left.
      destruct (IHt H2).
        left. right. assumption.
        right. assumption.
    destruct 1; subst.
      induction H; cbn.
        left.
        right. assumption.
      induction l as [| h t]; cbn.
        left.
        right. assumption.
Qed.
(* end hide *)

Lemma elem_app_l :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l1 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    constructor. assumption.
Qed.
(* end hide *)

Lemma elem_app_r :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma elem_or_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l1 \/ elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  destruct 1; [apply elem_app_l | apply elem_app_r]; assumption.
Qed.
(* end hide *)

Lemma elem_app_or :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x (l1 ++ l2) -> elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    right. assumption.
    inversion H; subst.
      left. constructor.
      destruct (IHt1 _ H2).
        left. constructor. assumption.
        right. assumption.
Qed.
(* end hide *)

Lemma elem_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x (l1 ++ l2) <-> elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  split; intros; [apply elem_app_or | apply elem_or_app]; assumption.
Qed.
(* end hide *)

Lemma elem_spec :
  forall (A : Type) (x : A) (l : list A),
    elem x l <-> exists l1 l2 : list A, l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      exists [], l. cbn. reflexivity.
      destruct IHelem as [l1 [l2 IH]].
        exists (h :: l1), l2. rewrite IH. cbn. reflexivity.
    destruct 1 as [l1 [l2 ->]]. apply elem_app_r. constructor.
Qed.
(* end hide *)

Lemma elem_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    elem x l -> elem (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; inversion 1; subst.
    constructor.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma elem_map_conv :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    elem y (map f l) <-> exists x : A, f x = y /\ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      inversion H; subst.
        exists h. split; trivial. constructor.
        destruct (IHt H2) as [x [Hx1 Hx2]]. exists x.
          split; trivial. constructor. assumption.
    destruct 1 as [x [<- H2]]. apply elem_map, H2.
Qed.
(* end hide *)

Lemma elem_map_conv' :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    (forall x y : A, f x = f y -> x = y) ->
      elem (f x) (map f l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; inversion 2; subst.
    specialize (H _ _ H3). subst. constructor.
    constructor. apply IHt; assumption.
Qed.
(* end hide *)

Lemma map_ext_elem :
  forall (A B : Type) (f g : A -> B) (l : list A),
    (forall x : A, elem x l -> f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite H, IHt.
      trivial.
      intros. apply H. constructor. assumption.
      constructor.
Qed.
(* end hide *)

Lemma elem_join :
  forall (A : Type) (x : A) (ll : list (list A)),
    elem x (join ll) <-> exists l : list A, elem x l /\ elem l ll.
(* begin hide *)
Proof.
  split.
    induction ll as [| h t]; cbn; intros.
      inversion H.
      rewrite elem_app in H. destruct H.
        exists h. split; try left; assumption.
        destruct (IHt H) as [l [H1 H2]].
          exists l. split; try right; assumption.
    destruct 1 as [l [H1 H2]]. induction H2; cbn.
      apply elem_app_l. assumption.
      apply elem_app_r, IHelem, H1.
Qed.
(* end hide *)

Lemma elem_replicate :
  forall (A : Type) (n : nat) (x y : A),
    elem y (replicate n x) <-> n <> 0 /\ x = y.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; inversion 1; subst.
      split; auto.
      destruct (IHn' H2). auto.
    intros [H H']. rewrite H'. destruct n as [| n'].
      contradiction H. trivial.
      cbn. left.
Qed.
(* end hide *)

Lemma nth_elem :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A, nth n l = Some x /\ elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      exists h. split; constructor.
      destruct (IHt _ (lt_S_n _ _ H)) as (x & IH1 & IH2).
        exists x. split; try right; assumption.
Qed.
(* end hide *)

(* TOOD: ulepszyć? *) Lemma iff_elem_nth :
  forall (A : Type) (x : A) (l : list A),
    elem x l <-> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  split.
    induction 1.
      exists 0. cbn. reflexivity.
      destruct IHelem as (n & IH). exists (S n). cbn. assumption.
    destruct 1 as (n & H). revert n H.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. left.
        right. apply (IHt _ H).
Qed.
(* end hide *)

Lemma elem_rev_aux :
  forall (A : Type) (x : A) (l : list A),
    elem x l -> elem x (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    inversion H; subst.
      apply elem_app_r. constructor.
      apply elem_app_l. apply IHt. assumption.
Qed.
(* end hide *)

Lemma elem_rev :
  forall (A : Type) (x : A) (l : list A),
    elem x (rev l) <-> elem x l.
(* begin hide *)
Proof.
  split; intro.
    apply elem_rev_aux in H. rewrite rev_inv in H. assumption.
    apply elem_rev_aux, H.
Qed.
(* end hide *)

Lemma elem_remove_nth :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    elem x l -> nth n l <> Some x ->
    match remove n l with
        | None => True
        | Some (_, l') => elem x l'
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n']; cbn in *; inv H.
      contradiction.
      assumption.
      destruct (remove n' t).
        destruct p. left.
        trivial.
      specialize (IHt _ H3 H0). destruct (remove n' t).
        destruct p. right. assumption.
        trivial.
Qed.
(* end hide *)

Lemma elem_take :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    elem x (take n l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; inversion H; subst; clear H.
      left.
      right. apply (IHt _ _ H2).
Qed.
(* end hide *)

Lemma elem_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    elem x (drop n l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n'].
      assumption.
      right. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma elem_splitAt' :
  forall (A : Type) (l l1 l2 : list A) (n : nat) (x y : A),
    splitAt n l = Some (l1, y, l2) ->
      elem x l <-> x = y \/ elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  split.
    intro. revert l1 l2 n y H. induction H0; cbn; intros.
      destruct n as [| n'].
        inv H. left. reflexivity.
        destruct (splitAt n' l).
          destruct p, p. inv H. right. do 2 left.
          inv H.
      destruct n as [| n'].
        inv H. do 2 right. assumption.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. inv H. decompose [or] (IHelem _ _ _ _ Heq).
            left. assumption.
            right. left. right. assumption.
            do 2 right. assumption.
          inv H.
    revert l1 l2 n x y H. induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. decompose [or] H0; clear H0.
          subst. left.
          inv H1.
          right. assumption.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. inv H. specialize (IHt _ _ _ x _ Heq).
            decompose [or] H0; clear H0.
              right. apply IHt. left. assumption.
              inv H1.
                left.
                right. apply IHt. right. left. assumption.
              right. apply IHt. do 2 right. assumption.
              inv H.
Qed.
(* end hide *)

Lemma elem_insert :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    elem y (insert l n x) <-> x = y \/ elem y l.
(* begin hide *)
Proof.
  split.
    revert n x. induction l as [| h t]; cbn; intros.
      inv H.
        left. reflexivity.
        inv H2.
      destruct n as [| n'].
        rewrite ?elem_cons' in *.
          decompose [or] H; clear H; subst; firstorder.
        rewrite ?elem_cons' in *. firstorder.
    revert n. induction l as [| h t]; cbn; intros.
      destruct H; subst.
        constructor.
        inv H.
      destruct H, n as [| n']; subst.
        left.
        right. apply IHt. left. reflexivity.
        right. assumption.
        inv H.
          left.
          right. apply IHt. right. assumption.
Qed.
(* end hide *)

Lemma elem_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    replace l n x = Some l' ->
      elem y l' <-> elem y (take n l) \/ x = y \/ elem y (drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H. destruct (n <? length l).
    inv H. rewrite elem_app, elem_cons'. firstorder.
    inv H.
Qed.
(* end hide *)

Lemma elem_filter :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x (filter p l) <-> p x = true /\ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      case_eq (p h); intros; rewrite H0 in *.
        inversion H; subst; clear H.
          repeat constructor. assumption.
          destruct (IHt H3). firstorder constructor. assumption.
        destruct (IHt H). firstorder constructor. assumption.
    destruct 1. induction H0; cbn.
      rewrite H. constructor.
      destruct (p h).
        right. apply IHelem, H.
        apply IHelem, H.
Qed.
(* end hide *)

Lemma elem_filter_conv :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    elem x l <->
    elem x (filter p l) /\ p x = true \/
    elem x (filter (fun x : A => negb (p x)) l) /\ p x = false.
(* begin hide *)
Proof.
  split; rewrite ?elem_filter.
  destruct (p x). all: firstorder.
Qed.
(* end hide *)

Lemma elem_partition :
  forall (A : Type) (p : A -> bool) (x : A) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      elem x l <->
      (elem x l1 /\ p x = true) \/ (elem x l2 /\ p x = false).
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H. inversion H; subst; clear H.
  rewrite (elem_filter_conv _ p). reflexivity.
Qed.
(* end hide *)

Lemma elem_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x (takeWhile p l) -> elem x l /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intros; rewrite H0 in *.
      split.
        inversion H; subst; clear H.
          constructor.
          right. destruct (IHt _ H3). assumption.
        inversion H; subst; clear H.
          assumption.
          destruct (IHt _ H3). assumption.
      inversion H.
Qed.
(* end hide *)

Lemma elem_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x (dropWhile p l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intros; rewrite H0 in *.
      destruct (IHt _ H).
        right; left.
        right; right; assumption.
      assumption.
Qed.
(* end hide *)

Lemma elem_takeWhile_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x l <-> elem x (takeWhile p l) \/ elem x (dropWhile p l).
(* begin hide *)
Proof.
  split.
    intros. apply elem_app. rewrite takeWhile_dropWhile_spec. assumption.
    induction l as [| h t]; cbn.
      destruct 1; assumption.
      destruct (p h) eqn: Heq.
        destruct 1.
          inv H; [left | right]. apply IHt. left. assumption.
          right. apply IHt. right. assumption.
        destruct 1; inv H; [left | right]. assumption.
Qed.
(* end hide *)

Lemma elem_dropWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    elem x l -> ~ elem x (dropWhile p l) -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    case_eq (p h); intro.
      rewrite H1 in H0. inversion H; subst.
        assumption.
        apply IHt; assumption.
      rewrite H1 in H0. contradiction H.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: span vs intersperse, groupBy *)
(* end hide *)

Lemma span_spec' :
  forall (A : Type) (p : A -> bool) (l : list A),
    match span p l with
        | None => forall x : A, elem x l -> p x = false
        | Some (b, x, e) =>
            b = takeWhile (fun x : A => negb (p x)) l /\
            Some x = find p l /\
            x :: e = dropWhile (fun x : A => negb (p x)) l /\
            Some (x, b ++ e) = removeFirst p l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph; cbn.
      repeat split; reflexivity.
      destruct (span p t) eqn: Heq.
        destruct p0, p0. decompose [and] IHt; clear IHt.
          rewrite <- H3, ?H, H0. cbn. repeat split. assumption.
        intros. inv H.
          assumption.
          apply IHt. assumption.
Qed.
(* end hide *)

Lemma elem_span_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    span p l = None -> forall x : A, elem x l -> p x = false.
(* begin hide *)
Proof.
  induction 2; cbn in H.
    destruct (p x).
      inv H.
      reflexivity.
    destruct (p h).
      inv H.
      apply IHelem. destruct (span p t).
        destruct p0, p0. inv H.
        reflexivity.
Qed.
(* end hide *)

Lemma elem_span_Some :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) -> 
      forall y : A, elem y l <-> elem y b \/ y = x \/ elem y e.
(* begin hide *)
Proof.
  intros. apply span_spec in H.
  rewrite H, elem_app, elem_cons'. reflexivity.
Qed.
(* end hide *)

Lemma elem_span :
  forall (A : Type) (p : A -> bool) (l : list A),
    match span p l with
        | None => forall x : A, elem x l -> p x = false
        | Some (b, x, e) =>
            forall y : A, elem y l <-> elem y b \/ y = x \/ elem y e
    end.
(* begin hide *)
Proof.
  intros. destruct (span p l) eqn: Heq.
    destruct p0, p0. eapply elem_span_Some. eassumption.
    apply elem_span_None. assumption.
Qed.
(* end hide *)

Lemma elem_removeFirst_None :
  forall (A : Type) (p : A -> bool) (l : list A),
    removeFirst p l = None ->
      forall x : A, elem x l -> p x = false.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H0.
    destruct (p h) eqn: Hph.
      inv H.
      destruct (removeFirst p t) eqn: Heq.
        destruct p0. inv H.
        inv H0.
          assumption.
          apply IHt; [reflexivity | assumption].
Qed.
(* end hide *)

Lemma elem_zip :
  forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    elem (a, b) (zip la lb) -> elem a la /\ elem b lb.
(* begin hide *)
Proof.
  induction la; cbn.
    inversion 1.
    destruct lb; cbn; inversion 1; subst; cbn in *.
      split; constructor.
      destruct (IHla _ H2). split; right; assumption.
Qed.
(* end hide *)

Lemma zip_not_elem :
  exists (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    elem a la /\ elem b lb /\ ~ elem (a, b) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists true, false.
  exists [true; false], [true; false].
  cbn. repeat split.
    repeat constructor.
    repeat constructor.
    inversion 1; subst. inversion H2; subst. inversion H3.
Qed.
(* end hide *)

Lemma elem_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    elem n (findIndices p l) ->
      exists x : A, nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h) eqn: H'.
      inversion H; subst; clear H; cbn.
        exists h. split; trivial.
        destruct n as [| n']; cbn.
          exists h. split; trivial.
          rewrite elem_map_conv in H2. destruct H2 as (n'' & IH1 & IH2).
            destruct (IHt _ IH2) as (i & IH1' & IH2'). exists i.
              inversion IH1; subst. split; trivial.
      destruct n as [| n'].
        rewrite elem_map_conv in H. destruct H as [n [Hn _]].
          inversion Hn.
        rewrite elem_map_conv in H. destruct H as (n'' & H1 & H2).
          destruct (IHt _ H2) as (x & IH1 & IH2).
            inversion H1; subst; cbn. exists x. split; trivial.
Qed.
(* end hide *)

Lemma isEmpty_bind :
  forall (A B : Type) (f : A -> list B) (l : list A),
    isEmpty (bind f l) = true <->
    l = [] \/ l <> [] /\ forall x : A, elem x l -> f x = [].
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      left. reflexivity.
      right. destruct (f h) eqn: Hfh; cbn in *.
        destruct (IHt H); subst.
          split; inversion 1; subst.
            assumption.
            inversion H3.
          destruct H0. split; inversion 1; subst.
            assumption.
            apply H1. assumption.
        inversion H.
    destruct 1 as [H | [H1 H2]]; subst.
      cbn. reflexivity.
      induction l as [| h t]; cbn.
        contradiction H1. reflexivity.
        destruct t as [| h' t']; cbn in *.
          rewrite app_nil_r. rewrite (H2 h).
            cbn. reflexivity.
            constructor.
          rewrite isEmpty_app, (H2 h); cbn.
            apply IHt.
              inversion 1.
              inversion 1; subst.
                apply H2. do 2 constructor.
                apply H2. do 2 constructor. assumption.
            constructor.
Qed.
(* end hide *)

Lemma elem_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A) (a : A) (b : B),
    f a = Some b -> elem a l -> elem b (pmap f l).
(* begin hide *)
Proof.
  induction 2; cbn.
    rewrite H. left.
    destruct (f h); try right; apply IHelem, H.
Qed.
(* end hide *)

Lemma elem_pmap' :
  forall (A B : Type) (f : A -> option B) (l : list A) (b : B),
    (exists a : A, elem a l /\ f a = Some b) -> elem b (pmap f l).
(* begin hide *)
Proof.
  destruct 1 as (a & H1 & H2). eapply elem_pmap; eauto.
Qed.
(* end hide *)

Lemma elem_pmap_conv :
  forall (A B : Type) (f : A -> option B) (l : list A) (b : B),
    elem b (pmap f l) -> exists a : A, elem a l /\ f a = Some b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (f h) eqn: Heq; cbn.
      inversion H; subst; clear H.
        exists h. split; [left | assumption].
        destruct (IHt _ H2) as (a & IH1 & IH2).
          exists a. split; try right; assumption.
      destruct (IHt _ H) as (a & IH1 & IH2).
        exists a. split; try right; assumption.
Qed.
(* end hide *)

Lemma elem_intersperse :
  forall (A : Type) (x y : A) (l : list A),
    elem x (intersperse y l) <-> elem x l \/ (x = y /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (intersperse y t) eqn : Heq.
        inversion H; subst.
          do 2 left.
          inversion H2.
        inversion H; subst.
          do 2 left.
          inversion H2; subst.
            destruct t; cbn in *.
              inversion Heq.
              right. split; trivial. lia.
            destruct (IHt H3).
              left. right. assumption.
              destruct H0. right. split; [assumption | lia].
    destruct 1.
      induction H; cbn.
        destruct (intersperse y l); left.
        destruct (intersperse y t).
          inversion IHelem.
          do 2 right. assumption.
      destruct H; subst. destruct l as [| h [| h' t]]; cbn.
        1-2: cbn in H0; lia.
        destruct (intersperse y t); cbn.
          right. left.
          right. left.
Qed.
(* end hide *)

(** ** [In] *)

(** Gratuluję, udało ci się zdefiniować predykat [elem] i dowieść wszystkich
    jego właściwości. To jednak nie koniec zabawy, gdyż predykaty możemy
    definiować nie tylko przez indukcję, ale także przez rekursję. Być może
    taki sposób definiowania jest nawet lepszy? Przyjrzyjmy się poniższej
    definicji — tak właśnie "bycie elementem" jest zdefiniowane w bibliotece
    standardowej. *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
match l with
    | [] => False
    | h :: t => x = h \/ In x t
end.

(** Powyższa definicja jest bardzo podobna do tej induktywnej. [In x]
    dla listy pustej redukuje się do [False], co oznacza, że w pustej
    liście nic nie ma, zaś dla listy mającej głowę i ogon redukuje się do
    zdania "[x] jest głową lub jest elementem ogona".

    Definicja taka ma swoje wady i zalety. Największą moim zdaniem wadą jest
    to, że nie możemy robić indukcji po dowodzie, gdyż dowód faktu [In x l]
    nie jest induktywny. Największą zaletą zaś jest fakt, że nie możemy robić
    indukcji po dowodzie — im mniej potencjalnych rzeczy, po których można
    robić indukcję, tym mniej zastanawiania się. Przekonajmy się zatem na
    własnej skórze, która definicja jest "lepsza". *)

Lemma In_elem :
  forall (A : Type) (x : A) (l : list A),
    In x l <-> elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct H.
        subst. left.
        right. apply IHt, H.
    induction 1.
      left. reflexivity.
      right. assumption.
Qed.
(* end hide *)

Lemma In_not_nil :
  forall (A : Type) (x : A), ~ In x [].
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma In_not_cons :
  forall (A : Type) (x h : A) (t : list A),
    ~ In x (h :: t) -> x <> h /\ ~ In x t.
(* begin hide *)
Proof.
  split; intro; apply H; [left | right]; assumption.
Qed.
(* end hide *)

Lemma In_cons :
  forall (A : Type) (x h : A) (t : list A),
    In x (h :: t) <-> x = h \/ In x t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma In_snoc :
  forall (A : Type) (x y : A) (l : list A),
    In x (snoc y l) <-> In x l \/ x = y.
(* begin hide *)
Proof.
  intros. rewrite ?In_elem. apply elem_snoc.
Qed.
(* end hide *)

Lemma In_app_l :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x l1 -> In x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    contradiction.
    destruct H; [left | right].
      assumption.
      apply IHt1, H.
Qed.
(* end hide *)

Lemma In_app_r :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x l2 -> In x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    assumption.
    right. apply IHt. assumption.
Qed.
(* end hide *)

Lemma In_or_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x l1 \/ In x l2 -> In x (l1 ++ l2).
(* begin hide *)
Proof.
  destruct 1; [apply In_app_l | apply In_app_r]; assumption.
Qed.
(* end hide *)

Lemma In_app_or :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x (l1 ++ l2) -> In x l1 \/ In x l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    right. assumption.
    destruct H.
      do 2 left. assumption.
      destruct (IHt1 _ H).
        left. right. assumption.
        right. assumption.
Qed.
(* end hide *)

Lemma In_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x (l1 ++ l2) <-> In x l1 \/ In x l2.
(* begin hide *)
Proof.
  split; intros; [apply In_app_or | apply In_or_app]; assumption.
Qed.
(* end hide *)

Lemma In_spec :
  forall (A : Type) (x : A) (l : list A),
    In x l <-> exists l1 l2 : list A, l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct H; subst.
        exists [], t. cbn. reflexivity.
        destruct (IHt H) as (l1 & l2 & IH); subst.
          exists (h :: l1), l2. cbn. reflexivity.
    destruct 1 as (l1 & l2 & H); subst.
      rewrite In_app. right. left. reflexivity.
Qed.
(* end hide *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct H; subst; [left | right].
      reflexivity.
      apply IHt, H.
Qed.
(* end hide *)

Lemma In_map_conv :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x : A, f x = y /\ In x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct H; subst.
        exists h. split; trivial. left. reflexivity.
        destruct (IHt H) as (x & H1 & H2). exists x.
          split; trivial. right. assumption.
    destruct 1 as [x [<- H2]]. apply In_map, H2.
Qed.
(* end hide *)

Lemma In_map_conv' :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    (forall x y : A, f x = f y -> x = y) ->
      In (f x) (map f l) -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct H0.
      specialize (H _ _ H0). subst. left. reflexivity.
      right. apply IHt; assumption.
Qed.
(* end hide *)

Lemma map_ext_In :
  forall (A B : Type) (f g : A -> B) (l : list A),
    (forall x : A, In x l -> f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite H, IHt.
      reflexivity.
      intros. apply H. right. assumption.
      left. reflexivity.
Qed.
(* end hide *)

Lemma In_join :
  forall (A : Type) (x : A) (ll : list (list A)),
    In x (join ll) <->
    exists l : list A, In x l /\ In l ll.
(* begin hide *)
Proof.
  split.
    induction ll as [| h t]; cbn; intros.
      contradiction.
      rewrite In_app in H. destruct H.
        exists h. split; try left; trivial.
        destruct (IHt H) as [l [H1 H2]].
          exists l. split; try right; assumption.
    destruct 1 as (l & H1 & H2).
    induction ll as [| h t]; cbn in *.
      assumption.
      destruct H2; subst.
        apply In_app_l. assumption.
        apply In_app_r, IHt, H.
Qed.
(* end hide *)

Lemma In_replicate :
  forall (A : Type) (n : nat) (x y : A),
    In y (replicate n x) <-> n <> 0 /\ x = y.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; inversion 1; subst.
      split; auto.
      destruct (IHn' H0). auto.
    intros [H H']. rewrite H'. destruct n as [| n'].
      contradiction H. trivial.
      cbn. left. reflexivity.
Qed.
(* end hide *)

Lemma In_iterate :
  forall (A : Type) (f : A -> A) (n : nat) (x y : A),
    In y (iterate f n x) <-> exists k : nat, k < n /\ y = iter f k x.
(* begin hide *)
Proof.
  split.
    revert f x y. induction n as [| n']; cbn; intros.
      contradiction.
      destruct H.
        rewrite H. exists 0. cbn. split.
          apply le_n_S, le_0_n.
          reflexivity.
        destruct (IHn' _ _ _ H) as (n & IH1 & IH2). exists (S n). split.
          apply lt_n_S. assumption.
          cbn. assumption.
    revert f x y. induction n as [| n']; cbn; intros.
      destruct H as (k & H1 & H2). inv H1.
      destruct H as (k & H1 & H2). destruct k as [| k']; cbn in *.
        left. assumption.
        right. rewrite H2. apply IHn'. exists k'. split.
          apply lt_S_n. assumption.
          reflexivity.
Qed.
(* end hide *)

Lemma nth_In :
  forall (A : Type) (l : list A) (n : nat),
    n < length l -> exists x : A, nth n l = Some x /\ In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      exists h. repeat constructor.
      destruct (IHt _ (lt_S_n _ _ H)) as (x & IH1 & IH2).
        exists x. split; try right; assumption.
Qed.
(* end hide *)

Lemma iff_In_nth :
  forall (A : Type) (x : A) (l : list A),
    In x l <-> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct H; subst.
        exists 0. reflexivity.
        destruct (IHt H) as (n & IH). exists (S n). assumption.
    induction l as [| h t]; cbn; intros.
      destruct H. inv H.
      destruct H as (n & H). destruct n as [| n'].
        inv H. left. reflexivity.
        right. apply IHt. exists n'. assumption.
Qed.
(* end hide *)

Lemma In_rev_aux :
  forall (A : Type) (x : A) (l : list A),
    In x l -> In x (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    inversion H; subst.
      apply In_app_r. left. reflexivity.
      apply In_app_l. apply IHt. assumption.
Qed.
(* end hide *)

Lemma In_rev :
  forall (A : Type) (x : A) (l : list A),
    In x (rev l) <-> In x l.
(* begin hide *)
Proof.
  split; intro.
    apply In_rev_aux in H. rewrite rev_inv in H. assumption.
    apply In_rev_aux, H.
Qed.
(* end hide *)

Lemma In_take :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    In x (take n l) -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; inversion H; subst; clear H.
      left. reflexivity.
      right. apply (IHt _ _ H0).
Qed.
(* end hide *)

Lemma In_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    In x (drop n l) -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n'].
      assumption.
      right. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma In_splitAt :
  forall (A : Type) (l b e : list A) (n : nat) (x y : A),
    splitAt n l = Some (b, x, e) ->
      In y l <-> In y b \/ x = y \/ In y e.
(* begin hide *)
Proof.
  intros. pose (splitAt_spec _ l n). rewrite H in y0. subst.
  rewrite In_app. cbn. firstorder.
Qed.
(* end hide *)

Lemma In_insert :
  forall (A : Type) (l : list A) (n : nat) (x y : A),
    In y (insert l n x) <-> x = y \/ In y l.
(* begin hide *)
Proof.
  split; revert n x.
    induction l as [| h t]; cbn; intros.
      firstorder.
      destruct n as [| n']; cbn in *.
        clear IHt. firstorder.
        firstorder.
    induction l as [| h t]; cbn; intros.
      firstorder.
      destruct n as [| n']; cbn.
        clear IHt. firstorder.
        firstorder.
Qed.
(* end hide *)

Lemma In_replace :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    replace l n x = Some l' ->
      In y l' <-> In y (take n l) \/ x = y \/ In y (drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H. destruct (n <? length l).
    inv H. rewrite In_app, In_cons. firstorder.
    inv H.
Qed.
(* end hide *)

Lemma In_filter :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x (filter p l) <-> p x = true /\ In x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      case_eq (p h); intros; rewrite H0 in *.
        inversion H; subst; clear H.
          repeat constructor. assumption.
          destruct (IHt H1). firstorder constructor.
        destruct (IHt H). firstorder constructor.
    induction l as [| h t]; cbn; destruct 1.
      assumption.
      case_eq (p h); cbn; intros.
        destruct H0; [left | right].
          assumption.
          apply IHt. split; assumption.
        destruct H0; subst.
          congruence.
          apply IHt. split; assumption.
Qed.
(* end hide *)

Lemma In_filter_conv :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    In x l <->
    In x (filter p l) /\ p x = true \/
    In x (filter (fun x : A => negb (p x)) l) /\ p x = false.
(* begin hide *)
Proof.
  split; rewrite ?In_filter.
  destruct (p x). all: firstorder.
Qed.
(* end hide *)

Lemma In_partition :
  forall (A : Type) (p : A -> bool) (x : A) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      In x l <->
      (In x l1 /\ p x = true) \/ (In x l2 /\ p x = false).
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H. inversion H; subst; clear H.
  rewrite (In_filter_conv _ p). reflexivity.
Qed.
(* end hide *)

Lemma In_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x (takeWhile p l) -> In x l /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction.
    case_eq (p h); intros; rewrite H0 in *; cbn in *.
      split; destruct H; subst.
        left. reflexivity.
          right. destruct (IHt _ H). assumption.
          assumption.
          destruct (IHt _ H). assumption.
      contradiction.
Qed.
(* end hide *)

Lemma In_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x (dropWhile p l) -> In x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction.
    case_eq (p h); intros; rewrite H0 in *; cbn in *.
      right. apply IHt. assumption.
      assumption.
Qed.
(* end hide *)

Lemma In_takeWhile_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x l ->
      In x (takeWhile p l) \/
      In x (dropWhile p l).
(* begin hide *)
Proof.
  intros. apply In_app. rewrite takeWhile_dropWhile_spec. assumption.
Qed.
(* end hide *)

Lemma In_dropWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    In x l -> ~ In x (dropWhile p l) -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction.
    case_eq (p h); intros; rewrite H1 in *; cbn in *.
      destruct H; subst.
        assumption.
        apply IHt; assumption.
      contradiction.
Qed.
(* end hide *)

Lemma In_span :
  forall (A : Type) (p : A -> bool) (x y : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      In y l <-> In y b \/ y = x \/ In y e.
(* begin hide *)
(* TODO: In_span jak elem (nie pamiętam, o co chodzi) *)
Proof.
  intros. rewrite ?In_elem. assert (H' := elem_span _ p l).
  rewrite H in H'. rewrite H'. reflexivity.
Qed.
(* end hide *)

Lemma In_zip :
  forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    In (a, b) (zip la lb) -> In a la /\ In b lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    contradiction.
    destruct lb as [| hb tb]; cbn in *.
      contradiction.
      destruct H.
        inversion H; subst. split; left; reflexivity.
      destruct (IHta _ H). split; right; assumption.
Qed.
(* end hide *)

Lemma zip_not_In :
  exists (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    In a la /\ In b lb /\ ~ In (a, b) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists true, false.
  exists [true; false], [true; false].
  cbn. repeat split.
    repeat constructor.
    right; left. reflexivity.
    inversion 1; inversion H0; subst.
      inversion H1.
      contradiction.
Qed.
(* end hide *)

Lemma In_intersperse :
  forall (A : Type) (x y : A) (l : list A),
    In x (intersperse y l) <->
    In x l \/ (x = y /\ 2 <= length l).
(* begin hide *)
Proof.
  intros. rewrite ?In_elem. apply elem_intersperse.
Qed.
(* end hide *)

(** ** [NoDup] *)

(** Zdefiniuj induktywny predykat [NoDup]. Zdanie [NoDup l] jest prawdziwe,
    gdy w [l] nie ma powtarzających się elementów. Udowodnij, że zdefiniowany
    przez ciebie predykat posiada pożądane właściwości. *)

(* begin hide *)
Inductive NoDup {A : Type} : list A -> Prop :=
    | NoDup_nil : NoDup []
    | NoDup_cons :
        forall (h : A) (t : list A),
          ~ elem h t -> NoDup t -> NoDup (h :: t).
(* end hide *)

Lemma NoDup_singl :
  forall (A : Type) (x : A), NoDup [x].
(* begin hide *)
Proof.
  repeat constructor. inversion 1.
Qed.
(* end hide *)

Lemma NoDup_cons_inv :
  forall (A : Type) (h : A) (t : list A),
    NoDup (h :: t) -> NoDup t.
(* begin hide *)
Proof.
  intros. inv H. assumption.
Qed.
(* end hide *)

Lemma NoDup_length :
  forall (A : Type) (l : list A),
    ~ NoDup l -> 2 <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    contradiction H. constructor.
    destruct t as [| h' t']; cbn.
      contradiction H. apply NoDup_singl.
      apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma NoDup_snoc :
  forall (A : Type) (x : A) (l : list A),
    NoDup (snoc x l) <-> NoDup l /\ ~ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      split.
        constructor.
        inversion 1.
      inversion H; subst; clear H. split.
        constructor.
          intro. apply H2. rewrite elem_snoc. left. assumption.
          destruct (IHt H3). assumption.
        inversion 1; subst.
          apply H2. rewrite elem_snoc. right. reflexivity.
          destruct (IHt H3). contradiction.
    destruct 1. induction H; cbn.
      repeat constructor. inversion 1.
      constructor.
        Focus 2. apply IHNoDup. intro. apply H0. right. assumption.
        intro. rewrite elem_snoc in H2. destruct H2; subst.
          contradiction.
          apply H0. left.
Qed.
(* end hide *)

Lemma NoDup_app :
  forall (A : Type) (l1 l2 : list A),
    NoDup (l1 ++ l2) <->
    NoDup l1 /\
    NoDup l2 /\
    (forall x : A, elem x l1 -> ~ elem x l2) /\
    (forall x : A, elem x l2 -> ~ elem x l1).
(* begin hide *)
Proof.
  split; intros.
    induction l1 as [| h1 t1]; cbn; intros.
      repeat split; firstorder.
        constructor.
        inversion H0.
        intro. inversion H1.
      inversion H; subst; clear H. rewrite elem_app in H2.
        decompose [and] (IHt1 H3); clear IHt1. repeat split; intros.
          constructor.
            firstorder.
            assumption.
          assumption.
          inversion H4; firstorder.
          inversion 1; subst; firstorder.
  decompose [and] H; clear H.
  induction H0; cbn.
    assumption.
    constructor.
      rewrite elem_app. destruct 1.
        contradiction.
        apply (H1 h).
          constructor.
          assumption.
      apply IHNoDup; intros.
        intro. apply (H1 x).
          constructor. assumption.
          assumption.
        intro. apply (H4 x).
          assumption.
          constructor. assumption.
Qed.
(* end hide *)

Lemma NoDup_app_comm :
  forall (A : Type) (l1 l2 : list A),
    NoDup (l1 ++ l2) <-> NoDup (l2 ++ l1).
(* begin hide *)
Proof.
  intro.
  assert (forall l1 l2 : list A, NoDup (l1 ++ l2) -> NoDup (l2 ++ l1)).
    intros l1 l2. revert l1. induction l2 as [| h t]; cbn; intros.
      rewrite app_nil_r in H. assumption.
      constructor.
        intro. apply NoDup_app in H. decompose [and] H; clear H.
          apply elem_app_or in H0. destruct H0.
            inversion H3. contradiction.
            specialize (H5 _ ltac:(left)). contradiction.
        apply IHt. apply NoDup_app in H. apply NoDup_app.
          decompose [and] H; clear H. repeat split.
            assumption.
            inversion H2. assumption.
            intros. specialize (H1 _ H). intro. apply H1. right. assumption.
            repeat intro. apply (H1 _ H3). right. assumption.
      intros. split; apply H.
Qed.
(* end hide *)

Lemma NoDup_rev :
  forall (A : Type) (l : list A),
    NoDup (rev l) <-> NoDup l.
(* begin hide *)
Proof.
  assert (forall (A : Type) (l : list A), NoDup l -> NoDup (rev l)).
    induction 1; cbn.
      constructor.
      apply NoDup_app; repeat split; intros.
        assumption.
        apply NoDup_singl.
        inversion 1; subst.
          contradiction H. rewrite <- elem_rev. assumption.
          inversion H5.
        inversion H1; subst; clear H1.
          intro. contradiction H. rewrite <- elem_rev. assumption.
          inversion H4.
  split; intro.
    rewrite <- rev_inv. apply H. assumption.
    apply H. assumption.
Qed.
(* end hide *)

Lemma NoDup_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    NoDup (map f l) -> NoDup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  constructor; inversion H; subst; clear H.
    intro. apply H2, elem_map. assumption.
    apply IHt. assumption.
Qed.
(* end hide *)

Lemma NoDup_map_inj :
  forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y : A, f x = f y -> x = y) ->
      NoDup l -> NoDup (map f l).
(* begin hide *)
Proof.
  induction 2; cbn; constructor.
    intro. apply H0, (elem_map_conv' _ _ f _ h H). assumption.
    assumption.
Qed.
(* end hide *)

Lemma NoDup_replicate :
  forall (A : Type) (n : nat) (x : A),
    NoDup (replicate n x) <-> n = 0 \/ n = 1.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; intros.
      left. reflexivity.
      inversion H; subst. destruct (IHn' H3); subst.
        right. reflexivity.
        contradiction H2. constructor.
    destruct 1; subst; cbn; repeat constructor. inversion 1.
Qed.
(* end hide *)

Lemma NoDup_take :
  forall (A : Type) (l : list A) (n : nat),
    NoDup l -> NoDup (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn; constructor.
      intro. inversion H; subst; clear H.
        apply elem_take in H0. contradiction.
      apply IHt. inversion H. assumption.
Qed.
(* end hide *)

Lemma NoDup_drop :
  forall (A : Type) (l : list A) (n : nat),
    NoDup l -> NoDup (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      apply IHt. inversion H. assumption.
Qed.
(* end hide *)

Lemma NoDup_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    NoDup l -> NoDup (filter p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h).
      constructor.
        intro. apply H. apply elem_filter in H1. destruct H1. assumption.
        assumption.
      assumption.
Qed.
(* end hide *)

Lemma NoDup_partition :
  forall (A : Type) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) -> NoDup l <-> NoDup l1 /\ NoDup l2.
(* begin hide *)
Proof.
  split.
    intro. revert dependent l2. revert dependent l1.
    induction H0; cbn in *; intros.
      inversion H; subst; clear H. split; constructor.
      case_eq (partition p t); case_eq (p h); intros; rewrite H2, H3 in *.
        inversion H1; subst; clear H1. destruct (IHNoDup _ _ eq_refl). split.
          constructor.
            intro. apply H. apply (elem_partition _ _ h) in H3.
              rewrite H3. left. split; assumption.
            assumption.
          assumption.
        inversion H1; subst; clear H1. destruct (IHNoDup _ _ eq_refl). split.
          assumption.
          constructor.
            intro. apply H. apply (elem_partition _ _ h) in H3. rewrite H3.
              right. split; assumption.
            assumption.
    revert dependent l2; revert dependent l1.
    induction l as [| h t]; cbn in *; intros.
      constructor.
      constructor.
        Focus 2. destruct (partition p t), (p h).
          destruct H0. inversion H; subst; inversion H0; subst; clear H H0.
            eapply IHt; eauto.
          destruct H0. inversion H; subst; inversion H1; subst; clear H H1.
            eapply IHt; eauto.
        intro. case_eq (partition p t); case_eq (p h); intros; subst;
        rewrite H2, H3 in *; inversion H; subst; clear H.
          pose (H4 := H3). apply (elem_partition _ _ h) in H4.
            rewrite H4 in H1. destruct H1.
              destruct H0. inversion H0. destruct H; contradiction.
              rewrite partition_spec in H3. inversion H3; subst; clear H3.
                destruct H. apply elem_filter in H. destruct H. destruct (p h).
                  inversion H.
                  inversion H2.
          pose (H4 := H3). apply (elem_partition _ _ h) in H4.
            rewrite H4 in H1. destruct H1.
              rewrite partition_spec in H3. inversion H3; subst; clear H3.
                destruct H. apply elem_filter in H. destruct H. destruct (p h).
                  inversion H2.
                  inversion H.
              destruct H0. inversion H1. destruct H. contradiction.
Qed.
(* end hide *)

Lemma NoDup_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    NoDup l -> NoDup (takeWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h); constructor.
      intro. apply H. apply elem_takeWhile in H1. destruct H1. assumption.
      assumption.
Qed.
(* end hide *)

Lemma NoDup_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    NoDup l -> NoDup (dropWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h).
      assumption.
      constructor; assumption.
Qed.
(* end hide *)

Lemma NoDup_zip :
  forall (A B : Type) (la : list A) (lb : list B),
    NoDup la /\ NoDup lb -> NoDup (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    constructor.
    destruct lb as [| hb tb]; cbn in *.
      constructor.
      destruct H. inversion H; inversion H0; subst; clear H H0; constructor.
        intro. apply elem_zip in H. destruct H. contradiction.
        apply IHta. split; assumption.
Qed.
(* end hide *)

Lemma NoDup_zip_conv :
  exists (A B : Type) (la : list A) (lb : list B),
    NoDup (zip la lb) /\ ~ NoDup la /\ ~ NoDup lb.
(* begin hide *)
Proof.
  exists bool, bool, [true; false; true], [false; false; true]. split.
    cbn. repeat constructor; intro; inv H; inv H2; inv H1.
    split; intro; inv H; apply H2.
      right. left.
      left.
Qed.
(* end hide *)

Lemma NoDup_pmap :
  exists (A B : Type) (f : A -> option B) (l : list A),
    NoDup l /\ ~ NoDup (pmap f l).
(* begin hide *)
Proof.
  exists bool, unit, (fun _ => Some tt), [true; false]. split.
    repeat constructor; inversion 1. inversion H2.
    cbn. inversion 1; subst. apply H2. constructor.
Qed.
(* end hide *)

Lemma NoDup_intersperse :
  forall (A : Type) (x : A) (l : list A),
    NoDup (intersperse x l) -> length l <= 2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        apply le_S, le_n.
        destruct (intersperse x t); inversion Heq.
      inversion H. inversion H3. subst. specialize (IHt H7).
        destruct t as [| w1 [| w2 z]]; cbn in *.
          inversion Heq.
          apply le_n.
          destruct (intersperse x z).
            inversion Heq. subst. contradiction H6. right. left.
            inversion Heq; subst. contradiction H6. right. left.
Qed.
(* end hide *)

Lemma NoDup_spec :
  forall (A : Type) (l : list A),
    ~ NoDup l <->
    exists (x : A) (l1 l2 l3 : list A),
      l = l1 ++ x :: l2 ++ x :: l3.
(* begin hide *)
Proof.
  split.
    Focus 2. destruct 1 as (x & l1 & l2 & l3 & H). subst. intro.
      rewrite <- !app_cons_l in H. rewrite !NoDup_app in H.
      decompose [and] H; clear H. specialize (H4 x). apply H4; constructor.
    induction l as [| h t]; cbn; intros.
      contradiction H. constructor.
      change (h :: t) with ([h] ++ t) in H. rewrite NoDup_app in H.
        contradiction H.
Abort. (* Ten [Abort] jest umyślny. *)
(* end hide *)

(** ** [Dup] *)

(** Powodem problemów z predykatem [NoDup] jest fakt, że jest on w pewnym
    sensie niekonstruktywny. Wynika to wprost z jego definicji: [NoDup l]
    zachodzi, gdy w [l] nie ma duplikatów. Parafrazując: [NoDup l] zachodzi,
    gdy _nieprawda_, że w [l] są duplikaty.

    Jak widać, w naszej definicji implicite występuje negacja. Wobec tego
    jeżeli spróbujemy za pomocą [NoDup] wyrazić zdanie "na liście [l] są
    duplikaty", to tak naprawdę dostaniemy zdanie "nieprawda, że nieprawda,
    że [l] ma duplikaty".

    Dostaliśmy więc po głowie nagłym atakiem podwójnej negacji. Nie ma się
    co dziwić w takiej sytuacji, że nasza "negatywna" definicja predykatu
    [NoDup] jest nazbyt klasyczna. Możemy jednak uratować sytuację, jeżeli
    zdefiniujemy predykat [Dup] i zanegujemy go.

    Zdefiniuj predykat [Dup], który jest spełniony, gdy na liście występują
    duplikaty. *)

(* begin hide *)
Inductive Dup {A : Type} : list A -> Prop :=
    | Dup_elem :
        forall (h : A) (t : list A),
          elem h t -> Dup (h :: t)
    | Dup_tail :
        forall (h : A) (t : list A),
          Dup t -> Dup (h :: t).
(* end hide *)

Lemma Dup_nil :
  forall A : Type, ~ Dup (@nil A).
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma Dup_cons :
  forall (A : Type) (x : A) (l : list A),
    Dup (x :: l) <-> elem x l \/ Dup l.
(* begin hide *)
Proof.
  split; intro.
    inv H; [left | right]; assumption.
    destruct H; constructor; assumption.
Qed.
(* end hide *)

Lemma Dup_singl :
  forall (A : Type) (x : A), ~ Dup [x].
(* begin hide *)
Proof.
  inversion 1; subst; inversion H1.
Qed.
(* end hide *)

Lemma Dup_cons_inv :
  forall (A : Type) (h : A) (t : list A),
    ~ Dup (h :: t) -> ~ elem h t /\ ~ Dup t.
(* begin hide *)
Proof.
  intros. split; intro; apply H; [left | right]; assumption.
Qed.
(* end hide *)

Lemma Dup_spec :
  forall (A : Type) (l : list A),
    Dup l <->
    exists (x : A) (l1 l2 l3 : list A),
      l = l1 ++ x :: l2 ++ x :: l3.
(* begin hide *)
Proof.
  split.
    induction 1.
      induction H.
        exists x, [], [], l. cbn. reflexivity.
        destruct IHelem as (x' & l1 & l2 & l3 & H').
          destruct l1; inversion H'; subst; clear H'.
            exists x', [], (h :: l2), l3. cbn. reflexivity.
            exists x', (a :: h :: l1), l2, l3. cbn. reflexivity.
      destruct IHDup as (x' & l1 & l2 & l3 & H'); subst.
        exists x', (h :: l1), l2, l3. cbn. reflexivity.
    destruct 1 as (x & l1 & l2 & l3 & H); subst.
    induction l1 as [| h1 t1]; cbn.
      constructor. rewrite elem_app. right. constructor.
      right. assumption.
Qed.
(* end hide *)

Lemma Dup_NoDup :
  forall (A : Type) (l : list A),
    ~ Dup l <-> NoDup l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      constructor.
      constructor.
        intro. apply H. left. assumption.
        apply IHt. intro. apply H. right. assumption.
    induction 1; cbn; intro.
      inversion H.
      inversion H1; subst; clear H1; contradiction.
Qed.
(* end hide *)

Lemma Dup_length :
  forall (A : Type) (l : list A),
    Dup l -> 2 <= length l.
(* begin hide *)
Proof.
  induction 1; cbn.
    destruct t; cbn.
      inversion H.
      apply le_n_S, le_n_S, le_0_n.
    apply le_trans with (length t).
      assumption.
      apply le_S. apply le_refl.
Qed.
(* end hide *)

Lemma Dup_snoc :
  forall (A : Type) (x : A) (l : list A),
    Dup (snoc x l) <-> Dup l \/ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H; subst; inversion H1.
      inversion H; subst; clear H.
        rewrite elem_snoc in H1. destruct H1.
          left. constructor. assumption.
          right. subst. left.
        destruct (IHt H1).
          left. right. assumption.
          do 2 right. assumption.
    destruct 1.
      induction H; cbn.
        left. rewrite elem_snoc. left. assumption.
        right. assumption.
      induction H; cbn.
        left. rewrite elem_snoc. right. reflexivity.
        right. assumption.
Qed.
(* end hide *)

Lemma Dup_app_l :
  forall (A : Type) (l1 l2 : list A),
    Dup l1 -> Dup (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor. apply elem_app_l. assumption.
    right. assumption.
Qed.
(* end hide *)

Lemma Dup_app_r :
  forall (A : Type) (l1 l2 : list A),
    Dup l2 -> Dup (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    right. apply (IHt1 _ H).
Qed.
(* end hide *)

Lemma Dup_app_both :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l1 -> elem x l2 -> Dup (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. apply elem_app_r. assumption.
    right. apply IHelem, H0.
Qed.
(* end hide *)

Lemma Dup_app :
  forall (A : Type) (l1 l2 : list A),
    Dup (l1 ++ l2) <->
    Dup l1 \/ Dup l2 \/ exists x : A, elem x l1 /\ elem x l2.
(* begin hide *)
Proof.
  split.
    induction l1 as [| h1 t1]; cbn; intros.
      right; left. assumption.
      inversion H; subst; clear H.
        rewrite elem_app in H1. destruct H1.
          left. constructor. assumption.
          right; right. exists h1. split; [constructor | assumption].
        decompose [ex or] (IHt1 H1); clear IHt1.
          left; right. assumption.
          right; left. assumption.
          destruct H. right; right. exists x.
            split; try constructor; assumption.
    destruct 1 as [H | [H | [x [H1 H2]]]].
      apply Dup_app_l; assumption.
      apply Dup_app_r; assumption.
      apply (Dup_app_both _ x); assumption.
Qed.
(* end hide *)

Lemma Dup_rev :
  forall (A : Type) (l : list A),
    Dup (rev l) <-> Dup l.
(* begin hide *)
Proof.
  assert (forall (A : Type) (l : list A), Dup l -> Dup (rev l)).
    induction 1; cbn.
      apply Dup_app_both with h.
        apply elem_rev. assumption.
        constructor.
      apply Dup_app_l. assumption.
    split; intros.
      rewrite <- rev_inv. apply H. assumption.
      apply H. assumption.
Qed.
(* end hide *)

Lemma Dup_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    Dup l -> Dup (map f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    left. apply elem_map. assumption.
    right. assumption.
Qed.
(* end hide *)

Lemma Dup_map_conv :
  forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y : A, f x = f y -> x = y) ->
      Dup (map f l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0.
    inversion H0; subst; clear H0.
      left. apply (elem_map_conv' _ _ _ _ _ H H2).
      right. apply IHt; assumption.
Qed.
(* end hide *)

Lemma Dup_join :
  forall (A : Type) (ll : list (list A)),
    Dup (join ll) ->
    (exists l : list A, elem l ll /\ Dup l) \/
    (exists (x : A) (l1 l2 : list A),
      elem x l1 /\ elem x l2 /\ elem l1 ll /\ elem l2 ll).
(* begin hide *)
Proof.
  induction ll as [| h t]; cbn; intros.
    inversion H.
    apply Dup_app in H. decompose [or ex] H; clear H.
      left. exists h. split; [constructor | assumption].
      decompose [ex or and] (IHt H1); clear IHt.
        left. exists x. split; try right; assumption.
        right. exists x, x0, x1. firstorder (constructor; assumption).
      right. destruct H0. apply elem_join in H0. destruct H0 as [l [H1 H2]].
        exists x, h, l. firstorder.
          1-2: constructor; assumption.
Qed.
(* end hide *)

Lemma Dup_replicate :
  forall (A : Type) (n : nat) (x : A),
    Dup (replicate n x) -> 2 <= n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; inversion H; subst; clear H.
    destruct n' as [| n'']; cbn in H1.
      inversion H1.
      apply le_n_S, le_n_S, le_0_n.
    apply le_trans with n'.
      apply (IHn' _ H1).
      apply le_S, le_n.
Qed.
(* end hide *)

Lemma Dup_nth :
  forall (A : Type) (l : list A),
    Dup l <->
    exists (x : A) (n1 n2 : nat),
      n1 < n2 /\ nth n1 l = Some x /\ nth n2 l = Some x.
(* begin hide *)
Proof.
  split.
    intro. apply Dup_spec in H. destruct H as (x & l1 & l2 & l3 & H); subst.
      exists x, (length l1), (length l1 + length l2 + 1). repeat split.
        lia.
        rewrite nth_app_r.
          rewrite <- minus_n_n. cbn. reflexivity.
          apply le_n.
        rewrite nth_app_r.
          rewrite <- app_cons_l, nth_app_r.
            replace (nth _ (x :: l3)) with (nth 0 (x :: l3)).
              cbn. reflexivity.
              f_equal. 1-3: cbn; lia.
    destruct 1 as (x & n1 & n2 & H1 & H2 & H3). revert x n1 n2 H1 H2 H3.
    induction l as [| h t]; cbn; intros.
      inv H2.
      destruct n1 as [| n1'], n2 as [| n2'].
        inv H1.
        inv H2. constructor. rewrite iff_elem_nth. exists n2'. assumption.
        inv H1.
        right. apply (IHt _ _ _ (lt_S_n _ _ H1) H2 H3).
Qed.
(* end hide *)

Lemma Dup_take :
  forall (A : Type) (l : list A) (n : nat),
    Dup (take n l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn; inversion H; subst; clear H.
      constructor. apply elem_take in H1. assumption.
      right. apply (IHt _ H1).
Qed.
(* end hide *)

Lemma Dup_drop :
  forall (A : Type) (l : list A) (n : nat),
    Dup (drop n l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      right. apply (IHt _ H).
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Dup vs insert i replace *)
(* TODO: findIndex, takeWhile, dropWhile dla replace *)
(* end hide *)

Lemma Dup_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup (filter p l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      inversion H; subst; clear H.
        left. apply elem_filter in H1. destruct H1. assumption.
        right. apply IHt, H1.
      right. apply IHt, H.
Qed.
(* end hide *)

Lemma Dup_filter_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup l ->
      Dup (filter p l) \/
      Dup (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction 1; cbn; case_eq (p h); cbn; intros.
    do 2 left. apply elem_filter. split; assumption.
    right. left. apply elem_filter. rewrite H0. split; trivial.
    destruct IHDup.
      left. right. assumption.
      right. assumption.
    destruct IHDup.
      left. assumption.
      right. right. assumption.
Qed.
(* end hide *)

Lemma Dup_partition :
  forall (A : Type) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) -> Dup l <-> Dup l1 \/ Dup l2.
(* begin hide *)
Proof.
  split.
    intro. revert dependent l2; revert dependent l1.
    induction H0; cbn in *; intros.
      case_eq (partition p t); case_eq (p h); intros;
      rewrite H1, H2 in *; inversion H0; subst; clear H0.
        apply (elem_partition _ _ h) in H2. rewrite H2 in H. destruct H.
          do 2 left. destruct H. assumption.
          destruct H. congruence.
        apply (elem_partition _ _ h) in H2. rewrite H2 in H. destruct H.
          destruct H. congruence.
          right; left. destruct H. assumption.
      destruct (partition p t), (p h);
      inversion H; subst; clear H; destruct (IHDup _ _ eq_refl).
        left; right; assumption.
        right; assumption.
        left; assumption.
        right; right. assumption.
    revert dependent l2; revert dependent l1.
    induction l as [| h t]; cbn in *; intros.
      inversion H; subst; clear H. destruct H0; assumption.
      case_eq (partition p t); case_eq (p h); intros;
      rewrite H1, H2 in *; inversion H; subst; clear H.
        destruct H0.
          inversion H; subst; clear H.
            apply (elem_partition _ _ h) in H2. left. rewrite H2. left.
              split; assumption.
            right. apply (IHt _ _ eq_refl). left. assumption.
          right. apply (IHt _ _ eq_refl). right. assumption.
        destruct H0.
          right. apply (IHt _ _ eq_refl). left. assumption.
          inversion H; subst; clear H.
            apply (elem_partition _ _ h) in H2. left. rewrite H2.
              right. split; assumption.
            right. apply (IHt _ _ eq_refl). right. assumption.
Qed.
(* end hide *)

Lemma Dup_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup (takeWhile p l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      inversion H; subst; clear H.
        left. apply elem_takeWhile in H1. destruct H1. assumption.
        right. apply IHt, H1.
      inversion H.
Qed.
(* end hide *)

Lemma Dup_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup (dropWhile p l) -> Dup l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      right. apply IHt, H.
      assumption.
Qed.
(* end hide *)

Lemma Dup_takeWhile_dropWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    Dup l ->
      Dup (takeWhile p l) \/
      Dup (dropWhile p l) \/
      exists x : A,
        elem x (takeWhile p l) /\ elem x (dropWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    case_eq (p h); intro.
      apply (elem_takeWhile_dropWhile _ p) in H. destruct H.
        do 2 left. assumption.
        do 2 right. exists h. split; [constructor | assumption].
      apply (elem_takeWhile_dropWhile _ p) in H. destruct H.
        right; do 2 left. apply elem_takeWhile in H. destruct H. assumption.
        right; do 2 left. apply elem_dropWhile in H. assumption.
    case_eq (p h); intro.
      destruct IHDup as [IH | [IH | [x [H1 H2]]]].
        left; right. assumption.
        right; left. assumption.
        right; right. exists x. split; try right; assumption.
      destruct IHDup as [IH | [IH | [x [H1 H2]]]].
        right; left; right. apply (Dup_takeWhile _ p). assumption.
        right; left; right. apply (Dup_dropWhile _ p). assumption.
        right; left; right. assumption.
Qed.
(* end hide *)

Lemma Dup_span :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      Dup l <-> Dup b \/ Dup e \/ elem x b \/ elem x e \/
        exists y : A, elem y b /\ elem y e.
(* begin hide *)
Proof.
  intros. apply span_spec in H. subst.
  rewrite Dup_app, Dup_cons. firstorder.
    inv H0; firstorder.
    do 2 right. exists x. split; [assumption | left].
    do 2 right. exists x0. split; try right; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Dup vs NoDup, Rep *)
(* end hide *)

Lemma Dup_zip :
  forall (A B : Type) (la : list A) (lb : list B),
    Dup (zip la lb) -> Dup la /\ Dup lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H.
    destruct lb as [| hb tb]; cbn; inversion H; subst; clear H.
      apply elem_zip in H1. destruct H1. split; left; assumption.
      destruct (IHta _ H1). split; right; assumption.
Qed.
(* end hide *)

Lemma Dup_zip_conv :
  forall (A B : Type) (la : list A) (lb : list B),
    ~ Dup la /\ ~ Dup lb -> ~ Dup (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion 1.
    destruct lb as [| hb tb]; cbn; intros.
      inversion 1.
      inversion 1; subst; clear H0.
        apply elem_zip in H2. destruct H, H2. apply H; left; assumption.
        destruct H. apply Dup_cons_inv in H. apply Dup_cons_inv in  H0.
          destruct H, H0. apply (IHta tb); try split; assumption.
Qed.
(* end hide *)

Lemma Dup_pmap :
  exists (A B : Type) (f : A -> option B) (l : list A),
    Dup l /\ ~ Dup (pmap f l).
(* begin hide *)
Proof.
  exists unit, unit, (fun _ => None), [tt; tt]. split.
    do 2 constructor.
    cbn. inversion 1.
Qed.
(* end hide *)

Lemma Dup_intersperse :
  forall (A : Type) (x : A) (l : list A),
    Dup (intersperse x l) -> 2 <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (intersperse x t) eqn: Heq.
      inversion H; inversion H1.
      destruct t; cbn in *.
        inversion Heq.
        apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)

(** ** [Rep] *)

(** Jeżeli zastanowimy się chwilę, to dojdziemy do wniosku, że [Dup l]
    znaczy "istnieje x, który występuje na liście l co najmniej dwa
    razy". Widać więc, że [Dup] jest jedynie specjalnym przypadkiem
    pewngo bardziej ogólnego predykatu [Rep x n] dla dowolnego [x] oraz
    n = 2. Zdefiniuj relację [Rep]. Zdanie [Rep x n l] zachodzi, gdy
    element [x] występuje na liście [l] co najmnej [n] razy.

    Zastanów się, czy lepsza będzie definicja induktywna, czy rekurencyjna.
    Jeżeli nie masz nic lepszego do roboty, zaimplementuj obie wersje i
    porównaj je pod względem łatwości w użyciu. *)

(* begin hide *)
Inductive Rep {A : Type} (x : A) : nat -> list A -> Prop :=
    | Rep_zero :
        forall l : list A, Rep x 0 l
    | Rep_cons_1 :
        forall (n : nat) (l : list A),
          Rep x n l -> Rep x (S n) (x :: l)
    | Rep_cons_2 :
        forall (n : nat) (l : list A) (y : A),
          Rep x n l -> Rep x n (y :: l).
(* end hide *)

Lemma Rep_S_cons :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x (S n) (y :: l) <-> (x = y /\ Rep x n l) \/ Rep x (S n) l.
(* begin hide *)
Proof.
  split; intros.
    inv H.
      left. split; [reflexivity | assumption].
      right. assumption.
    decompose [and or] H; clear H; subst; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_cons :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n (y :: l) <-> (x = y /\ Rep x (n - 1) l) \/ Rep x n l.
(* begin hide *)
Proof.
  split; intros.
    inv H.
      right. constructor.
      left. cbn. rewrite <- minus_n_O. split; [reflexivity | assumption].
    right. assumption.
    decompose [and or] H; clear H; subst.
      destruct n as [| n']; cbn in *; constructor.
        rewrite <-minus_n_O in H2. assumption.
      constructor. assumption.
Qed.
(* end hide *)

Lemma elem_Rep :
  forall (A : Type) (x : A) (l : list A),
    elem x l -> Rep x 1 l.
(* begin hide *)
Proof.
  induction 1; constructor.
    constructor.
    assumption.
Qed.
(* end hide *)

Lemma Rep_elem :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    1 <= n -> Rep x n l -> elem x l.
(* begin hide *)
Proof.
  induction 2.
    inversion H.
    left.
    destruct n as [| n'].
      inversion H.
      right. apply IHRep. apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma Dup_Rep :
  forall (A : Type) (l : list A),
    Dup l -> exists x : A, Rep x 2 l.
(* begin hide *)
Proof.
  induction 1.
    exists h. constructor. apply elem_Rep. assumption.
    destruct IHDup as [x IH]. exists x. constructor. assumption.
Qed.
(* end hide *)

Lemma Rep_Dup :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    2 <= n -> Rep x n l -> Dup l.
(* begin hide *)
Proof.
  induction 2.
    inversion H.
    left. apply Rep_elem in H0.
      assumption.
      apply le_S_n. assumption.
    right. apply IHRep, H.
Qed.
(* end hide *)

Lemma Rep_le :
  forall (A : Type) (x : A) (n m : nat) (l : list A),
    n <= m -> Rep x m l -> Rep x n l.
(* begin hide *)
Proof.
  intros A x n m l H HR. generalize dependent n.
  induction HR; intros.
    destruct n as [| n'].
      constructor.
      inversion H.
    destruct n0 as [| n0'].
      constructor.
      constructor. apply IHHR. apply le_S_n. assumption.
    constructor. apply IHHR. assumption.
Qed.
(* end hide *)

Lemma Rep_S_inv :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x (S n) l -> Rep x n l.
(* begin hide *)
Proof.
  intros. apply Rep_le with (S n).
    apply le_S, le_n.
    assumption.
Qed.
(* end hide *)

Lemma Rep_length :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x n l -> n <= length l.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    apply le_n_S. assumption.
    apply le_trans with (length l).
      assumption.
      apply le_S, le_n.
Qed.
(* end hide *)

Lemma Rep_S_snoc :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x n l -> Rep x (S n) (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn.
      repeat constructor.
      constructor. assumption.
    1-2: constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_snoc :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n l -> Rep x n (snoc y l).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_app_l :
  forall (A : Type) (x : A) (n : nat) (l1 l2 : list A),
    Rep x n l1 -> Rep x n (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_app_r :
  forall (A : Type) (x : A) (n : nat) (l1 l2 : list A),
    Rep x n l2 -> Rep x n (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    assumption.
    constructor. apply IHt1, H.
Qed.
(* end hide *)

Lemma Rep_app :
  forall (A : Type) (x : A) (n1 n2 : nat) (l1 l2 : list A),
    Rep x n1 l1 -> Rep x n2 l2 -> Rep x (n1 + n2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    apply Rep_app_r. assumption.
    constructor. apply IHRep, H0.
    constructor. apply IHRep, H0.
Qed.
(* end hide *)

Lemma Rep_app_conv :
  forall (A : Type) (x : A) (n : nat) (l1 l2 : list A),
    Rep x n (l1 ++ l2) <->
      exists n1 n2 : nat,
        Rep x n1 l1 /\ Rep x n2 l2 /\ n = n1 + n2.
(* begin hide *)
Proof.
  split.
    generalize dependent n. induction l1 as [| h1 t1]; cbn; intros.
      exists 0, n. repeat split; [constructor | assumption].
      inversion H; subst; clear H.
        exists 0, 0. repeat split; constructor.
        destruct (IHt1 _ H2) as (n1 & n2 & Hn1 & Hn2 & Heq).
          exists (S n1), n2. repeat split.
            constructor. assumption.
            assumption.
            rewrite Heq. cbn. reflexivity.
        destruct (IHt1 _ H2) as (n1 & n2 & Hn1 & Hn2 & Heq).
          exists n1, n2. repeat constructor; assumption.
    destruct 1 as (n1 & n2 & H1 & H2 & H3).
      rewrite H3. apply Rep_app; assumption.
Qed.
(* end hide *)

Lemma Rep_rev :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x n (rev l) <-> Rep x n l.
(* begin hide *)
Proof.
  assert (forall (A : Type) (x : A) (n : nat) (l : list A),
            Rep x n l -> Rep x n (rev l)).
    induction 1; cbn.
      constructor.
      rewrite Rep_app_conv. exists n, 1. repeat split.
        assumption.
        do 2 constructor.
        rewrite plus_comm. cbn. reflexivity.
      apply Rep_app_l. assumption.
    split; intros.
      rewrite <- rev_inv. apply H, H0.
      apply H, H0.
Qed.
(* end hide *)

Lemma Rep_map :
  forall (A B : Type) (f : A -> B) (x : A) (n : nat) (l : list A),
    Rep x n l -> Rep (f x) n (map f l).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_map_conv :
  forall (A B : Type) (f : A -> B) (x : A) (n : nat) (l : list A),
    (forall x y : A, f x = f y -> x = y) ->
      Rep (f x) n (map f l) -> Rep x n l.
(* begin hide *)
Proof.
  intros A B f x n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    inversion H0; subst. constructor.
    destruct n as [| n'].
      constructor.
      inversion H0; subst; clear H0.
        rewrite (H _ _ H2) in *. constructor. apply IHt; assumption.
        constructor. apply IHt, H3. assumption.
Qed.
(* end hide *)

Lemma Rep_replicate :
  forall (A : Type) (x : A) (n : nat),
    Rep x n (replicate n x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_replicate_general :
  forall (A : Type) (x : A) (n m : nat),
    n <= m -> Rep x n (replicate m x).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Rep_replicate.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Rep_take :
  forall (A : Type) (x : A) (l : list A) (n m : nat),
    Rep x n (take m l) -> Rep x n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      constructor.
      destruct m as [| m']; inversion H; subst; clear H.
        constructor. apply (IHt _ _ H2).
        apply Rep_cons_2. apply (IHt _ _ H2).
Qed.
(* end hide *)

Lemma Rep_drop :
  forall (A : Type) (x : A) (l : list A) (n m : nat),
    Rep x n (drop m l) -> Rep x n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      constructor.
      destruct m as [| m'].
        assumption.
        apply Rep_cons_2, (IHt _ _ H).
Qed.
(* end hide *)

Lemma Rep_filter :
  forall (A : Type) (p : A -> bool) (x : A) (n : nat) (l : list A),
    Rep x n (filter p l) -> Rep x n l.
(* begin hide *)
Proof.
  intros A p x n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    assumption.
    case_eq (p h); intros; rewrite H0 in *.
      inversion H; subst; clear H; constructor; apply IHt, H3.
      constructor. apply IHt, H.
Qed.
(* end hide *)

Lemma Rep_filter_true :
  forall (A : Type) (p : A -> bool) (x : A) (n : nat) (l : list A),
    p x = true -> Rep x n l -> Rep x n (filter p l).
(* begin hide *)
Proof.
  induction 2; cbn.
    constructor.
    rewrite H. constructor. assumption.
    destruct (p y); try constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_filter_false :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A) (n : nat),
    p x = false -> Rep x n (filter p l) -> n = 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0. reflexivity.
    case_eq (p h); intros; rewrite H1 in *.
      inversion H0; subst; clear H0.
        reflexivity.
        congruence.
        apply IHt, H4. assumption.
      apply IHt, H0. assumption.
Qed.
(* end hide *)

Lemma Rep_takeWhile :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A) (n : nat),
    Rep x n (takeWhile p l) -> Rep x n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h); inversion H; subst; clear H; constructor; apply IHt, H2.
Qed.
(* end hide *)

Lemma Rep_dropWhile :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A) (n : nat),
    Rep x n (dropWhile p l) -> Rep x n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      constructor; apply IHt, H.
      inversion H; subst; clear H; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_zip :
  forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B) (n : nat),
    Rep (a, b) n (zip la lb) -> Rep a n la /\ Rep b n lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H; subst; clear H. split; constructor.
    destruct lb as [| hb tb]; inversion H; subst; clear H;
      try destruct (IHta _ _ H2); split; constructor; assumption.
Qed.
(* end hide *)

Lemma Rep_intersperse :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n (intersperse y l) <->
    Rep x n l \/ x = y /\ Rep x (S n - length l) l.
(* begin hide *)
Proof.
            Hint Constructors Rep.
  split; revert n.
    induction l as [| h t]; cbn; intros.
      inversion H; subst. left. constructor.
      destruct (intersperse y t) eqn: Heq.
        inv H.
          left. constructor.
          inv H2. left. do 2 constructor.
          inv H2. left. constructor.
        inv H.
          left. constructor.
          inv H2.
Admitted.
(* end hide *)

(** ** [Exists] *)

(** Zaimplementuj induktywny predykat [Exists]. [Exists P l] zachodzi, gdy
    lista [l] zawiera taki element, który spełnia predykat [P]. *)

(* begin hide *)
Inductive Exists {A : Type} (P : A -> Prop) : list A -> Prop :=
    | Exists_head :
        forall (h : A) (t : list A), P h -> Exists P (h :: t)
    | Exists_tail :
        forall (h : A) (t : list A), Exists P t -> Exists P (h :: t).
(* end hide *)

Lemma Exists_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l <-> exists x : A, elem x l /\ P x.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists h. split; [constructor | assumption].
      destruct IHExists as [x [H1 H2]].
        exists x. split; try right; assumption.
    destruct 1 as [x [H1 H2]]. induction H1.
      left. assumption.
      right. apply IHelem; assumption.
Qed.
(* end hide *)

Lemma Exists_nil :
  forall (A : Type) (P : A -> Prop),
    Exists P [] <-> False.
(* begin hide *)
Proof.
  split; inversion 1.
Qed.
(* end hide *)

Lemma Exists_cons :
  forall (A : Type) (P : A -> Prop) (h : A) (t : list A),
    Exists P (h :: t) <-> P h \/ Exists P t.
(* begin hide *)
Proof.
  split.
    inversion 1; subst; [left | right]; assumption.
    destruct 1; [left | right]; assumption.
Qed.
(* end hide *)

Lemma Exists_length :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l -> 1 <= length l.
(* begin hide *)
Proof.
  induction 1; cbn; apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma Exists_snoc :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Exists P (snoc x l) <-> Exists P l \/ P x.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H; subst; clear H; [right | left]; assumption.
      inversion H; subst; clear H.
        do 2 left. assumption.
        destruct (IHt H1).
          left. right. assumption.
          right. assumption.
    destruct 1.
      induction H; cbn; [left | right]; assumption.
      induction l as [| h t]; cbn; [left | right]; assumption.
Qed.
(* end hide *)

Lemma Exists_app :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Exists P (l1 ++ l2) <-> Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  split.
    induction l1 as [| h1 t1]; cbn; intros.
      right. assumption.
      inversion H; subst; clear H.
        do 2 left. assumption.
        destruct (IHt1 H1).
          left; right. assumption.
          right. assumption.
    destruct 1.
      induction H; cbn.
        left. assumption.
        right. assumption.
      induction l1 as [| h t]; cbn.
        assumption.
        right. assumption.
Qed.
(* end hide *)

Lemma Exists_rev :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P (rev l) <-> Exists P l.
(* begin hide *)
Proof.
  intros A P. assert (forall l : list A, Exists P l -> Exists P (rev l)).
    induction 1; cbn; rewrite Exists_app.
      right. constructor. assumption.
      left. assumption.
    split; intro.
      rewrite <- rev_inv. apply H, H0.
      apply H, H0.
Qed.
(* end hide *)

Lemma Exists_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    Exists P (map f l) -> Exists (fun x : A => P (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  inversion H; subst; clear H.
    left. assumption.
    right. apply IHt, H1.
Qed.
(* end hide *)

Lemma Exists_join :
  forall (A : Type) (P : A -> Prop) (ll : list (list A)),
    Exists P (join ll) <->
    Exists (fun l : list A => Exists  P l) ll.
(* begin hide *)
Proof.
  split.
    induction ll as [| h t]; cbn; intros.
      inversion H.
      rewrite Exists_app in H. destruct H.
        left. assumption.
        right. apply IHt, H.
    induction ll as [| h t]; cbn; intros;
    inversion H; subst; clear H.
      rewrite Exists_app. left. assumption.
      rewrite Exists_app. right. apply IHt, H1.
Qed.
(* end hide *)

Lemma Exists_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    Exists P (replicate n x) <-> 1 <= n /\ P x.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; intros;
    inversion H; subst; clear H.
      split.
        apply le_n_S, le_0_n.
        assumption.
      destruct (IHn' H1). split.
        apply le_trans with n'.
          assumption.
          apply le_S, le_n.
        assumption.
    destruct 1, n as [| n']; cbn.
      inversion H.
      left. assumption.
Qed.
(* end hide *)

Lemma Exists_nth :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l <->
    exists (n : nat) (x : A), nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists 0, h. split; trivial.
      destruct IHExists as (n & x & H1 & H2).
        exists (S n), x. split; assumption.
    destruct 1 as (n & x & H1 & H2).
      pose (nth_spec A l n). rewrite H1 in y.
        rewrite y, Exists_app, Exists_cons. right. left. assumption.
Qed.
(* end hide *)

Lemma Exists_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P l ->
    match remove n l with
        | None => True
        | Some (x, l') => ~ P x -> Exists P l'
    end.
(* begin hide *)
Proof.
  intros; revert n.
  induction H; cbn; intros.
    destruct n as [| n'].
      intro. contradiction.
      destruct (remove n' t).
        destruct p. intro. left. assumption.
        trivial.
    destruct n as [| n'].
      intro. assumption.
      specialize (IHExists n'). destruct (remove n' t).
        destruct p. intro. right. apply IHExists. assumption.
        assumption.
Qed.
(* end hide *)

Lemma Exists_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P (take n l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn; inversion H; subst; clear H.
      left. assumption.
      right. apply (IHt _ H1).
Qed.
(* end hide *)

Lemma Exists_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P (drop n l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      right. apply (IHt _ H).
Qed.
(* end hide *)

Lemma Exists_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Exists P l -> Exists P (take n l) \/ Exists P (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. assumption.
    destruct n as [| n']; cbn.
      right. assumption.
      inversion H; subst; clear H.
        do 2 left. assumption.
        destruct (IHt n' H1).
          left. right. assumption.
          right. assumption.
Qed.
(* end hide *)

Lemma Exists_cycle :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exists P (cycle n l) <-> Exists P l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn', Exists_snoc, !Exists_cons. firstorder.
Qed.
(* end hide *)

Lemma Exists_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      Exists P l <-> P x \/ Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  split.
    intro. revert l1 l2 n x H. induction H0; cbn; intros.
      destruct n as [| n'].
        inv H0. left. assumption.
        destruct (splitAt n' t).
          destruct p, p. inv H0. right. do 2 left. assumption.
          inv H0.
      destruct n as [| n'].
        inv H. do 2 right. assumption.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. inv H. decompose [or] (IHExists _ _ _ _ Heq).
            left. assumption.
            right. left. right. assumption.
            do 2 right. assumption.
          inv H.
    revert l1 l2 n x H. induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inv H. decompose [or] H0; clear H0.
          left. assumption.
          inv H1.
          right. assumption.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. inv H. specialize (IHt _ _ _ x Heq).
            decompose [or] H0; clear H0.
              right. apply IHt. left. assumption.
              inv H1.
                left. assumption.
                right. apply IHt. right. left. assumption.
              right. apply IHt. do 2 right. assumption.
              inv H.
Restart.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  rewrite Exists_app, Exists_cons. firstorder.
Qed.
(* end hide *)

Lemma Exists_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat) (x : A),
    Exists P (insert l n x) <-> P x \/ Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite Exists_cons, Exists_nil. reflexivity.
    destruct n as [| n'].
      rewrite !Exists_cons. reflexivity.
      rewrite !Exists_cons, IHt. firstorder.
Qed.
(* end hide *)

Lemma Exists_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Exists P l' <->
      Exists P (take n l) \/ P x \/ Exists P (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. rewrite Exists_nil, Exists_cons, drop_0. firstorder.
      destruct (replace t n' x) eqn: Heq; inv H.
        rewrite ?Exists_cons, (IHt _ _ _ Heq), or_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Exists_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P (filter p l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
    destruct (p h).
      inversion H; subst; clear H.
        left. assumption.
        right. apply IHt, H1.
      right. apply IHt, H.
Qed.
(* end hide *)

Lemma Exists_filter_conv :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P l ->
      Exists P (filter p l) \/
      Exists P (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction 1; cbn.
    destruct (p h); cbn.
      do 2 left. assumption.
      right; left. assumption.
    destruct (p h), IHExists as [IH | IH]; cbn.
      left; right. assumption.
      right. assumption.
      left. assumption.
      right; right. assumption.
Qed.
(* end hide *)

Lemma Exists_filter_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ Exists P (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    inversion H0.
    case_eq (p h); intros; rewrite H1 in *.
      inversion H0; subst; clear H0.
        rewrite H, H1 in H3. congruence.
        apply IHt; assumption.
      apply IHt; assumption.
Qed.
(* end hide *)

Lemma Exists_partition :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      Exists P l <-> Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H.
  inversion H; subst; clear H. split; intro.
    apply Exists_filter_conv. assumption.
    destruct H; apply Exists_filter in H; assumption.
Qed.
(* end hide *)

Lemma Exists_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P (takeWhile p l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  try destruct (p h); inversion H; subst; clear H.
    left. assumption.
    right. apply IHt, H1.
Qed.
(* end hide *)

Lemma Exists_takeWhile_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ Exists P (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    inversion H0.
    case_eq (p h); intros; rewrite H1 in *; inversion H0; subst; clear H0.
        rewrite H, H1 in H3. congruence.
        apply IHt; assumption.
Qed.
(* end hide *)

Lemma Exists_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P (dropWhile p l) -> Exists P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h).
      right. apply IHt, H.
      assumption.
Qed.
(* end hide *)

Lemma Exists_takeWhile_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Exists P l -> Exists P (takeWhile p l) \/ Exists P (dropWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    destruct (p h).
      do 2 left. assumption.
      right; left. assumption.
    destruct (p h), IHExists.
      left; right. assumption.
      right. assumption.
      apply Exists_takeWhile in H0. right; right. assumption.
      apply Exists_dropWhile in H0. right; right. assumption.
Qed.
(* end hide *)

Lemma Exists_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        Exists P l <-> Exists P b \/ P x \/ Exists P e.
(* begin hide *)
Proof.
  intros. apply span_spec in H0.
  rewrite H0, Exists_app, Exists_cons.
  reflexivity.
Qed.
(* end hide *)

Lemma Exists_interesting :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (hb : B) (tb : list B),
    Exists (fun a : A => Exists (fun b : B => P (a, b)) tb) la ->
    Exists (fun a : A => Exists (fun b : B => P (a, b)) (hb :: tb)) la.
(* begin hide *)
Proof.
  induction 1.
    left. right. assumption.
    right. assumption.
Qed.
(* end hide *)

Lemma Exists_zip :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (lb : list B),
    Exists P (zip la lb) ->
      Exists (fun a : A => Exists (fun b : B => P (a, b)) lb) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H.
    induction lb as [| hb tb]; inversion H; subst; clear H.
      left. left. assumption.
      specialize (IHta _ H1). apply Exists_interesting. right. assumption.
Qed.
(* end hide *)

Lemma Exists_pmap :
  forall (A B : Type) (f : A -> option B) (P : B -> Prop) (l : list A),
    Exists P (pmap f l) <->
      Exists (fun x : A => match f x with | Some b => P b | _ => False end) l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (f h) eqn: Hfh.
        inversion H; subst.
          left. rewrite Hfh. assumption.
          right. apply IHt. assumption.
        right. apply IHt. assumption.
    induction l as [| h t]; cbn; inversion 1; subst; clear H.
      destruct (f h).
        left. assumption.
        contradiction.
      destruct (f h); try right; apply IHt, H1.
Restart.
  induction l as [| h t]; cbn; intros.
    rewrite ?Exists_nil. reflexivity.
    destruct (f h) eqn: H; cbn.
      rewrite ?Exists_cons, IHt, H. reflexivity.
      rewrite ?Exists_cons, IHt, H. tauto.
Qed.
(* end hide *)

Lemma Exists_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Exists P (intersperse x l) <->
    Exists P l \/ (P x /\ 2 <= length l).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct (intersperse x t) eqn: Heq.
        inv H.
          do 2 left. assumption.
          inv H1.
        inv H.
          do 2 left. assumption.
          inv H1.
            right. split; try assumption. destruct t; cbn in *.
              inv Heq.
              apply le_n_S, le_n_S, le_0_n.
            destruct (IHt H0).
              left. right. assumption.
              right. destruct H. split.
                assumption.
                destruct t; cbn in *.
                  inv H1.
                  apply le_n_S, le_n_S, le_0_n.
    destruct 1.
      induction H; cbn.
        destruct (intersperse x t); left; assumption.
        destruct (intersperse x t).
          inv IHExists.
          do 2 right. assumption.
      destruct H. destruct l as [| h [| h' t]]; cbn.
        inv H0.
        inv H0. inv H2.
        destruct (intersperse x t); cbn.
          right. left. assumption.
          right. left. assumption.
Qed.
(* end hide *)

(** ** [Forall] *)

(** Zaimplementuj induktywny predykat [Forall]. [Forall P l] jest
    spełniony, gdy każdy element listy [l] spełnia predykat [P]. *)

(* begin hide *)
Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
    | Forall_nil' : Forall P []
    | Forall_cons' :
        forall (h : A) (t : list A), P h -> Forall P t -> Forall P (h :: t).
(* end hide *)

Lemma Forall_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P l <-> forall x : A, elem x l -> P x.
(* begin hide *)
Proof.
  split.
    induction 1; intros.
      inv H.
      inv H1.
        assumption.
        apply IHForall. assumption.
    induction l as [| h t]; constructor.
      apply H. left.
      apply IHt. intros. apply H. right. assumption.
Qed.
(* end hide *)

Lemma Forall_nil :
  forall (A : Type) (P : A -> Prop),
    Forall P [] <-> True.
(* begin hide *)
Proof.
  split; constructor.
Qed.
(* end hide *)

Lemma Forall_cons :
  forall (A : Type) (P : A -> Prop) (h : A) (t : list A),
    Forall P (h :: t) <-> P h /\ Forall P t.
(* begin hide *)
Proof.
  split; inversion 1; constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_snoc :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Forall P (snoc x l) <-> Forall P l /\ P x.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inversion H; subst; clear H. split; assumption.
      inversion H; subst; clear H. destruct (IHt H3). split.
        constructor. 1-3: assumption.
    destruct 1.
      induction H; cbn; repeat constructor; try assumption.
Qed.
(* end hide *)

Lemma Forall_app :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  split.
    induction l1 as [| h1 t1]; cbn; intros.
      split; [constructor | assumption].
      inversion H; subst; clear H. destruct (IHt1 H3). split.
        constructor; assumption.
        assumption.
    destruct 1. induction H; cbn; try constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_rev :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P (rev l) <-> Forall P l.
(* begin hide *)
Proof.
  intros A P. assert (forall l : list A, Forall P l -> Forall P (rev l)).
    induction 1; cbn.
      constructor.
      rewrite Forall_app. split; repeat constructor; assumption.
    split; intro.
      rewrite <- rev_inv. apply H, H0.
      apply H, H0.
Qed.
(* end hide *)

Lemma Forall_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    Forall P (map f l) -> Forall (fun x : A => P (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    inversion H; subst; clear H. constructor.
      assumption.
      apply IHt, H3.
Qed.
(* end hide *)

Lemma Forall_join :
  forall (A : Type) (P : A -> Prop) (ll : list (list A)),
    Forall P (join ll) <-> Forall (fun l : list A => Forall P l) ll.
(* begin hide *)
Proof.
  split.
    induction ll as [| h t]; cbn; intros.
      constructor.
      rewrite Forall_app in H. destruct H. constructor.
        assumption.
        apply IHt, H0.
    induction ll as [| h t]; cbn; intros.
      constructor.
      inversion H; subst; clear H. apply Forall_app; auto.
Qed.
(* end hide *)

Lemma Forall_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    Forall P (replicate n x) <-> n = 0 \/ P x.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; intros.
      left. reflexivity.
      right. inversion H. assumption.
    destruct 1.
      subst. cbn. constructor.
      induction n as [| n']; cbn.
        constructor.
        constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_nth :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P l <-> forall n : nat, n < length l ->
      exists x : A, nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  split.
    induction 1; cbn; intros.
      inv H.
      destruct n as [| n']; cbn.
        exists h. split; trivial.
        apply IHForall. apply lt_S_n. assumption.
    induction l as [| h t]; cbn; intros.
      constructor.
      destruct (H 0 (Nat.lt_0_succ _)) as [x [H1 H2]]; cbn in *.
        inv H1. constructor.
          assumption.
          apply IHt. intros. apply (H (S n)), lt_n_S. assumption.
Qed.
(* end hide *)

Lemma Forall_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P l ->
    match remove n l with
        | None => True
        | Some (x, l') => Forall P l'
    end.
(* begin hide *)
Proof.
  intros. revert n.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n'].
      assumption.
      specialize (IHForall n'). destruct (remove n' t).
        destruct p. constructor; assumption.
        trivial.
Qed.
(* end hide *)

Lemma Forall_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P l -> Forall P (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      constructor.
      inversion H; subst; clear H. constructor.
        assumption.
        apply (IHt _ H3).
Qed.
(* end hide *)

Lemma Forall_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P l -> Forall P (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      inversion H; subst; clear H. apply (IHt _ H3).
Qed.
(* end hide *)

Lemma Forall_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    Forall P (take n l) -> Forall P (drop n l) -> Forall P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      inversion H; subst; clear H. constructor.
        assumption.
        apply (IHt _ H4 H0).
Qed.
(* end hide *)

Lemma Forall_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      Forall P l <-> P x /\ Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  rewrite Forall_app, Forall_cons. firstorder.
Qed.
(* end hide *)

Lemma Forall_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat) (x : A),
      Forall P (insert l n x) <-> P x /\ Forall P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite Forall_cons, Forall_nil. reflexivity.
    destruct n as [| n'].
      rewrite 2!Forall_cons. reflexivity.
      rewrite 2!Forall_cons, IHt. firstorder.
Qed.
(* end hide *)

Lemma Forall_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      Forall P l' <->
      Forall P (take n l) /\ P x /\ Forall P (drop (S n) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. rewrite Forall_nil, Forall_cons, drop_0. firstorder.
      destruct (replace t n' x) eqn: Heq; inv H.
        rewrite ?Forall_cons, (IHt _ _ _ Heq), and_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Forall_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P l -> Forall P (filter p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h); try constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_filter_conv :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P (filter p l) ->
    Forall P (filter (fun x : A => negb (p x)) l) ->
      Forall P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h); cbn in *.
      inversion H; subst; clear H. constructor; auto.
      inversion H0; subst; clear H0. constructor; auto.
Qed.
(* end hide *)

Lemma Forall_filter_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) -> Forall P (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    case_eq (p h); intros.
      constructor.
        rewrite H. assumption.
        apply IHt. assumption.
      apply IHt. assumption.
Qed.
(* end hide *)

Lemma Forall_partition :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      Forall P l <-> Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H.
  inversion H; subst; clear H; split; intros.
    split; apply Forall_filter; assumption.
    destruct H. apply (Forall_filter_conv _ _ p); assumption.
Qed.
(* end hide *)

Lemma Forall_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P l -> Forall P (takeWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h); constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_takeWhile_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) -> Forall P (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    case_eq (p h); intros; constructor; firstorder.
Qed.
(* end hide *)

Lemma Forall_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P l -> Forall P (dropWhile p l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p h); try constructor; assumption.
Qed.
(* end hide *)

Lemma Forall_takeWhile_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    Forall P (takeWhile p l) -> Forall P (dropWhile p l) -> Forall P l.
(* begin hide *)
Proof.
  intros. rewrite <- (takeWhile_dropWhile_spec _ p), Forall_app.
  split; assumption.
Qed.
(* end hide *)

Lemma Forall_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        Forall P l <-> Forall P b /\ P x /\ Forall P e.
(* begin hide *)
Proof.
  intros. apply span_spec in H0.
  rewrite H0, Forall_app, Forall_cons.
  reflexivity.
Qed.
(* end hide *)

Lemma Forall_zip :
  forall (A B : Type) (PA : A -> Prop) (PB : B -> Prop)
  (la : list A) (lb : list B),
    Forall PA la -> Forall PB lb ->
      Forall (fun '(a, b) => PA a /\ PB b) (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    constructor.
    destruct lb as [| hb tb].
      constructor.
      inversion H; inversion H0; subst; clear H H0. constructor.
        split; assumption.
        apply IHta; assumption.
Qed.
(* end hide *)

Lemma Forall_pmap :
  forall (A B : Type) (f : A -> option B) (P : B -> Prop) (l : list A),
    Forall (fun x : A => match f x with | Some b => P b | _ => False end) l ->
      Forall P (pmap f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    inversion H; subst; clear H. destruct (f h).
      constructor; try apply IHt; assumption.
      apply IHt. assumption.
Qed.
(* end hide *)

Lemma Forall_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Forall P (intersperse x l) <->
    Forall P l /\ (2 <= length l -> P x).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      split; [constructor | inversion 1].
      destruct (intersperse x t) eqn: Heq.
        inv H. destruct (IHt H3). split.
          constructor; assumption.
          intro. apply H0. destruct t as [| h' [| h'' t']]; cbn in *.
            inv H1. inv H5.
            inv Heq.
            apply le_n_S, le_n_S, le_0_n.
        inv H. inv H3. destruct (IHt H4). split.
          constructor; assumption.
          intro. assumption.
    destruct 1. induction H; cbn in *.
      constructor.
      destruct (intersperse x t) eqn: Heq.
        repeat constructor; assumption.
        constructor; [assumption | constructor].
          apply H0. destruct t; cbn in *.
            inv Heq.
            apply le_n_S, le_n_S, le_0_n.
          apply IHForall. intro. apply H0. destruct t; cbn in *.
            inv Heq.
            lia.
Qed.
(* end hide *)

Lemma Forall_impl :
  forall (A : Type) (P Q : A -> Prop) (l : list A),
    (forall x : A , P x -> Q x) ->
      Forall P l -> Forall Q l.
(* begin hide *)
Proof.
  induction 2; cbn; constructor.
    apply H. assumption.
    apply IHForall.
Qed.
(* end hide *)

Lemma Forall_Exists :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Forall P l -> ~ Exists (fun x : A => ~ P x) l.
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    inversion H.
    inversion H1; contradiction.
Qed.
(* end hide *)

Lemma Exists_Forall :
  forall (A : Type) (P : A -> Prop) (l : list A),
    Exists P l -> ~ Forall (fun x : A => ~ P x) l.
(* begin hide *)
Proof.
  induction 1; cbn; intro;
  rewrite Forall_cons in H0; destruct H0; contradiction.
Qed.
(* end hide *)

(** ** [AtLeast] *)

(** Czas uogólnić relację [Rep] oraz predykaty [Exists] i [Forall]. Zdefiniuj
    w tym celu relację [AtLeast]. Zdanie [AtLeast P n l] zachodzi, gdy na
    liście [l] jest co najmniej [n] elementów spełniających predykat [P]. *)

(* begin hide *)
Inductive AtLeast {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
    | AL_0 :
        forall l : list A, AtLeast P 0 l
    | AL_S :
        forall (n : nat) (h : A) (t : list A),
          P h -> AtLeast P n t -> AtLeast P (S n) (h :: t)
    | AL_skip :
        forall (n : nat) (h : A) (t : list A),
          AtLeast P n t -> AtLeast P n (h :: t).
(* begin hide *)

Lemma AtLeast_le :
  forall (A : Type) (P : A -> Prop) (n m : nat) (l : list A),
    AtLeast P n l -> m <= n -> AtLeast P m l.
(* begin hide *)
Proof.
  intros A P n m l H. generalize dependent m.
  induction H; intros.
    inversion H. constructor.
    destruct m as [| m'].
      constructor.
      constructor.
        assumption.
        apply IHAtLeast, le_S_n, H1.
      constructor. apply IHAtLeast, H0.
Qed.
(* end hide *)

Lemma AtLeast_cons :
  forall (A : Type) (P : A -> Prop) (n : nat) (h : A) (t : list A),
    AtLeast P n (h :: t) <->
    AtLeast P n t \/ P h /\ AtLeast P (n - 1) t.
(* begin hide *)
Proof.
  split; intros.
    inv H.
      left. constructor.
      right. cbn. rewrite <- minus_n_O. split; assumption.
      left. assumption.
    decompose [and or] H; clear H.
      constructor. assumption.
      destruct n as [| n'].
        constructor.
        cbn in H2. rewrite <- minus_n_O in H2. constructor; assumption.
Qed.
(* end hide *)

Lemma AtLeast_cons' :
  forall (A : Type) (P : A -> Prop) (n : nat) (h : A) (t : list A),
    AtLeast P (S n) (h :: t) -> AtLeast P n t.
(* begin hide *)
Proof.
  intros. inv H.
    assumption.
    apply AtLeast_le with (S n).
      assumption.
      apply le_S, le_n.
Qed.
(* end hide *)

Lemma AtLeast_length :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    AtLeast P n l -> n <= length l.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    apply le_n_S, IHAtLeast.
    apply le_trans with (length t).
      assumption.
      apply le_S, le_n.
Qed.
(* end hide *)

Lemma AtLeast_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtLeast P n l -> AtLeast P n (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma AtLeast_S_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtLeast P n l -> P x -> AtLeast P (S n) (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    induction l as [| h t]; cbn.
      repeat constructor; assumption.
      apply AL_skip. assumption.
    constructor.
      assumption.
      apply IHAtLeast, H1.
    apply AL_skip, IHAtLeast, H0.
Qed.
(* end hide *)

Lemma AtLeast_Exists :
  forall (A : Type) (P : A -> Prop) (l : list A),
    AtLeast P 1 l <-> Exists P l.
(* begin hide *)
Proof.
  split.
    remember 1 as n. induction 1; inversion Heqn; subst.
      left. assumption.
      right. apply IHAtLeast. reflexivity.
    induction 1.
      constructor.
        assumption.
        constructor.
      constructor 3. assumption.
Qed.
(* end hide *)

Lemma AtLeast_Forall :
  forall (A : Type) (P : A -> Prop) (l : list A),
    AtLeast P (length l) l <-> Forall P l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      constructor.
      inversion H; subst; clear H.
        constructor; auto.
        apply AtLeast_length in H2. lia.
    induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma AtLeast_Rep :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    AtLeast (fun y : A => x = y) n l <-> Rep x n l.
(* begin hide *)
Proof.
  split; induction 1; subst; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_app_l :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n l1 -> AtLeast P n (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_app_r :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n l2 -> AtLeast P n (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_plus_app :
  forall (A : Type) (P : A -> Prop) (n1 n2 : nat) (l1 l2 : list A),
    AtLeast P n1 l1 -> AtLeast P n2 l2 ->
      AtLeast P (n1 + n2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    apply AtLeast_app_r. assumption.
    1-2: constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_app_conv :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n (l1 ++ l2) ->
      exists n1 n2 : nat, AtLeast P n1 l1 /\ AtLeast P n2 l2 /\ n = n1 + n2.
(* begin hide *)
Proof.
  intros A P n l1. generalize dependent n.
  induction l1 as [| h t]; cbn; intros.
    exists 0, n. repeat split.
      constructor.
      assumption.
    inversion H; subst; clear H.
      exists 0, 0. repeat constructor.
      destruct (IHt _ _ H4) as (n1 & n2 & Hn1 & Hn2 & Heq).
        exists (S n1), n2. subst. cbn. repeat constructor; auto.
      destruct (IHt _ _ H2) as (n1 & n2 & Hn1 & Hn2 & Heq).
        exists n1, n2. subst. repeat constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_app :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n (l1 ++ l2) <->
    exists n1 n2 : nat,
      AtLeast P n1 l1 /\ AtLeast P n2 l2 /\ n = n1 + n2.
(* begin hide *)
Proof.
  split.
    apply AtLeast_app_conv.
    destruct 1 as (n1 & n2 & H1 & H2 & H3); subst.
      apply AtLeast_plus_app; assumption.
Qed.
(* end hide *)

Lemma AtLeast_app_comm :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    AtLeast P n (l1 ++ l2) -> AtLeast P n (l2 ++ l1).
(* begin hide *)
Proof.
  intros. apply AtLeast_app_conv in H.
  destruct H as (n1 & n2 & H1 & H2 & H3); subst.
  rewrite plus_comm. apply AtLeast_plus_app; assumption.
Qed.
(* end hide *)

Lemma AtLeast_rev :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    AtLeast P n (rev l) <-> AtLeast P n l.
(* begin hide *)
Proof.
  assert (forall (A : Type) P n (l : list A),
            AtLeast P n l -> AtLeast P n (rev l)).
    induction 1; cbn.
      constructor.
      apply AtLeast_app_comm; cbn. constructor; assumption.
      rewrite <- (plus_0_r n). apply AtLeast_plus_app.
        assumption.
        constructor.
    split; intro.
      rewrite <- rev_inv. apply H, H0.
      apply H, H0.
Qed.
(* end hide *)

Lemma AtLeast_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (n : nat) (l : list A),
    AtLeast (fun x : A => P (f x)) n l ->
      AtLeast P n (map f l).
(* begin hide *)
Proof.
  induction 1; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_map_conv :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (n : nat) (l : list A),
    (forall x y : A, f x = f y -> x = y) -> AtLeast P n (map f l) ->
      AtLeast (fun x : A => P (f x)) n l.
(* begin hide *)
Proof.
  intros A B P f n l. generalize dependent n.
  induction l as [| h t]; cbn; intros;
  inversion H0; subst; clear H0; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    n <> 0 -> P x -> AtLeast P n (replicate n x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    contradiction H. reflexivity.
    destruct n' as [| n'']; cbn in *.
      constructor; [assumption | constructor].
    constructor.
      assumption.
      apply IHn'; [inversion 1 | assumption].
Qed.
(* end hide *)

Lemma AtLeast_replicate_conv :
  forall (A : Type) (P : A -> Prop) (n m : nat) (x : A),
    AtLeast P m (replicate n x) -> m = 0 \/ m <= n /\ P x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros;
  inversion H; subst; clear H.
    1-2: left; reflexivity.
    destruct (IHn' _ _ H4) as [H | [H1 H2]]; subst; right.
      split; [apply le_n_S, le_0_n | assumption].
      split; [apply le_n_S, H1 | assumption].
    destruct (IHn' _ _ H2) as [H | [H1' H2']]; subst.
      left. reflexivity.
      right. split; try apply le_S; assumption.
Qed.
(* end hide *)

Lemma AtLeast_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (m : nat),
    AtLeast P m l -> forall n : nat,
      match remove n l with
          | None => True
          | Some (_, l') => AtLeast P (m - 1) l'
      end.
(* begin hide *)
Proof.
  induction 1; cbn; intro m.
    destruct (remove m l).
      destruct p. 1-2: constructor.
    destruct m as [| m']; cbn in *.
      rewrite <- minus_n_O. assumption.
      specialize (IHAtLeast m'). destruct (remove m' t).
        destruct p. destruct n as [| n']; cbn in *.
          constructor.
          rewrite <- minus_n_O in *. constructor; assumption.
        trivial.
    destruct m as [| m']; cbn in *.
      apply AtLeast_le with n.
        assumption.
        destruct n as [| n']; cbn.
          apply le_n.
          rewrite <- minus_n_O. apply le_S, le_n.
      specialize (IHAtLeast m'). destruct (remove m' t).
        destruct p. constructor. assumption.
        trivial.
Qed.
(* end hide *)

Lemma AtLeast_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m : nat),
    AtLeast P m (take n l) -> AtLeast P m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn; inversion H; subst; clear H.
      1-3: constructor.
        assumption.
        apply (IHt _ _ H4).
      constructor. apply (IHt _ _ H2).
Qed.
(* end hide *)

Lemma AtLeast_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m : nat),
    AtLeast P m (drop n l) -> AtLeast P m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      assumption.
      constructor. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma AtLeast_take_drop :
  forall (A : Type) (P : A -> Prop) (n m : nat) (l : list A),
    AtLeast P n l ->
    exists n1 n2 : nat,
      AtLeast P n1 (take m l) /\ AtLeast P n2 (drop m l) /\ n = n1 + n2.
(* begin hide *)
Proof.
  intros. apply AtLeast_app. rewrite app_take_drop. assumption.
Qed.
(* end hide *)

Lemma AtLeast_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      forall m : nat,
        AtLeast P m l ->
        exists m1 mx m2 : nat,
          AtLeast P m1 l1 /\ AtLeast P mx [x] /\ AtLeast P m2 l2 /\
          m1 + mx + m2 = m.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. inv H0.
        exists 0, 0, 0. repeat constructor.
        exists 0, 1, n. repeat constructor; assumption.
        exists 0, 0, m. repeat constructor. assumption.
    destruct (splitAt n' t) eqn: Heq.
      destruct p, p. inv H. inv H0.
        exists 0, 0, 0. repeat constructor.
        destruct (IHt _ _ _ _ Heq _ H4) as
                 (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4).
          exists (S m1), mx, m2. subst. firstorder. constructor; assumption.
        destruct (IHt _ _ _ _ Heq _ H2) as
                 (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4).
          exists m1, mx, m2. subst. firstorder. apply AL_skip. assumption.
      inv H.
Qed.
(* end hide *)

Lemma AtLeast_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    AtLeast P n l -> forall (m : nat) (x : A),
      AtLeast P n (insert l m x).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    destruct m as [| m']; cbn.
      apply AL_skip. constructor; assumption.
      constructor.
        assumption.
        apply IHAtLeast.
    destruct m as [| m']; cbn.
      do 2 apply AL_skip. assumption.
      apply AL_skip. apply IHAtLeast.
Qed.
(* end hide *)

Lemma AtLeast_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' -> AtLeast P m l ->
      AtLeast P (m - 1) l'.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. inv H0; cbn.
        constructor.
        rewrite <- minus_n_O. constructor. assumption.
        apply AtLeast_le with m.
          constructor. assumption.
          lia.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0; cbn.
        constructor.
        rewrite <- minus_n_O. specialize (IHt _ _ _ _ Heq H4).
          destruct n; cbn in *.
            constructor.
            rewrite <- minus_n_O in IHt. constructor; assumption.
        specialize (IHt _ _ _ _ Heq H2). constructor. assumption.
Qed.
(* end hide *)

Lemma AtLeast_replace' :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' -> AtLeast P m l -> P x ->
      AtLeast P m l'.
(* begin hide *)
Proof.
  intros until 2. revert l' n x H.
  induction H0; cbn; intros.
    constructor.
    destruct n0; cbn in *.
      inv H1. constructor; assumption.
      destruct (replace t n0 x) eqn: Heq; inv H1. constructor.
        assumption.
        apply (IHAtLeast _ _ _ Heq H2).
    destruct n0; cbn in H.
      inv H. constructor. assumption.
      destruct (replace t n0 x) eqn: Heq; inv H.
        constructor. apply (IHAtLeast _ _ _ Heq H1).
Qed.
(* end hide *)

Lemma AtLeast_replace_conv :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' -> AtLeast P m l' -> AtLeast P (m - 1) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n'].
      inv H. inv H0; cbn.
        constructor.
        rewrite <- minus_n_O. constructor. assumption.
        apply AtLeast_le with m.
          constructor. assumption.
          lia.
      destruct (replace t n' x) eqn: Heq; inv H. inv H0; cbn.
        constructor.
        rewrite <- minus_n_O. specialize (IHt _ _ _ _ Heq H4).
          destruct n; cbn in *.
            constructor.
            rewrite <- minus_n_O in IHt. constructor; assumption.
        specialize (IHt _ _ _ _ Heq H2). constructor. assumption.
Qed.
(* end hide *)

Lemma AtLeast_replace_conv' :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n m : nat) (x y : A),
    replace l n x = Some l' -> nth n l = Some y -> P y ->
      AtLeast P m l' -> AtLeast P m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. inv H0. inv H2.
        constructor.
        constructor; assumption.
      constructor. assumption.
    destruct (replace t n' x) eqn: Heq; inv H. inv H2; constructor.
      assumption.
      apply (IHt _ _ _ _ _ Heq H0 H1 H6).
      apply (IHt _ _ _ _ _ Heq H0 H1 H4).
Qed.
(* end hide *)

(* begin hide *)
(* TODO: [Exactly], [AtMost] dla [replace] *)
(* end hide *)

Lemma AtLeast_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    AtLeast P n (filter p l) -> AtLeast P n l.
(* begin hide *)
Proof.
  intros A P p n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h) eqn: Hph.
      inversion H; subst; clear H; constructor; auto.
      constructor. apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_filter_compat_true :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) ->
      AtLeast P (length (filter p l)) (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h) eqn: Hph; cbn.
      constructor.
        rewrite H. assumption.
        apply IHt, H.
      apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_filter_compat_false :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    (forall x : A, P x <-> p x = false) ->
      AtLeast P n (filter p l) -> n = 0.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0. reflexivity.
    destruct (p h) eqn: Hph.
      inv H0.
        reflexivity.
        rewrite H in H4. congruence.
        apply (IHt H H3).
      apply (IHt H H0).
Qed.
(* end hide *)

Lemma AtLeast_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    AtLeast P n (takeWhile p l) -> AtLeast P n l.
(* begin hide *)
Proof.
  intros A P p n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h) eqn: Heq.
      inversion H; subst; clear H; constructor; auto.
      inversion H. constructor.
Qed.
(* end hide *)

Lemma AtLeast_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    AtLeast P n (dropWhile p l) -> AtLeast P n l.
(* begin hide *)
Proof.
  intros A P p n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h) eqn: Heq.
      constructor; auto.
      inversion H; subst; clear H; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_takeWhile_true :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) ->
      AtLeast P (length (takeWhile p l)) (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h) eqn: Heq; cbn.
      constructor; [rewrite H | apply IHt]; assumption.
      constructor.
Qed.
(* end hide *)

Lemma AtLeast_takeWhile_false :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    (forall x : A, P x <-> p x = false) ->
      AtLeast P n (takeWhile p l) -> n = 0.
(* begin hide *)
Proof.
  intros A P p n l. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    inversion H0. reflexivity.
    destruct (p h) eqn: Heq.
      inversion H0; subst; clear H0.
        reflexivity.
        rewrite H, Heq in H4. congruence.
        apply IHt; assumption.
      inversion H0. reflexivity.
Qed.
(* end hide *)

Lemma AtLeast_dropWhile_true :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A) (n : nat),
    (forall x : A, P x <-> p x = true) ->
      AtLeast P n l -> AtLeast P (n - length (takeWhile p l)) (dropWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H0. cbn. constructor.
    destruct (p h) eqn: Heq; cbn.
      inversion H0; subst; clear H0.
        cbn. constructor.
        cbn. apply IHt; assumption.
        destruct n as [| n']; cbn.
          constructor.
          apply IHt.
            assumption.
            apply AtLeast_le with (S n').
              assumption.
              apply le_S, le_n.
      rewrite <- minus_n_O. assumption.
Qed.
(* end hide *)

Lemma AtLeast_dropWhile_false :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A) (n : nat),
    (forall x : A, P x <-> p x = false) ->
      AtLeast P n l -> AtLeast P n (dropWhile p l).
(* begin hide *)
Proof.
  induction 2; cbn.
    constructor.
    destruct (p h) eqn: Heq.
      rewrite H, Heq in H0. congruence.
      constructor; assumption.
    destruct (p h) eqn: Heq; try constructor; assumption.
Qed.
(* end hide *)

Lemma AtLeast_zip :
  forall (A B : Type) (PA : A -> Prop) (PB : B -> Prop)
  (la : list A) (lb : list B) (n : nat),
    AtLeast (fun '(a, b) => PA a /\ PB b) n (zip la lb) ->
      AtLeast PA n la /\ AtLeast PB n lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    inversion H. split; constructor.
    destruct lb as [| hb tb]; inversion H; subst; clear H.
      1-2: split; constructor.
      destruct H3. destruct (IHta _ _ H4). split; constructor; auto.
      destruct (IHta _ _ H2). split; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_findIndices :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A) (n : nat),
    (forall x : A, P x <-> p x = true) ->
      AtLeast P n l -> n <= length (findIndices p l).
(* begin hide *)
Proof.
  induction 2.
    apply le_0_n.
    cbn. destruct (H h). rewrite (H2 H0). cbn. apply le_n_S.
      rewrite length_map. assumption.
    cbn. destruct (p h); cbn; rewrite length_map.
      apply le_S. assumption.
      assumption.
Qed.
(* end hide *)

Lemma AtLeast_1_elem :
  forall (A : Type) (P : A -> Prop) (l : list A),
    AtLeast P 1 l <-> exists x : A, elem x l /\ P x.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; cbn; inversion 1; subst; clear H.
      exists h. split; [left | assumption].
      destruct (IHt H2) as (x & IH1 & IH2).
        exists x. split; try right; assumption.
    destruct 1 as (x & H1 & H2). induction H1.
      repeat constructor. assumption.
      apply AL_skip, IHelem, H2.
Qed.
(* end hide *)

Lemma AtLeast_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    P x -> AtLeast P (length l - 1) (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        constructor.
        destruct (intersperse x t); inv Heq.
      constructor. destruct t; cbn in *; constructor.
        assumption.
        rewrite <- minus_n_O in IHt. apply IHt, H.
Qed.
(* end hide *)

Lemma AtLeast_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    AtLeast P n l -> P x ->
      AtLeast P (n + (length l - 1)) (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    apply AtLeast_intersperse. assumption.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        inv H0. cbn. repeat constructor; assumption.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        rewrite <- plus_n_Sm. constructor.
          assumption.
          constructor.
            assumption.
            rewrite <- minus_n_O in IHAtLeast. apply IHAtLeast, H1.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        inv H. cbn. constructor.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        rewrite <- plus_n_Sm. apply AL_skip. constructor.
          assumption.
          rewrite <- minus_n_O in IHAtLeast. apply IHAtLeast, H0.
Qed.
(* end hide *)

Lemma AtLeast_intersperse'' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    AtLeast P n l -> ~ P x -> AtLeast P n (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          inv H0. constructor.
          destruct (intersperse x t); inv Heq.
      constructor.
        assumption.
        apply AL_skip. apply IHAtLeast, H1.
    destruct (intersperse x t) eqn: Heq.
      constructor. destruct t; cbn in *.
        inv H. constructor.
        destruct (intersperse x t); inv Heq.
      do 2 constructor. apply IHAtLeast, H0.
Qed.
(* end hide *)

(** ** [Exactly] *)

(** Zdefiniuj predykat [Exactly]. Zdanie [Exactly P n l] zachodzi, gdy
    na liście [l] występuje dokładnie [n] elementów spełniających predykat
    [P]. *)

(* begin hide *)
Inductive Exactly {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
    | Ex_0 : Exactly P 0 []
    | Ex_S :
        forall (n : nat) (h : A) (t : list A),
          P h -> Exactly P n t -> Exactly P (S n) (h :: t)
    | Ex_skip :
        forall (n : nat) (h : A) (t : list A),
          ~ P h -> Exactly P n t -> Exactly P n (h :: t).
(* end hide *)

Lemma Exactly_0_cons :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    Exactly P 0 (x :: l) <-> ~ P x /\ Exactly P 0 l.
(* begin hide *)
Proof.
  split; intros.
    inv H; firstorder.
    decompose [and or] H; clear H; constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_S_cons :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    Exactly P (S n) (x :: l) <->
    P x /\ Exactly P n l \/ ~ P x /\ Exactly P (S n) l.
(* begin hide *)
Proof.
  split; intros.
    inv H; firstorder.
    decompose [and or] H; clear H; constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_AtLeast :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exactly P n l -> AtLeast P n l.
(* begin hide *)
Proof.
  induction 1; constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_eq :
  forall (A : Type) (P : A -> Prop) (n m : nat) (l : list A),
    Exactly P n l -> Exactly P m l -> n = m.
(* begin hide *)
Proof.
  intros A P n m l H. generalize dependent m.
  induction H; cbn; intros.
    inversion H; subst. reflexivity.
    inversion H1; subst; clear H1.
      rewrite (IHExactly _ H6). reflexivity.
      contradiction.
    inversion H1; subst; clear H1.
      contradiction.
      apply IHExactly, H6.
Qed.
(* end hide *)

Lemma Exactly_length :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exactly P n l -> n <= length l.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_n.
    apply le_n_S. assumption.
    apply le_S. assumption.
Qed.
(* end hide *)

Lemma Exactly_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    Exactly P n l -> ~ P x -> Exactly P n (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    repeat constructor. assumption.
    1-2: constructor; [assumption | apply IHExactly, H1].
Qed.
(* end hide *)

Lemma Exactly_S_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    Exactly P n l -> P x -> Exactly P (S n) (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    repeat constructor. assumption.
    1-2: constructor; [assumption | apply IHExactly, H1].
Qed.
(* end hide *)

Lemma Exactly_app :
  forall (A : Type) (P : A -> Prop) (n1 n2 : nat) (l1 l2 : list A),
    Exactly P n1 l1 -> Exactly P n2 l2 -> Exactly P (n1 + n2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros; try constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_app_conv :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Exactly P n (l1 ++ l2) ->
      exists n1 n2 : nat,
        Exactly P n1 l1 /\ Exactly P n2 l2 /\ n = n1 + n2.
(* begin hide *)
Proof.
  intros A P n l1. generalize dependent n.
  induction l1 as [| h1 t1]; cbn; intros.
    exists 0, n. repeat constructor. assumption.
    inversion H; subst; clear H.
      destruct (IHt1 _ _ H4) as (n1 & n2 & H1 & H2 & Heq); subst.
        exists (S n1), n2. repeat constructor; assumption.
      destruct (IHt1 _ _ H4) as (n1 & n2 & H1 & H2 & Heq); subst.
        exists n1, n2. repeat constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_app_comm :
  forall (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Exactly P n (l1 ++ l2) -> Exactly P n (l2 ++ l1).
(* begin hide *)
Proof.
  intros. generalize dependent n.
  induction l1 as [| h t]; cbn; intros.
    rewrite app_nil_r. assumption.
    inversion H; subst; clear H; apply Exactly_app_conv in H4;
    destruct H4 as (n1 & n2 & H1 & H2 & Heq); subst.
      rewrite plus_comm, plus_n_Sm.
        apply Exactly_app; try constructor; assumption.
      rewrite plus_comm. apply Exactly_app; try constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_rev :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exactly P n (rev l) <-> Exactly P n l.
(* begin hide *)
Proof.
  intros A P. assert (forall (n : nat) (l : list A),
                        Exactly P n l -> Exactly P n (rev l)).
    induction 1; cbn.
      constructor.
      apply Exactly_app_comm. cbn. constructor; assumption.
      apply Exactly_app_comm. cbn. constructor; assumption.
    split; intros.
      rewrite <- rev_inv. apply H. assumption.
      apply H. assumption.
Qed.
(* end hide *)

Lemma Exactly_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (n : nat) (l : list A),
    (forall x y : A, f x = f y -> x = y) ->
    Exactly (fun x : A => P (f x)) n l <->
      Exactly P n (map f l).
(* begin hide *)
Proof.
  split.
    induction 1; cbn; constructor; auto.
    generalize dependent n.
      induction l as [| h t]; cbn; intros;
      inversion H0; subst; clear H0;
      constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    P x -> Exactly P n (replicate n x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; constructor; auto.
Qed.
(* end hide *)

Lemma Exactly_replicate_conv :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    Exactly P n (replicate n x) -> n = 0 \/ P x.
(* begin hide *)
Proof.
  destruct n as [| n']; cbn; intros.
    left. reflexivity.
    right. inversion H; subst; clear H.
      assumption.
      apply Exactly_length in H4. rewrite length_replicate in H4. lia.
Qed.
(* end hide *)

Lemma Exactly_replicate' :
  forall (A : Type) (P : A -> Prop) (n m : nat) (x : A),
    Exactly P n (replicate m x) <->
    n = 0 /\ m = 0 \/
    n = 0 /\ ~ P x \/
    n = m /\ P x.
(* begin hide *)
Proof.
  split.
    generalize dependent n.
    induction m as [| m']; cbn; inversion 1; subst.
      left. split; reflexivity.
      decompose [and or] (IHm' _ H4); subst; clear IHm'.
        do 2 right. split; trivial.
        contradiction.
        do 2 right. split; trivial.
      decompose [and or] (IHm' _ H4); subst; clear IHm'.
        right. left. split; trivial.
        right. left. split; trivial.
        contradiction.
    intro. decompose [and or] H; clear H; subst.
      cbn. constructor.
      induction m as [| m']; cbn; constructor; assumption.
      induction m as [| m']; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m1 m2 : nat),
    Exactly P m1 (take n l) -> Exactly P m2 l -> m1 <= m2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H; subst. apply le_0_n.
    destruct n as [| n']; cbn.
      inversion H. apply le_0_n.
      inversion H; inversion H0; subst; clear H H0; try contradiction.
        apply le_n_S. apply (IHt _ _ _ H5 H10).
        apply (IHt _ _ _ H5 H10).
Qed.
(* end hide *)

Lemma Exactly_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m1 m2 : nat),
    Exactly P m1 (drop n l) -> Exactly P m2 l -> m1 <= m2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H. apply le_0_n.
    destruct n as [| n']; cbn.
      inversion H; inversion H0; subst; clear H H0.
        specialize (IHt 0). rewrite drop_0 in IHt.
          specialize (IHt _ _ H5 H10). apply le_n_S, IHt.
        1-2: contradiction.
        specialize (IHt 0). rewrite drop_0 in IHt.
          apply (IHt _ _ H5 H10).
      inversion H0; subst; clear H0.
        apply le_S. apply (IHt _ _ _ H H5).
        apply (IHt _ _ _ H H5).
Qed.
(* end hide *)

Lemma Exactly_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n m : nat),
    Exactly P n l -> exists n1 n2 : nat,
      n = n1 + n2 /\ Exactly P n1 (take m l) /\ Exactly P n2 (drop m l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H; subst. exists 0, 0. repeat constructor.
    inversion H; subst; clear H.
      destruct m as [| m']; cbn.
        exists 0, (S n0). repeat constructor; assumption.
        destruct (IHt _ m' H4) as (n1 & n2 & IH1 & IH2 & IH3); subst.
          exists (S n1), n2. repeat constructor; assumption.
      destruct m as [| m']; cbn.
        exists 0, n. repeat constructor; assumption.
        destruct (IHt _ m' H4) as (n1 & n2 & IH1 & IH2 & IH3); subst.
          exists n1, n2. repeat constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      forall m : nat,
        Exactly P m l <->
        exists m1 mx m2 : nat,
          Exactly P m1 l1 /\ Exactly P mx [x] /\ Exactly P m2 l2 /\
          m1 + mx + m2 = m.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in *.
      inv H. split; intro.
        inv H.
          exists 0, 1, n. repeat constructor; assumption.
          exists 0, 0, m. repeat constructor; assumption.
          decompose [ex and] H; clear H; subst. inv H1. inv H0.
            cbn. constructor.
              assumption.
              inv H5. cbn. assumption.
            inv H5. cbn. constructor; assumption.
    destruct (splitAt n' t) eqn: Heq.
      destruct p, p. inv H. split; intro.
        inv H.
          rewrite (IHt _ _ _ _ Heq) in H4.
            destruct H4 as (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4); subst.
            exists (S m1), mx, m2. firstorder (constructor; assumption).
          rewrite (IHt _ _ _ _ Heq) in H4.
            destruct H4 as (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4); subst.
            exists m1, mx, m2. firstorder (constructor; assumption).
          destruct H as (m1 & mx & m2 & IH1 & IH2 & IH3 & IH4); subst.
            inv IH1.
              cbn. constructor.
                assumption.
                rewrite (IHt _ _ _ _ Heq). exists n, mx, m2. firstorder.
              constructor.
                assumption.
                rewrite (IHt _ _ _ _ Heq). exists m1, mx, m2. firstorder.
    inv H.
Qed.
(* end hide *)

Lemma Exactly_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) ->
      Exactly P (length (filter p l)) (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h) eqn: Hph; cbn.
      constructor.
        rewrite H. assumption.
        apply IHt, H.
      apply IHt, H.
Qed.
(* end hide *)

Lemma Exactly_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = true) ->
      Exactly P (length (takeWhile p l)) (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h) eqn: Hph; cbn; constructor.
      rewrite H. assumption.
      apply IHt, H.
Qed.
(* end hide *)

Lemma Exactly_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (l : list A),
    (forall x : A, P x <-> p x = true) ->
    Exactly P n l ->
      Exactly P (n - length (takeWhile p l)) (dropWhile p l).
(* begin hide *)
Proof.
  induction 2; cbn.
    constructor.
    destruct (p h) eqn: Hph; cbn.
      assumption.
      rewrite H, Hph in H0. congruence.
    destruct (p h) eqn: Hph; cbn.
      destruct n as [| n']; cbn in *.
        assumption.
        rewrite H in H0. contradiction.
      rewrite <- minus_n_O. constructor; assumption.
Qed.
(* end hide *)

Lemma Exactly_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool)
    (n : nat)(x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        Exactly P n l <->
        exists n1 n2 : nat,
          Exactly P n1 b /\ Exactly P n2 e /\
          if p x then S (n1 + n2) = n else n1 + n2 = n.
(* begin hide *)
Proof.
  intros. apply span_spec in H0. subst. split; intro.
    apply Exactly_app_conv in H0.
      destruct H0 as (n1 & n2 & H1 & H2 & H3). inv H2.
        destruct (p x) eqn: Hpx.
          exists n1, n0. repeat split; try assumption. apply plus_n_Sm.
          rewrite H in H6. congruence.
        destruct (p x) eqn: Hpx.
          rewrite H in H6. congruence.
          exists n1, n2. repeat split; assumption.
    destruct H0 as (n1 & n2 & IH1 & IH2 & IH3).
      destruct (p x) eqn: Hpx; subst.
        apply Exactly_app_comm. cbn. constructor.
          rewrite H. assumption.
          apply Exactly_app_comm, Exactly_app; assumption.
        apply Exactly_app_comm. cbn. constructor.
          intro. rewrite H in H0. congruence.
          apply Exactly_app_comm, Exactly_app; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Exactly vs span i AtLeast, AtMost *)
(* end hide *)

Lemma Exactly_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    Exactly P n l -> P x ->
      Exactly P (n + (length l - 1)) (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    destruct (intersperse x t) eqn: Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          specialize (IHExactly H1). inv IHExactly. constructor.
          destruct (intersperse x t); inv Heq.
      constructor.
        assumption.
        destruct t; cbn in *.
          inv Heq.
          rewrite <- plus_n_Sm. constructor.
            assumption.
            rewrite <- minus_n_O in IHExactly. apply IHExactly, H1.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        constructor; [assumption | apply IHExactly, H1].
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t); inv Heq.
          constructor.
            assumption.
            rewrite <- plus_n_Sm. constructor.
              assumption.
              rewrite <- minus_n_O in *. apply IHExactly, H1.
          constructor.
            assumption.
            rewrite <- plus_n_Sm. constructor.
              assumption.
              rewrite <- minus_n_O in IHExactly. apply IHExactly, H1.
Restart.
  intros. revert dependent n.
  functional induction @intersperse A x l; cbn; intros.
    inv H. constructor.
    destruct t; cbn in *.
      rewrite plus_0_r. assumption.
      destruct (intersperse x t); inv e0.
    destruct t; cbn in *.
      inv e0.
      rewrite <- plus_n_Sm. inv H.
        cbn. do 2 try constructor; try assumption.
          rewrite <- minus_n_O in IHl0.
            destruct (intersperse x t); inv e0; apply IHl0; assumption.
        apply Ex_skip; try constructor; try assumption.
          rewrite <- minus_n_O in IHl0.
            destruct (intersperse x t); inv e0; apply IHl0; assumption.
Qed.
(* end hide *)

Lemma Exactly_intersperse' :
  forall (A : Type) (P : A -> Prop) (x : A) (n : nat) (l : list A),
    Exactly P n l -> ~ P x ->
      Exactly P n (intersperse x l).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    specialize (IHExactly H1). destruct (intersperse x t).
      constructor; assumption.
      do 2 try constructor; assumption.
    specialize (IHExactly H1). destruct (intersperse x t).
      inv IHExactly. repeat constructor; assumption.
      do 2 try constructor; try assumption.
Qed.
(* end hide *)

(** ** [AtMost] *)

(** Zdefiniuj relację [AtMost]. Zdanie [AtMost P n l] zachodzi, gdy
    na liście [l] występuje co najwyżej [n] elementów spełniających
    predykat [P].

    Przykład: *)

(** [AtMost (fun n => n = 0) 3 [0; 1; 2; 3; 0]] zachodzi. *)

(** [AtMost (fun n => n < 5) 5 [1; 2; 3; 4; 5; 6; 7]] nie zachodzi. *)

(* begin hide *)
Inductive AtMost  {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
    | AM_0 : forall n : nat, AtMost P n []
    | AM_S :
        forall (n : nat) (h : A) (t : list A),
          ~ P h -> AtMost P n t -> AtMost P n (h :: t)
    | AM_skip :
        forall (n : nat) (h : A) (t : list A),
          AtMost P n t -> AtMost P (S n) (h :: t).
(* end hide *)

Lemma AtMost_0 :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    AtMost P 0 (x :: l) <-> ~ P x /\ AtMost P 0 l.
(* begin hide *)
Proof.
  split; intros.
    inv H. split; assumption.
    destruct H. constructor; assumption.
Qed.
(* end hide *)

Lemma AtMost_nil :
  forall (A : Type) (P : A -> Prop) (n : nat),
    AtMost P n [] <-> True.
(* begin hide *)
Proof.
  repeat constructor.
Qed.
(* end hide *)

Lemma AtMost_le :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    AtMost P n l -> forall m : nat, n <= m -> AtMost P m l.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    constructor.
      assumption.
      apply IHAtMost. assumption.
    destruct m as [| m'].
      inv H0.
      apply AM_skip, IHAtMost, le_S_n, H0.
Qed.
(* end hide *)

Lemma AtMost_S_cons :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtMost P (S n) (x :: l) <->
    (~ P x /\ AtMost P (S n) l) \/ AtMost P n l.
(* begin hide *)
Proof.
  split; intros.
    inv H; [left | right].
      split; assumption.
      cbn. assumption.
    decompose [and or] H; clear H.
      constructor; assumption.
      constructor; assumption.
Qed.
(* end hide *)

Lemma AtMost_S_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtMost P n l -> AtMost P (S n) (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply AM_skip. constructor.
    constructor; assumption.
    apply AM_skip. assumption.
Qed.
(* end hide *)

Lemma AtMost_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtMost P n l -> ~ P x -> AtMost P n (snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn; intro.
    repeat constructor; assumption.
    constructor; [assumption | apply IHAtMost, H1].
    apply AM_skip. apply IHAtMost, H0.
Qed.
(* end hide *)

Lemma AtMost_S :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    AtMost P n l -> AtMost P (S n) l.
(* begin hide *)
Proof.
  induction 1; constructor; assumption.
Qed.
(* end hide *)

(** * Relacje między listami *)

(* begin hide *)
(* TODO: zrób coś z tym (dziwna relacja [bool_le]) *)
Inductive bool_le : bool -> bool -> Prop :=
    | ble_refl : forall b : bool, bool_le b b
    | ble_false_true : bool_le false true.

(*
Definition bool_le (b1 b2 : bool) : Prop :=
match b1, b2 with
    | false, _ => True
    | true, false => False
    | true, true => True
end.
*)
(* end hide *)

(** ** Listy jako termy *)

(** Zdefiniuj relację [Sublist]. Zdanie [Sublist l1 l2] zachodzi, gdy
    [l2] jest podtermem listy [l1], tzn. jej ogonem, ogonem ogona,
    ogonem ogona ogona etc.

    Przykład: *)

(** [Sublist [4; 5] [1; 2; 3; 4; 5]] zachodzi. *)

(** [Sublist [3; 4] [1; 2; 3; 4; 5]] nie zachodzi. *)

(* begin hide *)
Inductive Sublist {A : Type} : list A -> list A -> Prop :=
    | Sublist_direct :
        forall (h : A) (t : list A), Sublist t (h :: t)
    | Sublist_cons :
        forall (x : A) (l1 l2 : list A),
          Sublist l1 l2 -> Sublist l1 (x :: l2).
(* end hide *)

Lemma Sublist_length :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> length l1 < length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_n.
    apply lt_S. assumption.
Qed.
(* end hide *)

Lemma Sublist_cons_l :
  forall (A : Type) (x : A) (l : list A), ~ Sublist (x :: l) l.
(* begin hide *)
Proof.
  repeat intro. apply Sublist_length in H. cbn in H. lia.
Qed.
(* end hide *)

Lemma Sublist_cons_l' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Sublist (x :: l1) l2 -> Sublist l1 l2.
(* begin hide *)
Proof.
  intros until 1. revert l1 H.
  induction l2 as [| h t]; cbn; intros.
    inv H.
    inv H.
      do 2 constructor.
      constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Sublist_nil_cons :
  forall (A : Type) (x : A) (l : list A), Sublist [] (x :: l).
(* begin hide *)
Proof.
  intros A x l. revert x.
  induction l as [| h t]; cbn; constructor; apply IHt.
Qed.
(* end hide *)

Lemma Sublist_irrefl :
  forall (A : Type) (l : list A), ~ Sublist l l.
(* begin hide *)
Proof.
  repeat intro. apply Sublist_length in H. lia.
Qed.
(* end hide *)

Lemma Sublist_antisym :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> ~ Sublist l2 l1.
(* begin hide *)
Proof.
  repeat intro.
  apply Sublist_length in H.
  apply Sublist_length in H0.
  lia.
Qed.
(* end hide *)

Lemma Sublist_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Sublist l1 l2 -> Sublist l2 l3 -> Sublist l1 l3.
(* begin hide *)
Proof.
  intros until 1. revert l3.
  induction H; intros.
    apply Sublist_cons_l' in H. assumption.
    apply IHSublist. apply Sublist_cons_l' in H0. assumption.
Qed.
(* end hide *)

Lemma Sublist_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Sublist l1 l2 -> Sublist (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Sublist_snoc_inv :
  forall (A : Type) (x y : A) (l1 l2 : list A),
    Sublist (snoc x l1) (snoc y l2) -> Sublist l1 l2 /\ x = y.
(* begin hide *)
Proof.
  intros.
  remember (snoc x l1) as l1'.
  remember (snoc y l2) as l2'.
  revert l1 l2 Heql1' Heql2'.
  induction H; cbn; intros; subst.
    destruct l2 as [| h2 t2]; inv Heql2'.
      apply (f_equal isEmpty) in H1. rewrite isEmpty_snoc in H1. inv H1.
      apply snoc_inv in H1. destruct H1; subst. split; constructor.
    destruct l3 as [| h3 t3]; cbn in *.
      inv Heql2'. inv H.
      inv Heql2'. destruct (IHSublist _ _ eq_refl eq_refl); subst.
        split; constructor. assumption.
Qed.
(* end hide *)

Lemma Sublist_app_l :
  forall (A : Type) (l1 l2 : list A),
    l1 <> [] -> Sublist l2 (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    contradiction.
    destruct t as [| h' t']; cbn.
      constructor.
      constructor. apply IHt. inversion 1.
Qed.
(* end hide *)

Lemma Sublist_app_l' :
  forall (A : Type) (l1 l2 l3 : list A),
    Sublist l1 l2 -> Sublist l1 (l3 ++ l2).
(* begin hide *)
Proof.
  intros until 1. revert l1 l2 H.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Sublist_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Sublist l1 l2 -> Sublist (l1 ++ l3) (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; intros; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Sublist_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Sublist l1 l2 -> Sublist (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Sublist_join :
  forall (A : Type) (l1 l2 : list (list A)),
    ~ elem [] l2 -> Sublist l1 l2 -> Sublist (join l1) (join l2).
(* begin hide *)
Proof.
  induction 2; cbn.
    rewrite elem_cons' in H. destruct h.
      firstorder.
      apply Sublist_app_l. inversion 1.
    apply Sublist_app_l'. apply IHSublist.
      intro. apply H. right. assumption.
Qed.
(* end hide *)

Lemma Sublist_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Sublist (replicate n x) (replicate m x) <-> n < m.
(* begin hide *)
Proof.
  split.
    revert n. induction m as [| m']; cbn; intros.
      inv H.
      destruct n as [| n']; cbn in *.
        apply Nat.lt_0_succ.
        apply lt_n_S. apply IHm'. inv H.
          constructor.
          apply Sublist_cons_l' in H2. assumption.
    intro. assert (exists k : nat, m = n + S k).
      revert n H. induction m as [| m']; cbn; intros.
        inv H.
        destruct n as [| n'].
          exists m'. reflexivity.
          destruct (IHm' _ (lt_S_n _ _ H)) as (k & IH). subst.
            exists k. rewrite <- ?plus_n_Sm. cbn. reflexivity.
      destruct H0 as (k & H'). subst.
        rewrite <- Nat.add_succ_comm, replicate_plus_comm, replicate_plus.
          apply Sublist_app_l'. cbn. constructor.
Qed.
(* end hide *)

Lemma Sublist_replicate' :
  forall (A : Type) (n m : nat) (x y : A),
    Sublist (replicate n x) (replicate m y) <->
    n < m /\ (n <> 0 -> x = y).
(* begin hide *)
Proof.
  split.
    revert m x y. induction n as [| n'], m as [| m']; intros.
      inv H.
      split.
        apply Nat.lt_0_succ.
        intro. contradiction.
      inv H.
      rewrite <- ?snoc_replicate in H. apply Sublist_snoc_inv in H.
        destruct H. destruct (IHn' _ _ _ H); subst. split.
          apply lt_n_S. assumption.
          reflexivity.
    destruct 1. destruct n as [| n'].
      destruct m as [| m'].
        inv H.
        cbn. apply Sublist_nil_cons.
      specialize (H0 ltac:(inversion 1)). subst. rewrite Sublist_replicate.
        assumption.
Qed.
(* end hide *)

Lemma Sublist_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Sublist (iterate f n x) (iterate f m x) ->
      n = 0 \/ n = m \/ (n <= m /\ f x = x).
(* begin hide *)
Proof.
  intros.
  remember (iterate f n x) as l1.
  remember (iterate f m x) as l2.
  revert x n m Heql1 Heql2.
  induction H; intros.
    destruct n, m; cbn in *; inversion Heql2; subst.
      left. reflexivity.
      right. destruct m; cbn in *.
        inversion H1.
        inversion H1.
Admitted.
(* end hide *)

Lemma Sublist_tail :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 ->
    forall t1 t2 : list A, tail l1 = Some t1 -> tail l2 = Some t2 ->
      Sublist t1 t2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H0. destruct t2; inv H. constructor.
    inv H1. destruct l1; inv H0. inv H.
      do 2 constructor.
      cbn in *. constructor. apply IHSublist; reflexivity.
Qed.
(* end hide *)

Lemma Sublist_last :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> l1 = [] \/ last l1 = last l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    destruct t; cbn; [left | right]; reflexivity.
    destruct IHSublist; [left | right].
      assumption.
      rewrite H0. destruct l2; cbn.
        inv H.
        reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Sublist vs insert, remove, take *)
(* end hide *)

Lemma Sublist_spec :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 <->
    exists n : nat,
      n < length l2 /\ l1 = drop (S n) l2.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists 0. rewrite drop_0. split; [apply Nat.lt_0_succ | reflexivity].
      destruct IHSublist as (n & IH1 & IH2). subst.
        exists (S n). split.
          apply lt_n_S. assumption.
          reflexivity.
    destruct 1 as (n & H1 & H2). subst. revert n H1.
      induction l2 as [| h t]; cbn; intros.
        inv H1.
        destruct t as [| h' t']; cbn in *.
          constructor.
          destruct n as [| n']; cbn in *.
            constructor.
            constructor. apply IHt. apply lt_S_n, H1.
Qed.
(* end hide *)

Lemma Sublist_drop_r :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall n : nat, Sublist (drop n l1) l2.
(* begin hide *)
Proof.
  induction 1; intros.
    revert n h. induction t as [| h' t']; cbn; intros.
      constructor.
      destruct n; cbn.
        constructor.
        constructor. apply IHt'.
    constructor. apply IHSublist.
Qed.
(* end hide *)

Lemma Sublist_drop :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall n : nat,
      n < length l2 -> Sublist (drop n l1) (drop n l2).
(* begin hide *)
Proof.
  intros. rewrite Sublist_spec in *. destruct H as (m & H1 & H2).
  subst. rewrite length_drop, ?drop_drop.
  revert n m H0 H1.
  induction l2 as [| h t]; cbn; intros.
    inv H0.
    destruct n as [| n'].
      rewrite plus_0_r. cbn. exists m. split; [assumption | reflexivity].
      destruct m as [| m'].
        cbn. exists 0. split.
          lia.
          rewrite drop_drop, plus_comm. cbn. reflexivity.
        apply lt_S_n in H0. apply lt_S_n in H1.
          destruct (IHt _ _ H0 H1) as (k & Hk1 & Hk2).
          exists (S k). split.
            Focus 2. replace (drop (S m' + S n') t) with
                             (drop 1 (drop (S m' + n') t)).
              rewrite Hk2. rewrite ?drop_drop. f_equal. lia.
              rewrite drop_drop. f_equal. lia.
            destruct (length t - n') eqn: Hlt.
              inv Hk1.
              destruct n as [| n''].
Abort.
(* end hide *)

Lemma Sublist_replace :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall (l1' l2' : list A) (n : nat) (x : A),
      replace l1 n x = Some l1' -> replace l2 (n + length l1) x = Some l2' ->
        Sublist l1' l2'.
(* begin hide *)
Proof.
  intros. rewrite Sublist_spec in *.
  destruct H as (m & Hm1 & Hm2). subst.
  rewrite replace_spec in *.
Abort.
(* end hide *)

Lemma Sublist_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list A),
    Sublist la1 la2 /\ Sublist lb1 lb2 /\
      ~ Sublist (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists bool, bool, [true], [false; false; true], [true], [false; true].
  cbn. firstorder.
    constructor. constructor.
    constructor.
    intro. inv H. inv H2. inv H1.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Sublist vs zipWith, unzip, unzipWith *)
(* end hide *)

Lemma Sublist_any_false :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 -> any p l2 = false -> any p l1 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (any p t); cbn.
      rewrite Bool.orb_true_r in H. inv H.
      reflexivity.
    destruct (p x); cbn in H0.
      inv H0.
      apply IHSublist, H0.
Qed.
(* end hide *)

Lemma Sublist_any_true :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 -> any p l1 = true -> any p l2 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    rewrite H, Bool.orb_true_r. reflexivity.
    rewrite (IHSublist H0), Bool.orb_true_r. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Sublist_all *)
(* end hide *)

Lemma Sublist_findLast :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 -> forall x : A,
      findLast p l1 = Some x -> findLast p l2 = Some x.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    rewrite H. reflexivity.
    rewrite (IHSublist _ H0). reflexivity.
Qed.
(* end hide *)

Lemma Sublist_removeLast :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 ->
      match removeLast p l1, removeLast p l2 with
          | None, None => True
          | None, Some (x, l2') => l1 = l2' \/ Sublist l1 l2'
          | x, None => False
          | Some (x, l1'), Some (y, l2') => x = y /\ Sublist l1' l2'
      end.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (removeLast p t) eqn: Heq.
      destruct p0. split; constructor.
      destruct (p h); cbn.
        left. reflexivity.
        trivial.
    destruct (removeLast p l1) eqn: Heq1.
      destruct p0. destruct (removeLast p l2) eqn: Heq2.
        destruct p0, IHSublist; subst. split.
          reflexivity.
          constructor. assumption.
        inv IHSublist.
      destruct (removeLast p l2) eqn: Heq2.
        destruct p0, IHSublist; subst.
          right. constructor.
          right. constructor. assumption.
        destruct (p x).
          right. assumption.
          trivial.
Qed.
(* end hide *)

Lemma Sublist_findIndex :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 -> forall n : nat,
      findIndex p l1 = Some n -> exists m : nat,
        findIndex p l2 = Some m.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (p h).
      exists 0. reflexivity.
      rewrite H. exists (S n). reflexivity.
    destruct (p x).
      exists 0. reflexivity.
      destruct (IHSublist _ H0) as (m & IH). rewrite IH.
        exists (S m). reflexivity.
Qed.
(* end hide *)

Lemma Sublist_filter :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  exists unit, (fun _ => false), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_findIndices :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (findIndices p l1) (findIndices p l2).
(* begin hide *)
Proof.
  exists unit, (fun _ => false), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_takeWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists unit, (fun _ => false), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_dropWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  exists unit, (fun _ => true), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_pmap :
  exists (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Sublist (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  exists unit, unit, (fun _ => None), [], [tt]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Sublist_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Sublist l1 l2 -> Sublist (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (intersperse x t); repeat constructor.
    destruct (intersperse x l2) eqn: Heq.
      inv IHSublist.
      do 2 constructor. assumption.
Qed.
(* end hide *)

Lemma Sublist_elem :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall x : A, elem x l1 -> elem x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. assumption.
    right. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_In :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall x : A, In x l1 -> In x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    right. assumption.
    right. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_NoDup :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> NoDup l2 -> NoDup l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. assumption.
    inv H0. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_Dup :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Dup l1 -> Dup l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    right. assumption.
    right. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_Rep :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Sublist l1 l2 -> forall n : nat, Rep x n l1 -> Rep x n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. assumption.
    constructor. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_Exists :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Sublist l1 l2 -> Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros; right; try apply IHSublist; assumption.
Qed.
(* end hide *)

Lemma Sublist_Forall :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Sublist l1 l2 -> Forall P l2 -> Forall P l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. assumption.
    inv H0. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor. assumption.
    constructor. apply IHSublist. assumption.
Qed.
(* end hide *)

Lemma Sublist_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtMost P n l2 -> AtMost P n l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
      assumption.
      apply AtMost_S. assumption.
    inv H0.
      apply IHSublist. assumption.
      apply AtMost_S, IHSublist, H3.
Qed.
(* end hide *)

(** ** Prefiksy *)

(** Zdefiniuj induktywną relację [Prefix]. Zdanie [Prefix l1 l2]
    zachodzi, gdy lista [l1] pokrywa się z początkowym fragmentem
    listy [l2] o dowolnej długości.

    Przykład: *)

(** [Prefix [1; 2] [1; 2; 3; 4; 5]] zachodzi. *)

(** [Prefix [1; 2] [1; 1; 2; 3; 5]] nie zachodzi. *)

(* begin hide*)
Inductive Prefix {A : Type} : list A -> list A -> Prop :=
    | Prefix_nil : forall l : list A, Prefix [] l
    | Prefix_cons :
        forall (x : A) (l1 l2 : list A),
          Prefix l1 l2 -> Prefix (x :: l1) (x :: l2).
(* end hide *)

Lemma Prefix_spec :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 <-> exists l3 : list A, l2 = l1 ++ l3.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists l. reflexivity.
      destruct IHPrefix as (l3 & IH). subst. exists l3. reflexivity.
    destruct 1 as (l3 & H). subst.
      induction l1 as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_refl :
  forall (A : Type) (l : list A), Prefix l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Prefix l1 l2 -> Prefix l2 l3 -> Prefix l1 l3.
(* begin hide *)
Proof.
  intros A l1 l2 l3 H. revert l3.
  induction H; intros.
    constructor.
    inv H0. constructor. apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_wasym :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix l2 l1 -> l1 = l2.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H. constructor.
    f_equal. apply IHPrefix. inv H0. assumption.
Qed.
(* end hide *)

Lemma Prefix_length :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> length l1 <= length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    apply le_n_S. assumption.
Qed.
(* end hide *)

Lemma Prefix_snoc :
  exists (A : Type) (l1 l2 : list A),
    Prefix l1 l2 /\ exists x : A, ~ Prefix (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  exists bool, [true], [true; true]. split.
    repeat constructor.
    exists false. cbn. intro. inv H. inv H1.
Qed.
(* end hide *)

Lemma Prefix_app :
  forall (A : Type) (l1 l2 l3 : list A),
    Prefix l1 l2 -> Prefix (l3 ++ l1) (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Prefix_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Prefix l1 l2 -> Prefix l1 (l2 ++ l3).
(* begin hide *)
Proof.
  intros. rewrite Prefix_spec in *. destruct H as (l3' & H); subst.
  exists (l3' ++ l3). rewrite app_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Prefix_rev_l :
  forall (A : Type) (l : list A),
    Prefix (rev l) l -> l = rev l.
(* begin hide *)
Proof.
  intros. apply Prefix_spec in H. destruct H as (l3 & H).
  rewrite H at 1. apply (f_equal length) in H.
  rewrite length_app, length_rev, plus_comm in H.
  destruct l3.
    rewrite app_nil_r. reflexivity.
    cbn in H. lia.
Qed.
(* end hide *)

Lemma Prefix_rev_r :
  forall (A : Type) (l : list A),
    Prefix l (rev l) -> l = rev l.
(* begin hide *)
Proof.
  intros. apply Prefix_spec in H. destruct H as (l3 & H).
  rewrite H at 1. apply (f_equal length) in H.
  rewrite length_app, length_rev, plus_comm in H.
  destruct l3.
    rewrite app_nil_r. reflexivity.
    cbn in H. lia.
Qed.
(* end hide *)

Lemma Prefix_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Prefix l1 l2 -> Prefix (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    apply Prefix_app. assumption.
Qed.
(* end hide *)

Lemma Prefix_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Prefix (replicate n x) (replicate m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert m x. induction n as [| n']; cbn; intros.
      apply le_0_n.
      inv H. destruct m as [| m']; inv H3. apply le_n_S, (IHn' _ x H1).
    revert m x. induction n as [| n']; cbn; intros.
      constructor.
      destruct m as [| m'].
        inv H.
        cbn. constructor. apply IHn', le_S_n, H.
Qed.
(* end hide *)

Lemma Prefix_replicate_inv_l :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    Prefix l (replicate n x) ->
      exists m : nat, m <= n /\ l = replicate m x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    exists 0. cbn. split; [apply le_0_n | reflexivity].
    inv H. destruct n as [| n']; inv H3.
      destruct (IHt _ _ H1) as (m & IH1 & IH2); subst. exists (S m); split.
        apply le_n_S. assumption.
        cbn. reflexivity.
Qed.
(* end hide *)

Lemma Prefix_replicate_inv_r :
  exists (A : Type) (l : list A) (n : nat) (x : A),
    Prefix (replicate n x) l /\
      ~ exists m : nat, n <= m /\ l = replicate m x.
(* begin hide *)
Proof.
  exists bool, [true; false], 1, true. cbn. split.
    do 2 constructor.
    destruct 1 as (m & H1 & H2). destruct m as [| m'].
      inv H1.
      cbn in H2. inv H2. destruct m'; inv H0.
Qed.
(* end hide *)

Lemma Prefix_replicate' :
  forall (A : Type) (n : nat) (x y : A),
    Prefix (replicate n x) (replicate n y) <-> n = 0 \/ x = y.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; cbn; intros.
      left. reflexivity.
      right. inv H. reflexivity.
    destruct 1; subst; cbn.
      1-2: apply Prefix_refl.
Qed.
(* end hide *)

Lemma Prefix_replicate'' :
  forall (A : Type) (n m : nat) (x y : A),
    Prefix (replicate n x) (replicate m y) <->
    n = 0 \/ n <= m /\ x = y.
(* begin hide *)
Proof.
  split.
    revert m x y. induction n as [| n']; cbn; intros.
      left. reflexivity.
      inv H. destruct m as [| m']; inv H3.
        destruct (IHn' _ _ _ H1) as [H | [IH1 IH2]]; subst.
          right. split.
            apply le_n_S, le_0_n.
            reflexivity.
          right. split.
            apply le_n_S. assumption.
            reflexivity.
    intro. decompose [and or] H; clear H; subst.
      cbn. constructor.
      rewrite Prefix_replicate. assumption.
Qed.
(* end hide *)

Lemma Prefix_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Prefix (iterate f n x) (iterate f m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert m x. induction n as [| n']; cbn; intros.
      apply le_0_n.
      inv H. destruct m as [| m']; inv H3. apply le_n_S, (IHn' _ _ H1).
    revert m x. induction n as [| n']; cbn; intros.
      constructor.
      destruct m as [| m'].
        inv H.
        cbn. constructor. apply IHn', le_S_n, H.
Qed.
(* end hide *)

Lemma Prefix_insert :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall (n : nat) (x : A),
      n <= length l1 -> Prefix (insert l1 n x) (insert l2 n x).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct n; inv H. rewrite insert_0. do 2 constructor.
    destruct n as [| n'].
      do 2 constructor. specialize (IHPrefix _ x0 (le_0_n (length l1))).
        rewrite ?insert_0 in IHPrefix. inv IHPrefix. assumption.
      constructor. apply IHPrefix. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma Prefix_replace :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall (n : nat) (x : A),
      match replace l1 n x, replace l2 n x with
          | Some l1', Some l2' => Prefix l1' l2'
          | _, _ => True
      end.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    trivial.
    destruct n as [| n']; cbn.
      constructor. assumption.
      specialize (IHPrefix n' x0).
        destruct (replace l1 n' x0), (replace l2 n' x0).
          constructor. assumption.
          1-3: trivial.
Qed.
(* end hide *)

Lemma insert_length_ge :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    length l <= n -> insert l n x = snoc x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      inv H.
      f_equal. apply IHt. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma Prefix_insert' :
  exists (A : Type) (l1 l2 : list A),
    Prefix l1 l2 /\
    exists (n : nat) (x : A),
      length l1 < n /\ ~ Prefix (insert l1 n x) (insert l2 n x).
(* begin hide *)
Proof.
  exists bool, [true], [true; true]. split.
    do 2 constructor.
    exists 2, false. cbn. split.
      apply le_n.
      intro. inv H. inv H1.
Qed.
(* end hide *)

Lemma Prefix_take_l :
  forall (A : Type) (l : list A) (n : nat), Prefix (take n l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct n as [| n']; cbn; constructor. apply IHt.
Qed.
(* end hide *)

Lemma Prefix_take :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall n : nat, Prefix (take n l1) (take n l2).
(* begin hide *)
Proof.
  induction 1; intros.
    rewrite take_nil. constructor.
    destruct n as [| n']; cbn; constructor. apply IHPrefix.
Qed.
(* end hide *)

Lemma Prefix_drop :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall n : nat, Prefix (drop n l1) (drop n l2).
(* begin hide *)
Proof.
  induction 1; intros.
    rewrite drop_nil. constructor.
    destruct n as [| n']; cbn.
      constructor. assumption.
      apply IHPrefix.
Qed.
(* end hide *)

Lemma Prefix_zip :
  forall (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Prefix la1 la2 -> Prefix lb1 lb2 ->
      Prefix (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  intros until 1. revert lb1 lb2. induction H; cbn; intros.
    constructor.
    inv H0; constructor. apply IHPrefix. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs unzip, zipWith, unzipWith *)
(* end hide *)

Lemma Prefix_any_false :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> any p l2 = false -> any p l1 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (any p l2).
      rewrite Bool.orb_true_r in H0. congruence.
      rewrite Bool.orb_false_r in H0. rewrite H0, IHPrefix; reflexivity.
Qed.
(* end hide *)

Lemma Prefix_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> any p l1 = true -> any p l2 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    congruence.
    destruct (any p l1).
      rewrite IHPrefix, Bool.orb_true_r; reflexivity.
      rewrite Bool.orb_false_r in H0. rewrite H0. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Prefix_all_false :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> all p l1 = false -> all p l2 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    congruence.
    destruct (all p l1).
      rewrite Bool.andb_true_r in H0. rewrite H0. cbn. reflexivity.
      rewrite IHPrefix, Bool.andb_false_r; reflexivity.
Qed.
(* end hide *)

Lemma Prefix_all_true :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> all p l2 = true -> all p l1 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (all p l2).
      rewrite Bool.andb_true_r in H0. rewrite H0, IHPrefix; reflexivity.
      rewrite Bool.andb_false_r in H0. congruence.
Qed.
(* end hide *)

Lemma Prefix_find_None :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> find p l2 = None -> find p l1 = None.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x).
      assumption.
      apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_find_Some :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> forall x : A,
      find p l1 = Some x -> find p l2 = Some x.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    destruct (p x).
      assumption.
      apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_findIndex_None :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> findIndex p l2 = None -> findIndex p l1 = None.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x).
      assumption.
      destruct (findIndex p l2).
        inv H0.
        rewrite IHPrefix; reflexivity.
Qed.
(* end hide *)

Lemma Prefix_findIndex_Some :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> forall i : nat,
      findIndex p l1 = Some i -> findIndex p l2 = Some i.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    destruct (p x).
      assumption.
      destruct (findIndex p l1); inv H0.
        rewrite (IHPrefix _ eq_refl). reflexivity.
Qed.
(* end hide *)

Lemma Prefix_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> count p l1 <= count p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    destruct (p x); try apply le_n_S; assumption.
Qed.
(* end hide *)

Lemma Prefix_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_findIndices :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (findIndices p l1) (findIndices p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; apply Prefix_map; assumption.
Qed.
(* end hide *)

Lemma Prefix_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Prefix (takeWhile p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    destruct (p h); constructor. assumption.
Qed.
(* end hide *)

Lemma Prefix_takeWhile_pres :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_dropWhile :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs findLast, removeFirst i removeLast *)
(* end hide *)

Lemma Prefix_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Prefix_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Prefix l1 l2 -> Prefix (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (intersperse x l1), (intersperse x l2).
      apply Prefix_refl.
      do 2 constructor.
      inv IHPrefix.
      do 2 constructor. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs groupBy *)
(* end hide *)

Lemma Prefix_elem :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall x : A, elem x l1 -> elem x l2.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H.
    inv H0.
      constructor.
      constructor. apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_elem_conv :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall x : A, ~ elem x l2 -> ~ elem x l1.
(* begin hide *)
Proof.
  induction 1; intros.
    intro. inv H0.
    intro. apply H0. inv H1.
      constructor.
      assert (~ elem x0 l2).
        rewrite elem_cons' in H0. intro. apply H0. right. assumption.
        specialize (IHPrefix _ H1). contradiction.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs In *)
(* end hide *)

Lemma Prefix_NoDup :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> NoDup l2 -> NoDup l1.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    inv H0. constructor.
      intro. apply H3. apply Prefix_elem with l1; assumption.
      apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_Dup :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> Dup l1 -> Dup l2.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H.
    inv H0.
      constructor. apply Prefix_elem with l1; assumption.
      right. apply IHPrefix. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs Rep *)
(* end hide *)

Lemma Prefix_Exists :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Prefix l1 l2 -> Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H.
    inv H0.
      constructor. assumption.
      right. apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_Forall :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Prefix l1 l2 -> Forall P l2 -> Forall P l1.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    inv H0. constructor.
      assumption.
      apply IHPrefix. assumption.
Qed.
(* end hide *)

Lemma Prefix_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. constructor.
    inv H0; constructor; try apply IHPrefix; assumption.
Qed.
(* end hide *)

Lemma Prefix_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtMost P n l2 -> AtMost P n l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    inv H0; constructor; try apply IHPrefix; assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Prefix vs Exactly - raczej nic z tego *)
(* end hide *)

Lemma Sublist_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true], [false; true]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Prefix_spec' :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 <-> exists n : nat, l1 = take n l2.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists 0. rewrite take_0. reflexivity.
      destruct IHPrefix as (n & IH). exists (S n). rewrite IH. reflexivity.
    destruct 1 as (n & H); subst. apply Prefix_take_l.
Qed.
(* end hide *)

(** ** Sufiksy *)

(** Zdefiniuj induktywną relację [Suffix]. Zdanie [Suffix l1 l2]
    zachodzi, gdy [l1] pokrywa się z końcowym fragmentem listy [l2]
    o dowolnej długości.

    Przykłady: *)

(** [Suffix [4; 5] [1; 2; 3; 4; 5]] zachodzi. *)

(** [Suffix [3; 4] [1; 2; 3; 4; 5]] nie zachodzi. *)

(* begin hide *)
Inductive Suffix {A : Type} : list A -> list A -> Prop :=
    | Suffix_refl :
        forall l : list A, Suffix l l
    | Suffix_cons :
        forall (x : A) (l1 l2 : list A),
          Suffix l1 l2 -> Suffix l1 (x :: l2).
(* end hide *)

Lemma Suffix_spec :
  forall (A : Type) (l1 l2 : list A),
    Suffix l1 l2 <-> exists l3 : list A, l2 = l3 ++ l1.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      exists []. cbn. reflexivity.
      destruct IHSuffix as (l3 & IH); subst.
        exists (x :: l3). reflexivity.
    destruct 1 as (l3 & H). subst.
      induction l3 as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Suffix_cons_inv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Suffix (x :: l1) l2 -> Suffix l1 l2.
(* begin hide *)
Proof.
  intros. apply Suffix_spec in H. destruct H as (l3 & H). subst.
  induction l3 as [| h t]; cbn.
    constructor. apply Suffix_refl.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Suffix_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Suffix l1 l2 -> Suffix l2 l3 -> Suffix l1 l3.
(* begin hide *)
Proof.
  intros A l1 l2 l3 H. revert l3.
  induction H; intros.
    assumption.
    apply IHSuffix. apply Suffix_cons_inv in H0. assumption.
Qed.
(* end hide *)

Lemma Suffix_wasym :
  forall (A : Type) (l1 l2 : list A),
    Suffix l1 l2 -> Suffix l2 l1 -> l1 = l2.
(* begin hide *)
Proof.
  intros.
  apply Suffix_spec in H. destruct H as (l1' & H1).
  apply Suffix_spec in H0. destruct H0 as (l2' & H2).
  subst. apply (f_equal length) in H2. rewrite ?length_app in H2.
  destruct l2', l1'; cbn in H2; try lia. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Suffix_nil_l :
  forall (A : Type) (l : list A), Suffix [] l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Suffix_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Suffix l1 l2 -> Suffix (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros; constructor; assumption.
Qed.
(* end hide *)

Lemma Suffix_Sublist :
  forall (A : Type) (l1 l2 : list A),
    Suffix l1 l2 <-> Sublist l1 l2 \/ l1 = l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      right. reflexivity.
      left. destruct IHSuffix; subst.
        apply Sublist_trans with l2.
          assumption.
          constructor.
        constructor.
    destruct 1; subst.
      induction H; constructor.
        apply Suffix_refl.
        assumption.
      apply Suffix_refl.
Qed.
(* end hide *)

Lemma Prefix_Suffix :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 <-> Suffix (rev l1) (rev l2).
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      apply Suffix_nil_l.
      rewrite <- ?snoc_app_singl. apply Suffix_snoc. assumption.
    assert (forall l1 l2 : list A, Suffix l1 l2 -> Prefix (rev l1) (rev l2)).
      induction 1; cbn.
        apply Prefix_refl.
        apply Prefix_app_r. assumption.
      intro. specialize (H _ _ H0). rewrite ?rev_inv in H. assumption.
Qed.
(* end hide *)

(** ** Listy jako ciągi *)

(** Zdefiniuj relację [Subseq]. Zdanie [Subseq l1 l2] zachodzi, gdy
    lista [l2] zawiera wszystkie elementy listy [l1] w takiej samej
    kolejności, w jakiej występują one w [l1], ale może też zawierać
    inne elementy.

    Przykłady: *)

(** [Subseq [1; 3; 5] [0; 1; 5; 2; 3; 4; 5]] zachodzi. *)

(** [Subseq [1; 3; 5] [3; 1; 5; 3; 6]] nie zachodzi. *)

(* begin hide *)
Inductive Subseq {A : Type} : list A -> list A -> Prop :=
    | Subseq_nil :
        forall l : list A, Subseq [] l
    | Subseq_cons :
        forall (x : A) (l1 l2 : list A),
          Subseq l1 l2 -> Subseq (x :: l1) (x :: l2)
    | Subseq_skip :
        forall (x : A) (l1 l2 : list A),
          Subseq l1 l2 -> Subseq l1 (x :: l2).
(* end hide *)

Lemma Subseq_refl :
  forall (A : Type) (l : list A), Subseq l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_cons_inv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq (x :: l1) (x :: l2) -> Subseq l1 l2.
(* begin hide *)
Proof.
  intros A x l1 l2. revert l1.
  induction l2 as [| h1 t1]; cbn; intros.
    inv H.
      assumption.
      inv H2.
    inv H.
      assumption.
      inv H2.
        constructor. apply IHt1. constructor. assumption.
        constructor. apply IHt1. apply Subseq_skip. assumption.
Qed.
(* end hide *)

Lemma Subseq_cons_inv_l :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq (x :: l1) l2 -> Subseq l1 l2.
(* begin hide *)
Proof.
  intros. revert x l1 H.
  induction l2 as [| h1 t1]; cbn; intros; inv H.
    constructor. assumption.
    constructor. apply IHt1 with x. assumption.
Qed.
(* end hide *)

Lemma Subseq_isEmpty_l :
  forall (A : Type) (l1 l2 : list A),
    isEmpty l1 = true -> Subseq l1 l2.
(* begin hide *)
Proof.
  destruct l1; cbn; intros.
    constructor.
    congruence.
Qed.
(* end hide *)

Lemma Subseq_nil_r :
  forall (A : Type) (l : list A),
    Subseq l [] -> l = [].
(* begin hide *)
Proof.
  inversion 1. reflexivity.
Qed.
(* end hide *)

Lemma Subseq_length :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> length l1 <= length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    apply le_n_S. assumption.
    apply le_S. assumption.
Qed.
(* end hide *)

Lemma Subseq_trans : 
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq l2 l3 -> Subseq l1 l3.
(* begin hide *)
Proof.
  intros A l1 l2 l3 H12 H23. revert l1 H12.
  induction H23; cbn; intros.
    inv H12. constructor.
    inv H12; constructor; apply IHSubseq; assumption.
    inv H12; constructor; apply IHSubseq; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_cons_l_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq (x :: l1) l2 ->
      exists l21 l22 : list A,
        l2 = l21 ++ x :: l22 /\ Subseq l1 l22.
(* begin hide *)
Proof.
  intros A x l1 l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inv H.
    inv H.
      exists [], t2. cbn. split; [reflexivity | assumption].
      destruct (IHt2 _ H2) as (l21 & l22 & IH1 & IH2); subst.
        exists (h2 :: l21), l22. cbn. split; [reflexivity | assumption].
Qed.
(* end hide *)

Lemma Subseq_wasym :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq l2 l1 -> l1 = l2.
(* begin hide *)
Proof.
  induction 1; intro.
    inv H. reflexivity.
    f_equal. apply IHSubseq. apply Subseq_cons_inv in H0. assumption.
    apply Subseq_cons_l_app in H0.
      destruct H0 as (l21 & l22 & H1 & H2). subst.
      apply Subseq_length in H.
      apply Subseq_length in H2.
      rewrite length_app in H. cbn in H. lia.
Qed.
(* end hide *)

Lemma Subseq_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq l1 (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_snoc' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn; repeat constructor. assumption.
    constructor. assumption.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_app_l :
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq l1 (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Subseq_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq l1 (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_app_l' :
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq (l3 ++ l1) (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Subseq_app_r' :
  forall (A : Type) (l1 l2 l3 : list A),
    Subseq l1 l2 -> Subseq (l1 ++ l3) (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply Subseq_app_l, Subseq_refl.
    1-2: constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_app_not_comm :
  exists (A : Type) (l1 l2 l3 : list A),
    Subseq l1 (l2 ++ l3) /\ ~ Subseq l1 (l3 ++ l2).
(* begin hide *)
Proof.
  exists bool, [true; false], [true], [false]. cbn. split.
    repeat constructor.
    intro. inv H. inv H2.
      inv H0.
      inv H1.
Qed.
(* end hide *)

Lemma Subseq_map : 
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Subseq l1 l2 -> Subseq (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    apply Subseq_app_l'. assumption.
    apply Subseq_app_l. assumption.
Qed.
(* end hide *)

Lemma Subseq_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Subseq (replicate n x) (replicate m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert m. induction n as [| n']; cbn; intros.
      apply le_0_n.
      destruct m as [| m']; cbn in H.
        inv H.
        apply le_n_S, IHn'. apply Subseq_cons_inv with x. assumption.
    induction 1.
      apply Subseq_refl.
      cbn. constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Subseq (iterate f n x) (iterate f m x) <-> n <= m.
(* begin hide *)
Proof.
  split.
    revert f m x. induction n as [| n']; cbn; intros.
      apply le_0_n.
      destruct m as [| m']; cbn in H.
        inv H.
        apply le_n_S, (IHn' f _ (f x)).
          apply Subseq_cons_inv with x. assumption.
    revert f m x. induction n as [| n']; cbn; intros.
      constructor.
      destruct m as [| m']; cbn.
        inv H.
        constructor. apply IHn', le_S_n. assumption.
Qed.
(* end hide *)

Lemma Subseq_tail :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall l1' l2' : list A,
      tail l1 = Some l1' -> tail l2 = Some l2' -> Subseq l1' l2'.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    inv H0; inv H1. assumption.
    inv H1. destruct l1; inv H0. apply Subseq_cons_inv_l in H. assumption.
Qed.
(* end hide *)

Lemma Subseq_uncons :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (h1 h2 : A) (t1 t2 : list A),
      uncons l1 = Some (h1, t1) -> uncons l2 = Some (h2, t2) ->
        h1 = h2 \/ Subseq l1 t2.
(* begin hide *)
Proof.
  intros. inv H; cbn in *.
    inv H0.
    inv H0; inv H1. left. reflexivity.
    inv H1. right. assumption.
Qed.
(* end hide *)

Lemma Subseq_init :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall l1' l2' : list A,
      init l1 = Some l1' -> init l2 = Some l2' -> Subseq l1' l2'.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    destruct (init l1) eqn: Heq1, (init l2) eqn: Heq2.
      inv H0; inv H1. constructor. apply IHSubseq; reflexivity.
      inv H0; inv H1. apply init_None in Heq2. subst. inv H.
        cbn in Heq1. inv Heq1.
      inv H0; inv H1. constructor.
      inv H0; inv H1. constructor.
    destruct (init l2) eqn: Heq2.
      inv H1. constructor. apply IHSubseq; trivial.
      inv H1. apply init_None in Heq2. subst. inv H. cbn in H0. inv H0.
Qed.
(* end hide *)

Lemma Subseq_unsnoc :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (h1 h2 : A) (t1 t2 : list A),
      unsnoc l1 = Some (h1, t1) -> unsnoc l2 = Some (h2, t2) ->
        h1 = h2 \/ Subseq l1 t2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    destruct (unsnoc l1) eqn: Heq1, (unsnoc l2) eqn: Heq2.
      destruct p, p0. inv H0; inv H1.
        destruct (IHSubseq _ _ _ _ eq_refl eq_refl).
          left. assumption.
          right. constructor. assumption.
      apply unsnoc_None in Heq2. subst. inv H. cbn in Heq1. inv Heq1.
      destruct p. inv H0; inv H1. apply unsnoc_None in Heq1; subst.
        right. constructor. apply Subseq_nil.
      inv H0; inv H1. left. reflexivity.
    destruct (unsnoc l2) eqn: Heq.
      destruct p. inv H1. destruct (IHSubseq _ _ _ _ H0 eq_refl).
        left. assumption.
        right. constructor. assumption.
      apply unsnoc_None in Heq. subst. inv H. right. apply Subseq_nil.
Qed.
(* end hide *)

Lemma Subseq_nth :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    Subseq l1 l2 -> nth n l1 = Some x ->
      exists m : nat, nth m l2 = Some x /\ n <= m.
(* begin hide *)
Proof.
  intros A l1 l2 n x H. revert n x.
  induction H; cbn; intros.
    inv H.
    destruct n as [| n']; cbn in H0.
      inv H0. exists 0. cbn. split; [reflexivity | apply le_0_n].
      destruct (IHSubseq _ _ H0) as (m & IH1 & IH2).
        exists (S m). cbn. split.
          assumption.
          apply le_n_S. assumption.
    destruct (IHSubseq _ _ H0) as (m & IH1 & IH2).
      exists (S m). cbn. split.
        assumption.
        apply le_S. assumption.
Qed.
(* end hide *)

Lemma Subseq_insert :
  forall (A : Type) (l1 l2 : list A) (n : nat) (x : A),
    Subseq l1 l2 -> Subseq l1 (insert l2 n x).
(* begin hide *)
Proof.
  intros A l1 l2 n x H. revert n x.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n'].
      do 2 constructor. assumption.
      constructor. apply IHSubseq.
    destruct n as [| n']; repeat constructor; trivial.
Qed.
(* end hide *)

Lemma Subseq_replace :
  forall (A : Type) (l1 l1' l2 : list A) (n : nat) (x : A),
    Subseq l1 l2 -> replace l1 n x = Some l1' ->
      exists (m : nat) (l2' : list A),
        replace l2 m x = Some l2' /\ Subseq l1' l2'.
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma Subseq_remove' :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    Subseq l1 l2 -> Subseq (remove' n l1) l2.
(* begin hide *)
Proof.
  intros A l1 l2 n H. revert n.
  induction H; cbn; intros.
    constructor.
    destruct n as [| n']; cbn.
      constructor. assumption.
      rewrite remove'_S_cons. constructor. apply IHSubseq.
    constructor. apply IHSubseq.
Qed.
(* end hide *)

Lemma Subseq_take :
  forall (A : Type) (l : list A) (n : nat),
    Subseq (take n l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply Subseq_refl.
    destruct n as [| n']; constructor. apply IHt.
Qed.
(* end hide *)

Lemma Subseq_drop :
  forall (A : Type) (l : list A) (n : nat),
    Subseq (drop n l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply Subseq_refl.
    destruct n as [| n']; constructor.
      apply Subseq_refl.
      apply IHt.
Qed.
(* end hide *)

Lemma Subseq_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Subseq la1 la2 /\ Subseq lb1 lb2 /\
      ~ Subseq (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists bool, bool, [true], [true; false], [false], [true; false].
  firstorder.
    do 2 constructor.
    do 3 constructor.
    cbn. intro. inv H. inv H2. inv H1.
Qed.
(* end hide *)

Lemma Subseq_all :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> bool_le (all p l2) (all p l1).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (all p l); constructor.
    destruct (p x); cbn; [assumption | constructor].
    destruct (p x); cbn.
      assumption.
      destruct (all p l1); constructor.
Qed.
(* end hide *)

Lemma Subseq_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> bool_le (any p l1) (any p l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct (any p l); constructor.
    destruct (p x); cbn; [constructor | assumption].
    destruct (p x); cbn.
      destruct (any p l1); constructor.
      assumption.
Qed.
(* end hide *)

Lemma Subseq_all' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> all p l2 = true -> all p l1 = true.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x); cbn in *.
      apply IHSubseq. assumption.
      congruence.
    destruct (p x); cbn in *.
      apply IHSubseq. assumption.
      congruence.
Qed.
(* end hide *)

Lemma Subseq_any' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> any p l2 = false -> any p l1 = false.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct (p x); cbn in *.
      congruence.
      apply IHSubseq. assumption.
    destruct (p x); cbn in *.
      congruence.
      apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_findIndex :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A) (n m : nat),
    Subseq l1 l2 /\ findIndex p l1 = Some n /\
    findIndex p l2 = Some m /\ m < n.
(* begin hide *)
Proof.
  exists bool, id, [false; true], [true; false; true; false], 1, 0.
  cbn. firstorder. repeat constructor.
Qed.
(* end hide *)

Lemma Subseq_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> count p l1 <= count p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    apply le_0_n.
    destruct (p x); try apply le_n_S; assumption.
    destruct (p x); try apply le_S; assumption.
Qed.
(* end hide *)

Lemma Subseq_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
    destruct (p x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_filter' :
  forall (A : Type) (p : A -> bool) (l : list A),
    Subseq (filter p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Subseq (takeWhile p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_takeWhile' :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Subseq (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists bool, id, [true], [false; true]. cbn. split.
    repeat constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Subseq_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Subseq (dropWhile p l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h); constructor.
      assumption.
      apply Subseq_refl.
Qed.
(* end hide *)

Lemma Subseq_dropWhile' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (p x); try constructor; assumption.
    destruct (p x); try constructor.
      assumption.
      apply Subseq_trans with (dropWhile p l2).
        assumption.
        apply Subseq_dropWhile.
Qed.
(* end hide *)

Lemma Subseq_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); try constructor; assumption.
    destruct (f x); try constructor; assumption.
Qed.
(* end hide *)

Lemma Subseq_map_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (map Some (pmap f l1)) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); cbn; constructor; assumption.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Subseq l1 l2 -> Subseq (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (intersperse x l1) eqn: Heq1, (intersperse x l2) eqn: Heq2.
      do 2 constructor.
      do 2 constructor.
      inv IHSubseq.
      do 2 constructor. assumption.
    destruct (intersperse x l2).
      inv IHSubseq. constructor.
      do 2 constructor. assumption.
Qed.
(* end hide *)

(* begin hide *)

(* TODO: intercalate, Subseq_spec i inne dla Subseq *)

Fixpoint intercalate {A : Type} (l : list A) (ll : list (list A)) : list A :=
match l, ll with
    | [], _ => join ll
    | _, [] => l
    | h :: t, l :: ls => h :: l ++ intercalate t ls
end.

Lemma Subseq_spec :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 ->
      exists ll : list (list A),
        l2 = intercalate l1 ll.
Proof.
  induction 1; cbn.
    exists (map (fun x => [x]) l). admit.
    destruct IHSubseq as (ll & IH). subst.
      exists ([] :: ll). cbn. reflexivity.
    destruct IHSubseq as (ll & IH). subst. destruct ll as [| hl tl].
      destruct l1; cbn in *.
        exists [[x]]. cbn. reflexivity.
        exists [[x]]. cbn. destruct l1; cbn.
Abort.

(*
bind

unzip
zipWith
unzipWith

find i findLast
removeFirst i removeLast
findIndices
*)
(* end hide *)

Lemma Subseq_elem :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 ->
      forall x : A, elem x l1 -> elem x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    inv H0; [left | right]. apply IHSubseq. assumption.
    right. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_In :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 ->
      forall x : A, In x l1 -> In x l2.
(* begin hide *)
Proof.
  induction 1; firstorder.
Qed.
(* end hide *)

Lemma Subseq_NoDup :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> NoDup l2 -> NoDup l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    inv H0. constructor.
      intro. apply H3. apply Subseq_elem with l1; assumption.
      apply IHSubseq. assumption.
    inv H0. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_Dup :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> Dup l1 -> Dup l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    inv H0.
      left. apply Subseq_elem with l1; assumption.
      right. apply IHSubseq. assumption.
    right. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_Rep :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (x : A) (n : nat),
      Rep x n l1 -> Rep x n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. constructor.
    inv H0; constructor; apply IHSubseq; assumption.
    constructor. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_Exists :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Subseq l1 l2 -> Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H.
    rewrite Exists_cons in *. firstorder.
    right. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_Forall :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Subseq l1 l2 -> Forall P l2 -> Forall P l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    inv H0. constructor; try apply IHSubseq; assumption.
    inv H0. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    inv H. constructor.
    inv H0; constructor; try apply IHSubseq; assumption.
    constructor. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Subseq_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtMost P n l2 -> AtMost P n l1.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    constructor.
    inv H0.
      constructor; try apply IHSubseq; assumption.
      apply AM_skip. apply IHSubseq. assumption.
    inv H0.
      apply IHSubseq. assumption.
      apply AtMost_S. apply IHSubseq. assumption.
Qed.
(* end hide *)

Lemma Sublist_Subseq :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Subseq l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor. apply Subseq_refl.
    constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_Sublist :
  exists (A : Type) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Sublist l1 l2.
(* begin hide *)
Proof.
  exists unit, [], []. split.
    constructor.
    inversion 1.
Qed.
(* end hide *)

Lemma Prefix_Subseq :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> Subseq l1 l2.
(* begin hide *)
Proof.
  induction 1; constructor. assumption.
Qed.
(* end hide *)

Lemma Subseq_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true], [false; true]. split.
    do 3 constructor.
    intro. inv H.
Qed.
(* end hide *)

(** ** Zawieranie *)

(** Zdefiniuj (niekoniecznie induktywnie) relację [Incl]. Zdanie
    [Incl l1 l2] zachodzi, gdy lista [l2] zawiera wszystkie te
    elementy, które zawiera lista [l1], ale nie musi koniecznie
    zawierać tyle samo sztuk każdego elementu.

    Przykłady: *)

(** [Incl [1; 1; 2; 2; 3; 3] [3; 4; 5; 1; 9; 0; 2]] zachodzi. *)

(** [Incl [1; 1; 2; 2; 3; 3] [2; 3; 4; 5]] nie zachodzi. *)

(* begin hide *)
Definition Incl {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 -> elem x l2.
(* end hide *)

Lemma Incl_nil :
  forall (A : Type) (l : list A), Incl [] l.
(* begin hide *)
Proof.
  unfold Incl; intros. inversion H.
Qed.
(* end hide *)

Lemma Incl_nil_inv :
  forall (A : Type) (l : list A),
    Incl l [] -> l = [].
(* begin hide *)
Proof.
  unfold Incl; intros. destruct l as [| h t].
    reflexivity.
    specialize (H h ltac:(left)). inversion H.
Qed.
(* end hide *)

Lemma Incl_cons :
  forall (A : Type) (h : A) (t1 t2 : list A),
    Incl t1 t2 -> Incl (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  unfold Incl; intros.
  inversion H0; subst; clear H0.
    left.
    right. apply H, H3.
Qed.
(* end hide *)

Lemma Incl_cons' :
  forall (A : Type) (h : A) (t : list A),
    Incl t (h :: t).
(* begin hide *)
Proof.
  inversion 1; subst.
    right. left.
    do 2 right. assumption.
Qed.
(* end hide *)

Lemma Incl_cons'' :
  forall (A : Type) (h : A) (t l : list A),
    Incl l t -> Incl l (h :: t).
(* begin hide *)
Proof.
  unfold Incl; intros. right. apply H, H0.
Qed.
(* end hide *)

Lemma Incl_cons_conv :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Incl (x :: l1) (x :: l2) /\ ~ Incl l1 l2.
(* begin hide *)
Proof.
  exists unit, tt, [tt], []. unfold Incl. split; intros.
    inv H.
      constructor.
      assumption.
    intro. specialize (H tt ltac:(left)). inv H.
Qed.
(* end hide *)

Lemma Incl_refl :
  forall (A : Type) (l : list A), Incl l l.
(* begin hide *)
Proof.
  unfold Incl. trivial.
Qed.
(* end hide *)

Lemma Incl_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Incl l1 l2 -> Incl l2 l3 -> Incl l1 l3.
(* begin hide *)
Proof.
  unfold Incl; intros. apply H0, H, H1.
Qed.
(* end hide *)

Lemma Incl_length :
  forall (A : Type) (l1 l2 : list A),
    ~ Dup l1 -> Incl l1 l2 -> length l1 <= length l2.
(* begin hide *)
(* TODO: Incl_length *)
Proof.
  unfold Incl. induction l1 as [| h1 t1]; cbn; intros.
    apply le_0_n.
    destruct l2 as [| h2 t2].
      specialize (H0 h1 ltac:(left)). inv H0.
      cbn. apply le_n_S, IHt1.
        intro. apply H. right. assumption.
        intros. specialize (H0 x ltac:(right; assumption)). inv H0.
Abort.
(* end hide *)

Lemma Incl_snoc :
  forall (A : Type) (x : A) (l : list A),
    Incl l (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply Incl_nil.
    apply Incl_cons. assumption.
Qed.
(* end hide *)

Lemma Incl_singl_snoc :
  forall (A : Type) (x : A) (l : list A),
    Incl [x] (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply Incl_refl.
    apply Incl_cons''. assumption.
Qed.
(* end hide *)

Lemma Incl_snoc_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Incl l1 l2 -> Incl (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    apply Incl_singl_snoc.
    unfold Incl in *. intros x' H'. inversion H'; subst.
      rewrite elem_snoc. left. apply H. left.
      apply IHt.
        intros. apply H. right. assumption.
        assumption.
Qed.
(* end hide *)

Lemma Incl_app_rl :
  forall (A : Type) (l l1 l2 : list A),
    Incl l l2 -> Incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_app_r, H, H0.
Qed.
(* end hide *)

Lemma Incl_app_rr :
  forall (A : Type) (l l1 l2 : list A),
    Incl l l1 -> Incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_app_l, H, H0.
Qed.
(* end hide *)

Lemma Incl_app_l :
  forall (A : Type) (l1 l2 l3 : list A),
    Incl (l1 ++ l2) l3 <-> Incl l1 l3 /\ Incl l2 l3.
(* begin hide *)
Proof.
  unfold Incl; repeat split; intros.
    apply H. rewrite elem_app. left. assumption.
    apply H. rewrite elem_app. right. assumption.
    rewrite elem_app in H0. destruct H, H0.
      apply H. assumption.
      apply H1. assumption.
Qed.
(* end hide *)

Lemma Incl_app_sym :
  forall (A : Type) (l1 l2 l : list A),
    Incl (l1 ++ l2) l -> Incl (l2 ++ l1) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply H. rewrite elem_app in *.
  destruct H0; [right | left]; assumption.
Qed.
(* end hide *)

Lemma Incl_rev :
  forall (A : Type) (l : list A), Incl (rev l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. rewrite <- elem_rev. assumption.
Qed.
(* end hide *)

Lemma Incl_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Incl l1 l2 -> Incl (map f l1) (map f l2).
(* begin hide *)
Proof.
  unfold Incl; intros. rewrite elem_map_conv in *.
  destruct H0 as [x' [H1 H2]]. exists x'. split.
    assumption.
    apply H, H2.
Qed.
(* end hide *)

Lemma Incl_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Incl l1 l2 -> Incl (join l1) (join l2).
(* begin hide *)
Proof.
  unfold Incl; intros.
  apply elem_join in H0. destruct H0 as (l & H1 & H2).
  apply elem_join. exists l. split.
    assumption.
    apply H. assumption.
Qed.
(* end hide *)

Lemma Incl_elem_join :
  forall (A : Type) (ll : list (list A)) (l : list A),
    elem l ll -> Incl l (join ll).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_join. exists l. split; assumption.
Qed.
(* end hide *)

Lemma Incl_replicate :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    elem x l -> Incl (replicate n x) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_replicate in H0.
  destruct H0. subst. assumption.
Qed.
(* end hide *)

Lemma Incl_replicate' :
  forall (A : Type) (n m : nat) (x : A),
    n <> 0 -> Incl (replicate m x) (replicate n x).
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_replicate in H0.
  destruct H0. subst. apply elem_replicate. split; trivial.
Qed.
(* end hide *)

Lemma Incl_nth :
  forall (A : Type) (l1 l2 : list A),
    Incl l1 l2 <->
    forall (n1 : nat) (x : A), nth n1 l1 = Some x ->
      exists n2 : nat, nth n2 l2 = Some x.
(* begin hide *)
Proof.
  unfold Incl; split; intros.
    rewrite <- iff_elem_nth. apply H. rewrite iff_elem_nth.
      exists n1. assumption.
    rewrite iff_elem_nth in *. destruct H0 as (n & H0).
      apply H with n. assumption.
Qed.
(* end hide *)

Lemma Incl_remove :
  forall (A : Type) (l : list A) (n : nat),
    match remove n l with
        | None => True
        | Some (_, l') => Incl l' l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      apply Incl_cons'.
      specialize (IHt n'). destruct (remove n' t).
        destruct p. apply Incl_cons, IHt.
        trivial.
Qed.
(* end hide *)

Lemma Incl_take :
  forall (A : Type) (l : list A) (n : nat),
    Incl (take n l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_take in H. assumption.
Qed.
(* end hide *)

Lemma Incl_drop :
  forall (A : Type) (l : list A) (n : nat),
    Incl (drop n l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_drop in H. assumption.
Qed.
(* end hide *)

Lemma Incl_insert :
  forall (A : Type) (l1 l2 : list A) (n m : nat) (x : A),
    Incl l1 l2 -> Incl (insert l1 n x) (insert l2 m x).
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite elem_insert in *. firstorder.
Qed.
(* end hide *)

Lemma Incl_replace :
  forall (A : Type) (l1 l1' l2 : list A) (n : nat) (x : A),
    Incl l1 l2 -> replace l1 n x = Some l1' ->
      exists (m : nat) (l2' : list A),
        replace l2 m x = Some l2' /\ Incl l1' l2'.
(* begin hide *)
Proof.
  unfold Incl. induction l1 as [| h1 t1]; cbn; intros.
    inv H0.
    destruct n as [| n']; cbn in *.
      inv H0. exists 0.
      Focus 2. destruct (replace t1 n' x) eqn: Heq.
        inv H0.
Abort.
(* end hide *)

Lemma Incl_splitAt :
  forall (A : Type) (l : list A) (n : nat),
    match splitAt n l with
        | None => True
        | Some (l1, _, l2) => Incl l1 l /\ Incl l2 l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      split.
        apply Incl_nil.
        apply Incl_cons'.
      specialize (IHt n'). destruct (splitAt n' t).
        destruct p, p. destruct IHt as (IH1 & IH2). split.
          apply Incl_cons, IH1.
          apply Incl_cons'', IH2.
        assumption.
Qed.
(* end hide *)

Lemma Incl_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl (filter p l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_filter in H. destruct H. assumption.
Qed.
(* end hide *)

Lemma Incl_filter_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl l (filter p l) <-> filter p l = l.
(* begin hide *)
Proof.
  unfold Incl. split.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      case_eq (p h); intros; rewrite H0 in *.
        rewrite IHt.
          reflexivity.
          intros. specialize (H x ltac:(right; assumption)).
            inversion H; subst; clear H.
              rewrite elem_filter. split; assumption.
              assumption.
        specialize (H h ltac:(left)). rewrite elem_filter in H.
          destruct H. congruence.
    intros -> *. trivial.
Qed.
(* end hide *)

Lemma Incl_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl (takeWhile p l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_takeWhile in H. destruct H. assumption.
Qed.
(* end hide *)

(* begin hide *)
Lemma Incl_takeWhile_conv_aux :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl l (takeWhile p l) -> all p l = true.
Proof.
  unfold Incl. intros.
  assert (forall x : A, elem x l -> p x = true).
    intros. destruct (elem_takeWhile _ _ _ _ (H _ H0)). assumption.
    clear H. induction l as [| h t]; cbn.
      reflexivity.
      destruct (p h) eqn: Hph; cbn.
        apply IHt. intros. apply H0. right. assumption.
        rewrite <- Hph, H0.
          reflexivity.
          left.
Qed.
(* end hide *)

Lemma Incl_takeWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl l (takeWhile p l) <-> takeWhile p l = l.
(* begin hide *)
Proof.
  split; intros.
    apply all_takeWhile'. apply Incl_takeWhile_conv_aux, H.
    rewrite H. apply Incl_refl.
Qed.
(* end hide *)

Lemma Incl_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    Incl (dropWhile p l) l.
(* begin hide *)
Proof.
  unfold Incl; intros. apply elem_dropWhile in H. assumption.
Qed.
(* end hide *)

Lemma Incl_span :
  forall (A : Type) (p : A -> bool) (x : A) (l b e : list A),
    span p l = Some (b, x, e) ->
      Incl b l /\ elem x l /\ Incl e l.
(* begin hide *)
Proof.
  intros. apply span_spec in H. subst. repeat split.
    apply Incl_app_rr, Incl_refl.
    rewrite elem_app. right. left.
    apply Incl_app_rl. constructor. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Incl vs span i Sublist, palindromy *)
(* end hide *)

Lemma Incl_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    Incl (map Some (pmap f l)) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply Incl_refl.
    destruct (f h); cbn; rewrite ?IHt.
      apply Incl_cons. assumption.
      apply Incl_cons''. assumption.
Qed.
(* end hide *)

Lemma Incl_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Incl l1 (intersperse x l2) -> Incl l1 (x :: l2).
(* begin hide *)
Proof.
  unfold Incl; intros.
  specialize (H _ H0). rewrite elem_intersperse in H.
  decompose [and or] H; subst; [right | left]; assumption.
Qed.
(* end hide *)

Lemma Incl_intersperse_conv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    2 <= length l2 -> Incl l1 (x :: l2) -> Incl l1 (intersperse x l2).
(* begin hide *)
Proof.
  unfold Incl; intros.
  specialize (H0 _ H1). rewrite elem_intersperse.
  inversion H0; subst; firstorder.
Qed.
(* end hide *)

Lemma Incl_In :
  forall (A : Type) (l1 l2 : list A),
    Incl l1 l2 -> forall x : A, In x l1 -> In x l2.
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite In_elem in *. apply H, H0.
Qed.
(* end hide *)

Lemma Incl_NoDup :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ NoDup l2 /\ ~ NoDup l1.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. repeat split.
    unfold Incl. intros. destruct x. constructor.
    repeat constructor. inversion 1.
    intro. inv H. apply H2. constructor.
Qed.
(* end hide *)

Lemma Incl_Dup :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ Dup l1 /\ ~ Dup l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. repeat split.
    unfold Incl. intros. destruct x. constructor.
    repeat constructor.
    intro. inv H; inv H1.
Qed.
(* end hide *)

Lemma Incl_Rep :
  exists (A : Type) (x : A) (n : nat) (l1 l2 : list A),
    Incl l1 l2 /\ Rep x n l1 /\ ~ Rep x n l2.
(* begin hide *)
Proof.
  exists unit, tt, 2, [tt; tt], [tt]. repeat split.
    unfold Incl. destruct x. constructor.
    repeat constructor.
    intro. inv H; inv H2.
Qed.
(* end hide *)

Lemma Incl_Exists :
  forall (A : Type) (l1 l2 : list A),
    Incl l1 l2 -> forall P : A -> Prop,
      Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite Exists_spec in *.
  destruct H0 as (x & H1 & H2). exists x. split.
    apply H. assumption.
    assumption.
Qed.
(* end hide *)

Lemma Incl_Forall :
  forall (A : Type) (l1 l2 : list A),
    Incl l1 l2 -> forall P : A -> Prop,
      Forall P l2 -> Forall P l1.
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite Forall_spec in *. intros. apply H0, H, H1.
Qed.
(* end hide *)

Lemma Incl_AtLeast :
  exists (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Incl l1 l2 /\ AtLeast P n l1 /\ ~ AtLeast P n l2.
(* begin hide *)
Proof.
  exists unit, (fun _ => True), 2, [tt; tt], [tt]. repeat split.
    unfold Incl. destruct x. constructor.
    repeat constructor.
    intro. inv H.
      inv H4.
      inv H2.
Qed.
(* end hide *)

Lemma Incl_Exactly :
  exists (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Incl l1 l2 /\ Exactly P n l1 /\ ~ Exactly P n l2.
(* begin hide *)
Proof.
  exists unit, (fun _ => True), 2, [tt; tt], [tt]. repeat split.
    unfold Incl. destruct x. constructor.
    repeat constructor.
    intro. inv H.
      inv H4.
      contradiction.
Qed.
(* end hide *)

Lemma Incl_AtMost :
  exists (A : Type) (P : A -> Prop) (n : nat) (l1 l2 : list A),
    Incl l1 l2 /\ AtMost P n l2 /\ ~ AtMost P n l1.
(* begin hide *)
Proof.
  exists unit, (fun _ => True), 1, [tt; tt], [tt]. repeat split.
    unfold Incl. destruct x. constructor.
    apply AM_skip. constructor.
    intro. inv H.
      contradiction.
      inv H2. contradiction.
Qed.
(* end hide *)

Lemma Sublist_Incl :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  intros. unfold Incl. apply Sublist_elem. assumption.
Qed.
(* end hide *)

Lemma Incl_Sublist :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ ~ Sublist l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. split.
    unfold Incl. destruct x. constructor.
    intro. inv H. inv H2.
Qed.
(* end hide *)

Lemma Prefix_Incl :
  forall (A : Type) (l1 l2 : list A),
    Prefix l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  intros. unfold Incl. apply Prefix_elem. assumption.
Qed.
(* end hide *)

Lemma Incl_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [true; true], [true]. split.
    unfold Incl. intros. inv H.
      constructor.
      assumption.
    intro. inv H. inv H1.
Qed.
(* end hide *)

Lemma Subseq_Incl :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  intros. unfold Incl. apply Subseq_elem. assumption.
Qed.
(* end hide *)

Lemma Incl_Subseq :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ ~ Subseq l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. split.
    unfold Incl. destruct x. constructor.
    intro. inv H.
      inv H1.
      inv H2.
Qed.
(* end hide *)

(** ** Listy jako zbiory *)

(** Zdefiniuj relację [SetEquiv]. Zdanie [SetEquiv l1 l2] zachodzi,
    gdy listy [l1] i [l2] mają te same elementy, choć niekoniecznie
    w tej samej kolejności czy ilości.

    Przykłady: *)

(** [SetEquiv [1; 1; 2] [2; 2; 1]] zachodzi. *)

(** [SetEquiv [1; 2; 3; 3] [2; 2; 3; 3; 4]] nie zachodzi. *)

(* begin hide *)
Definition SetEquiv {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 <-> elem x l2.
(* end hide *)

Lemma SetEquiv_Incl :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <-> Incl l1 l2 /\ Incl l2 l1.
(* begin hide *)
Proof.
  unfold SetEquiv, Incl. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_refl :
  forall (A : Type) (l : list A), SetEquiv l l.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_sym :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <-> SetEquiv l2 l1.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    SetEquiv l1 l2 -> SetEquiv l2 l3 -> SetEquiv l1 l3.
(* begin hide *)
Proof.
  unfold SetEquiv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_nil_l :
  forall (A : Type) (l : list A),
    SetEquiv [] l -> l = [].
(* begin hide *)
Proof.
  unfold SetEquiv. destruct l as [| h t]; intros.
    reflexivity.
    assert (elem h []).
      rewrite H. left.
      inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_nil_r :
  forall (A : Type) (l : list A),
    SetEquiv l [] -> l = [].
(* begin hide *)
Proof.
  intros. apply SetEquiv_nil_l. rewrite SetEquiv_sym. assumption.
Qed.
(* end hide *)

Lemma SetEquiv_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_cons'. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_cons_conv :
  exists (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv (x :: l1) (x :: l2) /\ ~ SetEquiv l1 l2.
(* begin hide *)
Proof.
  exists unit, tt, [tt], []. unfold SetEquiv. firstorder.
    destruct x. constructor.
    destruct x. constructor.
    intro. assert (elem tt []).
      rewrite <- H. constructor.
      inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_cons' :
  exists (A : Type) (x : A) (l : list A),
    ~ SetEquiv l (x :: l).
(* begin hide *)
Proof.
  exists unit, tt, []. unfold SetEquiv. intro.
  assert (elem tt []).
    rewrite H. constructor.
    inv H0.
Qed.
(* end hide *)

Lemma SetEquiv_snoc_cons :
  forall (A : Type) (x : A) (l : list A),
    SetEquiv (snoc x l) (x :: l).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite elem_snoc, elem_cons'. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_snoc. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_comm :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv (l1 ++ l2) (l2 ++ l1).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_l :
  forall (A : Type) (l1 l2 l : list A),
    SetEquiv l1 l2 -> SetEquiv (l ++ l1) (l ++ l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_app_r :
  forall (A : Type) (l1 l2 l : list A),
    SetEquiv l1 l2 -> SetEquiv (l1 ++ l) (l2 ++ l).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_app. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_rev :
  forall (A : Type) (l : list A), SetEquiv (rev l) l.
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite elem_rev. reflexivity.
Qed.
(* end hide *)

Lemma SetEquiv_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (map f l1) (map f l2).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. rewrite ?elem_map_conv. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_join :
  forall (A : Type) (l1 l2 : list (list A)),
    SetEquiv l1 l2 -> SetEquiv (join l1) (join l2).
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl in *. destruct H. split.
    apply Incl_join. assumption.
    apply Incl_join. assumption.
Qed.
(* end hide *)

Lemma SetEquiv_replicate :
  forall (A : Type) (n : nat) (x : A),
    SetEquiv (replicate n x) (if isZero n then [] else [x]).
(* begin hide *)
Proof.
  unfold SetEquiv. intros. destruct n; cbn.
    reflexivity.
    rewrite elem_cons', elem_replicate. split; intros.
      decompose [and or] H; subst; constructor.
      inv H.
        left. reflexivity.
        inv H2.
Qed.
(* end hide *)

Lemma SetEquiv_replicate' :
  forall (A : Type) (n m : nat) (x : A),
    m <> 0 -> n <> 0 -> SetEquiv (replicate m x) (replicate n x).
(* begin hide *)
Proof.
  intros. eapply SetEquiv_trans.
    apply SetEquiv_replicate.
    apply SetEquiv_sym. eapply SetEquiv_trans.
      apply SetEquiv_replicate.
      destruct n, m; try contradiction; cbn. apply SetEquiv_refl.
Qed.
(* end hide *)

Lemma SetEquiv_nth :
  forall (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 <->
    (forall n : nat, exists m : nat, nth n l1 = nth m l2) /\
    (forall n : nat, exists m : nat, nth m l1 = nth n l2).
(* begin hide *)
(* TODO : SetEquiv_nth *)
Proof.
  split; intros.
    rewrite SetEquiv_Incl in H. destruct H.
      rewrite Incl_nth in H. rewrite Incl_nth in H0.
      split; intros.
        destruct (nth n l1) eqn: Heq1.
          destruct (H _ _ Heq1) as (m & H'). exists m. symmetry. assumption.
          exists (length l2). rewrite nth_length_ge; reflexivity.
        destruct (nth n l2) eqn: Heq1.
          destruct (H0 _ _ Heq1) as (m & H'). exists m. assumption.
          exists (length l1). rewrite nth_length_ge; reflexivity.
    destruct H. rewrite SetEquiv_Incl. split.
      rewrite Incl_nth. intros. destruct (H n1) as (n2 & Hn2).
        exists n2. rewrite <- Hn2. assumption.
      rewrite Incl_nth. intros. destruct (H0 n1) as (n2 & Hn2).
        exists n2. rewrite Hn2. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Lemma SetEquiv_remove :
  exists (A : Type) (l1 l1' l2 l2' : list A) (n1 n2 : nat),
    remove match remove n l with
        | None => True
        | Some (_, l') => SetEquiv l' l
    end.
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      apply SetEquiv_cons'.
      specialize (IHt n'). destruct (remove n' t).
        destruct p. apply SetEquiv_cons, IHt.
        trivial.
Qed.*)
(* end hide *)

Lemma SetEquiv_take :
  forall (A : Type) (l : list A) (n : nat),
    SetEquiv (take n l) l <-> Incl (drop n l) (take n l).
(* begin hide *)
Proof.
  split; intros.
    rewrite SetEquiv_Incl in H. destruct H. apply Incl_trans with l.
      apply Incl_drop.
      apply H0.
    rewrite SetEquiv_Incl. split.
      apply Incl_take.
      rewrite <- (app_take_drop _ l n) at 1. rewrite Incl_app_l. split.
        apply Incl_refl.
        assumption.
Qed.
(* end hide *)

Lemma SetEquiv_drop :
  forall (A : Type) (n : nat) (l : list A),
    SetEquiv (drop n l) l <-> Incl (take n l) (drop n l).
(* begin hide *)
Proof.
  split; intros.
    rewrite SetEquiv_Incl in H. destruct H. apply Incl_trans with l.
      apply Incl_take.
      apply H0.
    rewrite SetEquiv_Incl. split.
      apply Incl_drop.
      rewrite <- (app_take_drop _ l n) at 1. rewrite Incl_app_l. split.
        assumption.
        apply Incl_refl.
Qed.
(* end hide *)

Lemma SetEquiv_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (filter p l) l <-> all p l = true.
(* begin hide *)
Proof.
  split.
    intros. rewrite SetEquiv_Incl in H. destruct H.
      rewrite Incl_filter_conv in H0. rewrite <- H0, all_filter.
        reflexivity.
    induction l as [| h t]; cbn; intros.
      apply SetEquiv_refl.
      destruct (p h) eqn: Hph; cbn in *.
        apply SetEquiv_cons, IHt, H.
        congruence.
Qed.
(* end hide *)

Lemma SetEquiv_filter' :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    SetEquiv l1 l2 -> SetEquiv (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  unfold SetEquiv; split; intros.
    rewrite elem_filter in *. firstorder.
    rewrite elem_filter in *. firstorder.
Qed.
(* end hide *)

Lemma SetEquiv_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (takeWhile p l) l <-> all p l = true.
(* begin hide *)
Proof.
  split.
    intros. rewrite SetEquiv_Incl in H. destruct H.
      rewrite Incl_takeWhile_conv in H0. rewrite <- H0, all_takeWhile.
        reflexivity.
    induction l as [| h t]; cbn; intros.
      apply SetEquiv_refl.
      destruct (p h) eqn: Hph; cbn in *.
        apply SetEquiv_cons, IHt, H.
        congruence.
Qed.
(* end hide *)

Lemma SetEquiv_dropWhile :
  exists (A : Type) (p : A -> bool) (l : list A),
    SetEquiv (dropWhile p l) l /\ any p l = true.
(* begin hide *)
Proof.
  exists bool, id, [true; false; true; false]. cbn. split.
    unfold SetEquiv. firstorder; destruct x; repeat constructor.
    reflexivity.
Qed.
(* end hide *)

Lemma SetEquiv_pmap :
  exists (A B : Type) (f : A -> option B) (l : list A),
    ~ SetEquiv (map Some (pmap f l)) (map f l).
(* begin hide *)
Proof.
  exists bool, unit, (fun b : bool => if b then Some tt else None),
         [true; false].
    cbn. unfold SetEquiv. intro. assert (elem None [Some tt]).
      rewrite H. repeat constructor.
      inv H0. inv H3.
Qed.
(* end hide *)

Lemma SetEquiv_intersperse :
  forall (A : Type) (x : A) (l : list A),
    2 <= length l -> SetEquiv (intersperse x l) (x :: l).
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl. split.
    apply Incl_intersperse. apply Incl_refl.
    apply Incl_intersperse_conv.
      assumption.
      apply Incl_refl.
Qed.
(* end hide *)

Lemma SetEquiv_intersperse_conv :
  forall (A : Type) (x : A) (l : list A),
    SetEquiv (intersperse x l) (x :: l) ->
      elem x l \/ 2 <= length l.
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl in H. destruct H.
  destruct l as [| h1 [| h2 t]]; cbn in *.
    specialize (H0 _ ltac:(left)). inv H0.
    specialize (H0 _ ltac:(left)). inv H0.
      left. constructor.
      inv H3.
    right. apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)

(* begin hide *)
Ltac se := repeat (cbn in *;
match goal with
    | H : SetEquiv [] _ |- _ => apply SetEquiv_nil_l in H; inv H
    | H : SetEquiv _ [] |- _ => apply SetEquiv_nil_r in H; inv H
    | H : ?P |- ?P => assumption
    | |- SetEquiv [] [] => apply SetEquiv_refl
end).
(* end hide *)

Lemma SetEquiv_singl :
  forall (A : Type) (l : list A) (x : A),
    SetEquiv [x] l -> forall y : A, elem y l -> y = x.
(* begin hide *)
Proof.
  intros. apply SetEquiv_Incl in H. destruct H. clear H.
  unfold Incl in H1. specialize (H1 _ H0). inv H1.
    reflexivity.
    inv H3.
Qed.
(* end hide *)

Lemma SetEquiv_pres_intersperse :
  exists (A : Type) (x : A) (l1 l2 : list A),
    SetEquiv l1 l2 /\ ~ SetEquiv (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  exists bool, false, [true], [true; true]. cbn. split.
    unfold SetEquiv. firstorder.
      inv H.
        repeat constructor.
        inv H2.
      repeat (inv H; [repeat constructor | rename H2 into H]). inv H.
    intro. assert (elem false [true]).
      unfold SetEquiv in H. rewrite H. repeat constructor.
      inv H0. inv H3.
Qed.
(* end hide *)

(** ** Listy jako multizbiory *)

Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.

(** Zdefiniuj induktywną relację [Permutation]. Zdanie
    [Permutation l1 l2] zachodzi, gdy listy [l1] i [l2] mają te same
    elementy w tej samej ilości sztuk, ale niekoniecznie w tej samej
    kolejności.

    Przykłady: *)

(** [Permutation [1; 5; 1; 4; 3] [4; 1; 1; 5; 3]] zachodzi. *)

(** [Permutation [0; 0; 2; 6; 7] [7; 0; 2; 0; 6; 0]] nie zachodzi. *)

(** Uwaga: to zadanie jest dużo trudniejsze od reszty zadań dotyczących
    relacji między listami. Jeżeli masz problem z rozwiązaniem, spróbuj
    poszukać gotowca w bibliotece standardowej Coqa. *)

(* begin hide *)
Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    | perm_nil : Permutation [] []
    | perm_skip : forall (x : A) (l l' : list A),
        Permutation l l' -> Permutation (x :: l) (x :: l')
    | perm_swap : forall (x y : A) (l : list A),
        Permutation (y :: x :: l) (x :: y :: l)
    | perm_trans : forall l l' l'' : list A,
        Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Hint Constructors Permutation.
(* end hide *)

Lemma Permutation_refl :
  forall (A : Type) (l : list A),
    Permutation l l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; auto.
Defined.
(* end hide *)

Lemma Permutation_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3.
(* begin hide *)
Proof.
  intros. eapply perm_trans; eauto.
Qed.
(* end hide *)

Lemma Permutation_sym :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation l2 l1.
(* begin hide *)
Proof.
  induction 1; auto. eapply Permutation_trans; eauto.
Qed.
(* end hide *)

Instance Permutation_Equivalence:
  forall A : Type, RelationClasses.Equivalence (Permutation (A := A)).
(* begin hide *)
Proof.
  split; red.
    apply Permutation_refl.
    apply Permutation_sym.
    apply Permutation_trans.
Defined.
(* end hide *)

Lemma Permutation_isEmpty :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> isEmpty l1 = isEmpty l2.
(* begin hide *)
Proof.
  induction 1; cbn; congruence.
Qed.
(* end hide *)

Lemma Permutation_nil_l :
  forall (A : Type) (l : list A),
    Permutation [] l -> l = [].
(* begin hide *)
Proof.
  intros. apply Permutation_isEmpty in H. cbn in H.
  destruct l; inv H. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_nil_r :
  forall (A : Type) (l : list A),
    Permutation l [] -> l = [].
(* begin hide *)
Proof.
  intros. apply Permutation_isEmpty in H. cbn in H.
  destruct l; inv H. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_nil_cons_l :
  forall (A : Type) (l : list A) (x : A),
    ~ Permutation [] (x :: l).
(* begin hide *)
Proof.
  intros; intro. apply Permutation_nil_l in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_nil_cons_r :
  forall (A : Type) (l : list A) (x : A),
    ~ Permutation (x :: l) [].
(* begin hide *)
Proof.
  intros; intro. apply Permutation_nil_r in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_nil_app_cons_l :
  forall (A : Type) (l l' : list A) (x : A),
    ~ Permutation [] (l ++ x :: l').
(* begin hide *)
Proof.
  intros; intro. apply (Permutation_isEmpty) in H.
  rewrite isEmpty_app in H. destruct l; inv H.
Qed.
(* end hide *)

Instance Permutation_cons :
  forall A : Type,
    Proper (eq ==> @Permutation A ==> @Permutation A) (@cons A).
(* begin hide *)
Proof.
  unfold Proper, respectful. intros; subst; auto.
Defined.
(* end hide *)

Lemma Permutation_ind' :
  forall (A : Type) (P : list A -> list A -> Prop),
    P [] [] ->
    (forall x l l', Permutation l l' -> P l l' -> P (x :: l) (x :: l')) ->
    (forall x y l l', Permutation l l' -> P l l' ->
      P (y :: x :: l) (x :: y :: l')) ->
    (forall l l' l'', Permutation l l' -> P l l' -> Permutation l' l'' ->
      P l' l'' -> P l l'') ->
    forall l l', Permutation l l' -> P l l'.
(* begin hide *)
Proof.
  intros A P Hnil Hskip Hswap Htrans.
  induction 1.
    apply Hnil.
    apply Hskip; assumption.
    apply Hswap.
      reflexivity.
      induction l.
        assumption.
        apply Hskip.
          reflexivity.
          assumption.
    apply Htrans with l'; assumption.
Qed.
(* end hide *)

Inductive Elem {A : Type} (x : A) : list A -> list A -> Prop :=
    | es_here :
        forall l : list A, Elem x l (x :: l)
    | es_there :
        forall (y : A) (l1 l2 : list A),
          Elem x l1 l2 -> Elem x (y :: l1) (y :: l2).

Lemma Elem_spec :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Elem x l1 l2 -> exists l21 l22 : list A,
      l2 = l21 ++ x :: l22 /\ l1 = l21 ++ l22.
(* begin hide *)
Proof.
  induction 1.
    exists [], l. split; reflexivity.
    destruct IHElem as (l21 & l22 & IH1 & IH2); subst.
      exists (y :: l21), l22. split; reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Elem :
  forall (A : Type) (x : A) (l l' : list A),
    Elem x l l' -> Permutation l' (x :: l).
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    apply perm_trans with (y :: x :: l1); constructor; assumption.
Qed.
(* end hide *)

Lemma Elem_Permutation :
  forall (A : Type) (x : A) (l1 l1' : list A),
    Elem x l1 l1' -> forall l2' : list A,
      Permutation l1' l2' -> exists l2 : list A, Elem x l2 l2'.
(* begin hide *)
Proof.
  intros. revert x l1 H. induction H0; intros.
    inv H.
    inv H.
      eexists. constructor.
      destruct (IHPermutation _ _ H3) as (l2 & IH).
        exists (x :: l2). constructor. assumption.
    inv H.
      eexists. do 2 constructor.
      inv H2.
        eexists. constructor.
        eexists. do 2 constructor. eassumption.
    destruct (IHPermutation1 _ _ H) as (l2 & IH1).
      destruct (IHPermutation2 _ _ IH1) as (l2' & IH2).
        exists l2'. assumption.
Qed.
(* end hide *)

Lemma Permutation_Elems :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> forall (x : A) (l1' l2' : list A),
      Elem x l1' l1 -> Elem x l2' l2 ->
        Permutation l1' l2'.
(* begin hide *)
Proof.
  induction 1; intros.
    inv H0.
    inv H0; inv H1.
      assumption.
      rewrite H. eapply Permutation_Elem. assumption.
      rewrite <- H. symmetry. apply Permutation_Elem. assumption.
      constructor. eapply IHPermutation; eassumption.
    repeat match goal with
        | H : Elem _ _ (_ :: _) |- _ => inv H
        | |- Permutation (?x :: _) (?x :: _) => constructor
        | H : ?G |- ?G => assumption
        | |- Permutation ?x ?x => reflexivity
    end.
      symmetry. apply Permutation_Elem. assumption.
      rewrite perm_swap. constructor. symmetry.
        apply Permutation_Elem. assumption.
      apply Permutation_Elem. assumption.
      rewrite perm_swap. constructor. apply Permutation_Elem. assumption.
      admit. (* Za mało indukcji *)
    destruct (@Elem_Permutation _ _ _ _ H1 _ H) as (l3 & IH).
      specialize (IHPermutation1 _ _ _ H1 IH).
      specialize (IHPermutation2 _ _ _ IH H2).
      rewrite IHPermutation1, <- IHPermutation2. reflexivity.
Restart.
  intro.
  apply (@Permutation_ind' _
    (fun l1 l2 => forall x l1' l2',
      Elem x l1' l1 -> Elem x l2' l2 -> Permutation l1' l2'));
  intros.
    inv H0.
    inv H1; inv H2.
      assumption.
      rewrite H. eapply Permutation_Elem. assumption.
      rewrite <- H. symmetry. apply Permutation_Elem. assumption.
      constructor. eapply H0; eassumption.
    repeat match goal with
        | H : Elem _ _ (_ :: _) |- _ => inv H
        | |- Permutation (?x :: _) (?x :: _) => constructor
        | H : ?G |- ?G => assumption
    end.
      rewrite <- H. symmetry. apply Permutation_Elem. assumption.
      rewrite perm_swap, <- H. constructor. symmetry.
        apply Permutation_Elem. assumption.
      rewrite H. apply Permutation_Elem. assumption.
      rewrite perm_swap, H. constructor. apply Permutation_Elem. assumption.
      rewrite perm_swap. do 2 constructor. eapply H0; eassumption.
    destruct (@Elem_Permutation _ _ _ _ H3 _ H) as (l3 & IH).
      specialize (H0 _ _ _ H3 IH). specialize (H2 _ _ _ IH H4).
      rewrite H0, <- H2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_cons_inv :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Permutation (x :: l1) (x :: l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros.
  apply Permutation_Elems with (x := x) (l1 := x :: l1) (l2 := x :: l2).
    assumption.
    1-2: constructor.
Qed.
(* end hide *)

(* begin hide *)
(*
Lemma Permutation_cons_aux :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation (x :: l1) l2 ->
      exists l21 l22 : list A, l2 = l21 ++ x :: l22.
Proof.
  intros. pose (@Permutation_In _ _ _ H x).
  assert (In x (x :: l1)).
    left. reflexivity.
    rewrite i in H0. apply In_spec. assumption.
Qed.
*)
(* end hide *)

Lemma Permutation_length :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> length l1 = length l2.
(* begin hide *)
Proof.
  induction 1; cbn; congruence.
Qed.
(* end hide *)

Lemma Permutation_length' :
  forall A : Type,
    Proper (@Permutation A ==> eq) (@length A).
(* begin hide *)
Proof.
  unfold Proper, respectful; intros.
  apply Permutation_length. assumption.
Qed.
(* end hide *)

Lemma Permutation_length_1:
  forall (A : Type) (l1 l2 : list A),
    length l1 = 1 -> Permutation l1 l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction 2; cbn in *.
    reflexivity.
    destruct l, l'; cbn in *.
      reflexivity.
      apply Permutation_nil_l in H0. inv H0.
      inv H.
      inv H.
    inv H.
    rewrite IHPermutation1, IHPermutation2.
      reflexivity.
      apply Permutation_length in H0_. rewrite <- H0_. assumption.
      assumption.
Qed.
(* end hide *)

Lemma Permutation_singl :
  forall (A : Type) (a b : A),
    Permutation [a] [b] -> a = b.
(* begin hide *)
Proof.
  intros. apply Permutation_length_1 in H.
    inv H. reflexivity.
    cbn. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_length_1_inv:
  forall (A : Type) (x : A) (l : list A),
    Permutation [x] l -> l = [x].
(* begin hide *)
Proof.
  destruct l as [| y [| z t]]; intros.
    symmetry in H. apply Permutation_nil_l in H. inversion H.
    apply Permutation_singl in H. rewrite H. reflexivity.
    apply Permutation_length in H. cbn in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction 1; cbn; repeat constructor.
    assumption.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_cons_snoc :
  forall (A : Type) (l : list A) (x : A),
    Permutation (x :: l) (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite perm_swap. constructor. apply IHt.
Qed.
(* end hide *)

Lemma Permutation_cons_snoc' :
  forall (A : Type) (l : list A) (x : A),
    Permutation (x :: l) (l ++ [x]).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite perm_swap. constructor. apply IHt.
Qed.
(* end hide *)

Lemma Permutation_app_l :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation l1 l2 -> Permutation (l3 ++ l1) (l3 ++ l2).
(* begin hide *)
Proof.
  induction l3 as [| h t]; cbn; intros; auto.
Qed.
(* end hide *)

Lemma Permutation_app_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation l1 l2 -> Permutation (l1 ++ l3) (l2 ++ l3).
(* begin hide *)
Proof.
  induction 1; cbn; intros; auto.
    apply Permutation_refl.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_app :
  forall (A : Type) (l1 l1' l2 l2' : list A),
    Permutation l1 l1' -> Permutation l2 l2' ->
      Permutation (l1 ++ l2) (l1' ++ l2').
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    assumption.
    constructor. apply IHPermutation. assumption.
    rewrite perm_swap. do 2 constructor. apply Permutation_app_l, H.
    rewrite (IHPermutation1 H1). apply Permutation_app_r. assumption.
Qed.
(* end hide *)

Instance Permutation_app':
  forall A : Type,
    Proper (@Permutation A ==> @Permutation A ==> @Permutation A) (@app A).
(* begin hide *)
Proof.
  unfold Proper, respectful.
  intros. apply Permutation_app; assumption.
Defined.
(* end hide *)

Lemma Permutation_add_inside :
  forall (A : Type) (x : A) (l1 l2 l1' l2' : list A),
    Permutation l1 l1' -> Permutation l2 l2' ->
      Permutation (l1 ++ x :: l2) (l1' ++ x :: l2').
(* begin hide *)
Proof.
  intros. rewrite H, H0. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_cons_middle :
  forall (A : Type) (l1 l2 l3 : list A) (x : A),
    Permutation l1 (l2 ++ l3) -> Permutation (x :: l1) (l2 ++ x :: l3).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    apply Permutation_nil_l in H. destruct l2, l3; inv H.
      cbn. reflexivity.
    rewrite H. rewrite app_cons_r, <- app_cons_l. apply Permutation_app.
      apply Permutation_cons_snoc'.
      reflexivity.
Qed.
(* end hide *)

Lemma Permutation_middle :
  forall (A : Type) (l1 l2 : list A) (x : A),
    Permutation (l1 ++ x :: l2) (x :: (l1 ++ l2)).
(* begin hide *)
Proof.
  intros. symmetry. apply Permutation_cons_middle. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_app_comm :
  forall (A : Type) (l1 l2 : list A),
    Permutation (l1 ++ l2) (l2 ++ l1).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    rewrite Permutation_cons_middle.
      reflexivity.
      apply IHt1.
Qed.
(* end hide *)

(* begin hide *)
(*
Lemma Permutation_app_inv :
  forall (A : Type) (l1 l2 l3 l4 : list A) (x : A),
    Permutation (l1 ++ x :: l2) (l3 ++ x :: l4) ->
    Permutation (l1 ++ l2) (l3 ++ l4).
Proof.
  intros. rewrite ?Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
*)
(* end hide *)

Lemma Permutation_app_inv_l :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation (l1 ++ l2) (l1 ++ l3) -> Permutation l2 l3.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    assumption.
    apply IHt. apply Permutation_cons_inv in H. assumption.
Qed.
(* end hide *)

Lemma Permutation_app_inv_r :
  forall (A : Type) (l1 l2 l3 : list A),
    Permutation (l1 ++ l3) (l2 ++ l3) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros.
  rewrite (Permutation_app_comm _ l1 l3) in H.
  rewrite (Permutation_app_comm _ l2 l3) in H.
  apply Permutation_app_inv_l in H. assumption.
Qed.
(* end hide *)

Lemma Permutation_rev :
  forall (A : Type) (l : list A),
    Permutation (rev l) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    symmetry. rewrite <- Permutation_cons_snoc'. constructor.
      symmetry. assumption.
Qed.
(* end hide *)

Instance Permutation_rev' :
  forall A : Type,
    Proper (@Permutation A ==> @Permutation A) (@rev A).
(* begin hide *)
Proof.
  unfold Proper, respectful; intros.
  rewrite ?Permutation_rev. assumption.
Qed.
(* end hide *)

Lemma Permutation_map:
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; try constructor.
    assumption.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_map':
  forall (A B : Type) (f : A -> B),
    Morphisms.Proper
      (Morphisms.respectful (Permutation (A:=A)) (Permutation (A:=B)))
      (map f).
(* begin hide *)
Proof.
  unfold Proper, respectful. induction 1; cbn; try constructor.
    assumption.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Permutation l1 l2 -> Permutation (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    apply Permutation_app_l, IHPermutation.
    rewrite Permutation_app_comm, <- app_assoc.
      apply Permutation_app_l, Permutation_app_comm.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_join_rev :
  exists (A : Type) (l1 l2 : list (list A)),
    Permutation (join l1) (join l2) /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [[]]. cbn. split.
    reflexivity.
    intro. apply Permutation_length in H. inversion H.
Qed.
(* end hide *)

Lemma Permutation_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Permutation (replicate n x) (replicate m x) <-> n = m.
(* begin hide *)
Proof.
  split.
    revert m x. induction n as [| n']; cbn; intros.
      apply Permutation_length in H. destruct m; inversion H. reflexivity.
      destruct m as [| m'].
        apply Permutation_length in H; cbn in H. inv H.
        apply f_equal, (IHn' m' x), Permutation_cons_inv with x, H.
    intros ->. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(*
Lemma Permutation_cons_middle_inv :
  forall (A : Type) (l l1 l2 : list A) (x : A),
    Permutation (x :: l) (l1 ++ x :: l2) -> Permutation l (l1 ++ l2).
Proof.
  intros. rewrite Permutation_middle in H.
  apply Permutation_cons_inv in H. assumption.
Qed.
*)
(* end hide *)

Lemma Permutation_In :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> (forall x : A, In x l1 <-> In x l2).
(* begin hide *)
Proof.
  induction 1; cbn; firstorder.
Qed.
(* end hide *)

Lemma Permutation_in :
  forall (A : Type) (l l' : list A) (x : A),
    Permutation l l' -> In x l -> In x l'.
(* begin hide *)
Proof.
  induction 1; intros; cbn; auto.
    inversion H0; auto.
    inversion H; auto. inversion H0; auto.
Qed.
(* end hide *)

Lemma Permutation_in' :
  forall A : Type,
    Proper (eq ==> @Permutation A ==> iff) (@In A).
(* begin hide*)
Proof.
  unfold Proper, respectful; intros.
  subst. split; intro H; eapply Permutation_in; eauto.
  symmetry. assumption.
Qed.
(* end hide *)

Lemma Permutation_replicate' :
  forall (A : Type) (n : nat) (x y : A),
    Permutation (replicate n x) (replicate n y) <-> n = 0 \/ x = y.
(* begin hide *)
Proof.
  split.
    revert x y. induction n as [| n']; cbn; intros.
      left. reflexivity.
      right. assert (H' := @Permutation_in A _ _ x H ltac:(left; reflexivity)).
        inv H'. reflexivity.
        apply In_replicate in H0. destruct H0. symmetry. assumption.
    destruct 1; rewrite H; reflexivity.
Qed.
(* end hide *)

Lemma Permutation_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Permutation (iterate f n x) (iterate f m x) <-> n = m.
(* begin hide *)
Proof.
  split.
    revert f m x. induction n as [| n']; cbn; intros.
      apply Permutation_length in H. destruct m; inversion H. reflexivity.
      destruct m as [| m'].
        apply Permutation_length in H; cbn in H. inv H.
        apply f_equal, (IHn' f m' (f x)), Permutation_cons_inv with x, H.
    intros ->. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_iterate' :
  forall (A : Type) (f : A -> A) (n : nat) (x y : A),
    Permutation (iterate f n x) (iterate f n y) ->
      n = 0 \/ exists k : nat, k < n /\ iter f k y = x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    left. reflexivity.
    right. pose (H' := @Permutation_in A _ _ x H ltac:(left; reflexivity)).
      inv H'. exists 0. split.
        apply le_n_S, le_0_n.
        cbn. reflexivity.
      apply In_iterate in H0. destruct H0 as (k & H1 & H2).
        exists (S k). split.
          apply lt_n_S. assumption.
          cbn. symmetry. assumption.
Qed.
(* end hide *)

Lemma Permutation_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    Permutation (insert l n x) (x :: l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite perm_swap. constructor. apply IHt.
Qed.
(* end hide *)

Lemma Permutation_take :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\
      exists n : nat, ~ Permutation (take n l1) (take n l2).
(* begin hide *)
Proof.
  exists bool, [true; false], [false; true]. split.
    constructor.
    exists 1. cbn. intro. apply Permutation_length_1 in H.
      congruence.
      reflexivity.
Qed.
(* end hide *)

Lemma Permutation_drop :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\
      exists n : nat, ~ Permutation (drop n l1) (drop n l2).
(* begin hide *)
Proof.
  exists bool, [true; false], [false; true]. split.
    constructor.
    exists 1. cbn. intro. apply Permutation_length_1 in H.
      congruence.
      reflexivity.
Qed.
(* end hide *)

Lemma Permutation_cycle :
  forall (A : Type) (n : nat) (l : list A),
    Permutation (cycle n l) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn'. rewrite Permutation_cons_snoc. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_filter_cycle :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    Permutation (filter p (cycle n l)) (filter p l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn', filter_snoc; cbn. destruct (p h).
        rewrite Permutation_cons_snoc. reflexivity.
        reflexivity.
Qed.
(* end hide *)

Lemma Permutation_length_2_inv:
  forall (A : Type) (x y : A) (l : list A),
    Permutation [x; y] l -> l = [x; y] \/ l = [y; x].
(* begin hide *)
Proof.
  intros.
  assert (H' := @Permutation_length _ _ _ H).
  destruct l as [| a [| b [| c t]]]; inv  H'.
  assert (H' := @Permutation_In _ _ _ H).
  assert (In x [a; b]).
    rewrite <- H'. left. reflexivity.
    cbn in H0. decompose [or] H0; clear H0; subst.
      left. apply Permutation_cons_inv, Permutation_singl in H. subst.
        reflexivity.
      rewrite (@Permutation_app_comm _ [a] [b]) in H. cbn in H.
        apply Permutation_cons_inv, Permutation_singl in H. subst.
          right. reflexivity.
      contradiction.
Qed.
(* end hide *)

Lemma Permutation_length_2:
  forall (A : Type) (x1 x2 y1 y2 : A),
    Permutation [x1; x2] [y1; y2] ->
      x1 = y1 /\ x2 = y2 \/ x1 = y2 /\ x2 = y1.
(* begin hide *)
Proof.
  intros. apply Permutation_length_2_inv in H.
  destruct H; inversion H; subst.
    left. split; reflexivity.
    right. split; reflexivity.
Qed.
(* end hide *)

Lemma Permutation_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Permutation la1 la2 /\ Permutation lb1 lb2 /\
      ~ Permutation (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists bool, bool,
    [true; false], [false; true], [false; true; false], [false; false; true].
  repeat split.
    apply perm_swap.
    do 2 constructor.
    cbn. intro. apply Permutation_length_2 in H. firstorder congruence.
Qed.
(* end hide *)

Lemma Permutation_zipWith :
  exists
    (A B C : Type) (f : A -> B -> C)
    (la1 la2 : list A) (lb1 lb2 : list B),
      Permutation la1 la2 /\
      Permutation lb1 lb2 /\
      ~ Permutation (zipWith f la1 lb1) (zipWith f la2 lb2).
(* begin hide *)
Proof.
  destruct (Permutation_zip)
    as (A & B & la1 & la2 & lb1 & lb2 & H1 & H2 & H3).
  exists A, B, (prod A B), pair, la1, la2, lb1, lb2. repeat split.
    1-2: assumption.
    rewrite ?zipWith_pair. assumption.
Qed.
(* end hide *)

Lemma Permutation_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> any p l1 = any p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. destruct (p x); reflexivity.
    destruct (p x), (p y); reflexivity.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_all :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> all p l1 = all p l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. destruct (p x); reflexivity.
    destruct (p x), (p y); reflexivity.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1; cbn; try destruct (p x); try destruct (p y); congruence.
Qed.
(* end hide *)

Lemma Permutation_count_replicate_filter :
  forall (A : Type) (p : A -> bool) (l b e : list A) (x : A),
    span p l = Some (b, x, e) ->
      Permutation l (replicate (count p l) x ++ b ++ e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph.
      cbn. inv H. constructor. apply IHt.
Abort.
(* end hide *)

Lemma Permutation_count_conv :
  forall (A : Type) (l1 l2 : list A),
    (forall p : A -> bool, count p l1 = count p l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma Permutation_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    destruct (p x); rewrite IHPermutation; reflexivity.
    destruct (p x), (p y); try constructor; reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_takeWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 /\
    ~ Permutation (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists bool, id, [true; false], [false; true]. cbn. split.
    constructor.
    intro. apply Permutation_nil_r in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_dropWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 /\
    ~ Permutation (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  exists bool, id, [true; false], [false; true]. cbn. split.
    constructor.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_span :
  forall (A : Type) (p : A -> bool) (l b e : list A) (x : A),
    span p l = Some (b, x, e) -> Permutation l (b ++ x :: e).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. cbn. reflexivity.
      destruct (span p t) eqn: Heq.
        destruct p0, p0. inv H. cbn. constructor. apply IHt. reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma Permutation_removeFirst :
  forall (A : Type) (p : A -> bool) (l l' : list A) (x : A),
    removeFirst p l = Some (x, l') -> Permutation l (x :: l').
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h).
      inv H. reflexivity.
      destruct (removeFirst p t) eqn: Heq.
        destruct p0. inv H. rewrite perm_swap. constructor. apply IHt.
          reflexivity.
        inv H.
Qed.
(* end hide *)

Lemma Permutation_intersperse_replicate :
  forall (A : Type) (x : A) (l : list A),
    Permutation (intersperse x l) (replicate (length l - 1) x ++ l).
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn.
    reflexivity.
    destruct t; cbn in *.
      reflexivity.
      destruct (intersperse x t); inv e0.
    rewrite <- minus_n_O. destruct t; cbn in *.
      inv e0.
      destruct (intersperse x t); inv e0; rewrite <- minus_n_O in *.
        rewrite perm_swap. constructor.
          rewrite <- Permutation_cons_middle.
            constructor. apply IHl0.
            reflexivity.
        rewrite perm_swap. constructor. rewrite Permutation_app_comm in *.
          cbn in *. do 2 constructor. apply Permutation_cons_inv in IHl0.
            assumption.
Qed.
(* end hide *)

Lemma Permutation_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Permutation (intersperse x l1) (intersperse x l2) <->
    Permutation l1 l2.
(* begin hide *)
Proof.
  split; intros.
    assert (length l1 = length l2).
      destruct (length l1 =? length l2) eqn: Heq.
        apply Nat.eqb_eq in Heq. assumption.
        rewrite Nat.eqb_neq in Heq. apply Permutation_length in H.
          rewrite ?length_intersperse in H. lia.
      rewrite ?Permutation_intersperse_replicate, H0 in H.
        apply Permutation_app_inv_l in H. assumption.
    assert (length l1 = length l2).
      apply Permutation_length. assumption.
      rewrite ?Permutation_intersperse_replicate, H0.
        apply Permutation_app_l. assumption.
Qed.
(* end hide *)

Lemma Permutation_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    destruct (f x); rewrite IHPermutation; reflexivity.
    destruct (f x), (f y); try constructor; reflexivity.
    rewrite IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_elem :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall x : A, elem x l1 <-> elem x l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?elem_cons', IHPermutation. reflexivity.
    rewrite ?elem_cons'. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_replicate'' :
  forall (A : Type) (n m : nat) (x y : A),
    Permutation (replicate n x) (replicate m y) <->
    n = m /\ (n <> 0 -> m <> 0 -> x = y).
(* begin hide *)
Proof.
  split.
    revert m x y. induction n as [| n']; cbn; intros.
      apply Permutation_nil_l in H. destruct m; inv H. split.
        reflexivity.
        contradiction.
      destruct m as [| m']; cbn in H.
        apply Permutation_nil_r in H. inv H.
        assert (x = y).
          assert (elem x (y :: replicate m' y)).
            rewrite <- Permutation_elem. 2: eassumption. left.
            rewrite elem_cons', elem_replicate in H0. firstorder.
          subst. apply Permutation_cons_inv in H.
            destruct (IHn' _ _ _ H). subst. split; reflexivity.
    destruct 1. subst. rewrite Permutation_replicate'. destruct m as [| m'].
      left. reflexivity.
      right. apply H0; inversion 1.
Qed.
(* end hide *)

Lemma NoDup_Permutation:
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 -> NoDup l2 ->
      (forall x : A, In x l1 <-> In x l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    inversion H0; subst.
      reflexivity.
      assert False.
        rewrite (H1 h). left. reflexivity.
        contradiction.
    destruct l2 as [| h2 t2]; cbn; intros.
      specialize (H1 h1). destruct H1. destruct H1. left. reflexivity.
      inversion H; inversion H0; subst; clear H H0.
        destruct (H1 h1). destruct H.
          left. reflexivity.
          subst. constructor. apply IHt1.
            1-2: assumption.
            split; intro.
              assert (In x (h2 :: t2)).
                rewrite <- H1. right. assumption.
                destruct H2.
                  subst. rewrite In_elem in *. contradiction.
                  assumption.
              assert (In x (h2 :: t1)).
                cbn. rewrite H1. right. assumption.
                destruct H2; subst.
                  rewrite In_elem in *. contradiction.
                  assumption.
          apply In_spec in H. destruct H as (l1 & l2 & HIn); subst.
            rewrite Permutation_middle. rewrite perm_swap. constructor.
            apply IHt1.
              assumption.
              constructor.
                intro. apply H8. apply elem_app_or in H.
                  apply elem_or_app. destruct H.
                    left. assumption.
                    do 2 right. assumption.
                rewrite NoDup_app_comm in H9. inversion H9.
                  rewrite NoDup_app_comm. assumption.
              split; intro.
                assert (In x (h2 :: l1 ++ h1 :: l2)).
                  rewrite <- H1. right. assumption.
                  inversion H2; subst.
                    left. reflexivity.
                    apply In_app_or in H3. destruct H3.
                      right. apply In_or_app. left. assumption.
                      inversion H3; subst.
                        rewrite In_elem in *. contradiction.
                        right. apply In_or_app. right. assumption.
                assert (In x (h2 :: l1 ++ h1 :: l2)).
                  cbn in H. destruct H.
                    subst. left. reflexivity.
                    apply In_app_or in H. destruct H.
                      right. apply In_or_app. left. assumption.
                      right. apply In_or_app. do 2 right. assumption.
                  specialize (H1 x). rewrite <- H1 in H2. destruct H2.
                    subst. destruct H.
                      subst. contradiction H8. apply elem_or_app.
                        right. left.
                      apply In_app_or in H. destruct H.
                        rewrite NoDup_app_comm in H9. inversion H9.
                          subst. contradiction H6. apply elem_or_app.
                            right. rewrite <- In_elem. assumption.
                        rewrite NoDup_app_comm in H9. inversion H9.
                          subst. contradiction H6. apply elem_or_app.
                            left. rewrite <- In_elem. assumption.
                    assumption.
Qed.
(* end hide *)

Lemma NoDup_Permutation_bis:
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> length l2 <= length l1 ->
      Incl l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros A l1 l2 H. revert l2.
  induction H; cbn; intros.
    destruct l2; inv H0. reflexivity.
    destruct l2 as [| h2 t2]; inv H1; unfold Incl in H3.
      specialize (H3 _ ltac:(left)). inv H3.
      assert (H' := H3 _ ltac:(left)). inv H'.
        constructor. apply IHNoDup.
          assumption.
          apply le_S_n. cbn in H2. assumption.
          unfold Incl. intros. assert (elem x (h2 :: t2)).
            apply H3. right. assumption.
            inv H4.
              contradiction.
              assumption.
        assert (exists l1 l2 : list A, t2 = l1 ++ h :: l2).
          apply elem_spec. assumption.
          destruct H1 as (l1 & l2 & Heq). subst.
            rewrite <- Permutation_cons_middle.
              rewrite perm_swap. constructor. apply (IHNoDup (h2 :: l1 ++ l2)).
                constructor.
                  intro. apply H6. rewrite elem_app, ?elem_cons' in *.
                    firstorder.
                rewrite NoDup_app_comm in H7. inv H7.
                  rewrite NoDup_app_comm. assumption.
                cbn in *. rewrite length_app in *. cbn in *. lia.
                unfold Incl. intros.
                  specialize (H3 x ltac:(right; assumption)).
                    repeat (rewrite ?elem_cons', ?elem_app in *).
                      decompose [and or] H3; clear H3.
                        subst. left. reflexivity.
                        right. left. assumption.
                        subst. contradiction.
                        do 2 right. assumption.
                reflexivity.
Qed.
(* end hide *)

Lemma Permutation_NoDup:
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> NoDup l1 -> NoDup l2.
(* begin hide *)
Proof.
  induction 1; intros.
    constructor.
    inv H0. constructor.
      rewrite <- In_elem in *. intro. apply H3. eapply Permutation_in.
        symmetry. eassumption.
        assumption.
      apply IHPermutation. assumption.
    inv H. inv H3. constructor.
      intro. inv H.
        apply H2. left.
        contradiction.
      constructor.
        intro. apply H2. right. assumption.
        assumption.
    apply IHPermutation2, IHPermutation1, H1.
Qed.
(* end hide *)

Lemma Permutation_NoDup':
  forall A : Type,
    Morphisms.Proper
      (Morphisms.respectful (Permutation (A:=A)) iff)
      (NoDup (A:=A)).
(* begin hide *)
Proof.
  unfold Proper, respectful. split; intro.
    eapply Permutation_NoDup; eauto.
    eapply Permutation_NoDup.
      symmetry. all: eassumption.
Qed.
(* end hide *)

Lemma Permutation_Dup :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Dup l1 <-> Dup l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    assert (H' := @Permutation_elem _ _ _ H).
      rewrite ?Dup_cons, ?IHPermutation, H'. reflexivity.
    rewrite ?Dup_cons, ?elem_cons'. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Rep :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall (x : A) (n : nat), Rep x n l1 <-> Rep x n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?Rep_cons, ?IHPermutation. reflexivity.
    rewrite ?Rep_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Exists :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall P : A -> Prop, Exists P l1 <-> Exists P l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?Exists_cons, IHPermutation. reflexivity.
    rewrite ?Exists_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Exists_conv :
  exists (A : Type) (l1 l2 : list A),
    (forall P : A -> Prop, Exists P l1 <-> Exists P l2) /\
    ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt], [tt; tt]. split.
    intro. rewrite ?Exists_cons. firstorder.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_Forall :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall P : A -> Prop, Forall P l1 <-> Forall P l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?Forall_cons, IHPermutation. reflexivity.
    rewrite ?Forall_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat), AtLeast P n l1 <-> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite ?AtLeast_cons, ?IHPermutation. reflexivity.
    rewrite ?AtLeast_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Exactly :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat), Exactly P n l1 <-> Exactly P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      rewrite !Exactly_0_cons, IHPermutation. reflexivity.
      rewrite !Exactly_S_cons, !IHPermutation. reflexivity.
    destruct n as [| [| n']].
      rewrite !Exactly_0_cons. firstorder.
      rewrite !Exactly_S_cons, !Exactly_0_cons. firstorder.
      rewrite !Exactly_S_cons. firstorder.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat), AtMost P n l1 <-> AtMost P n l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      rewrite ?AtMost_0, IHPermutation. reflexivity.
      rewrite ?AtMost_S_cons, ?IHPermutation. reflexivity.
    destruct n as [| [| n']]; cbn.
      rewrite ?AtMost_0. firstorder.
      rewrite !AtMost_S_cons, !AtMost_0. firstorder.
      rewrite !AtMost_S_cons. firstorder.
      rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_Sublist :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\ ~ Sublist l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    constructor.
    intro. inv H. inv H2. inv H1.
Qed.
(* end hide *)

Lemma Sublist_Permutation :
  exists (A : Type) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [tt]. split.
    constructor.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    constructor.
    intro. inv H.
Qed.
(* end hide *)

Lemma Prefix_Permutation :
  exists (A : Type) (l1 l2 : list A),
    Prefix l1 l2 /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [tt]. split.
    constructor.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_Subseq :
  exists (A : Type) (l1 l2 : list A),
    Permutation l1 l2 /\ ~ Subseq l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    constructor.
    intro. inv H. inv H2.
      inv H0.
      inv H1.
Qed.
(* end hide *)

Lemma Subseq_Permutation :
  exists (A : Type) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Permutation l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [tt]. split.
    constructor.
    intro. apply Permutation_length in H. inv H.
Qed.
(* end hide *)

Lemma Permutation_Incl :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  unfold Incl. intros. rewrite Permutation_elem.
    eassumption.
    symmetry. assumption.
Qed.
(* end hide *)

Lemma Permutation_SetEquiv :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl. split.
    apply Permutation_Incl. assumption.
    apply Permutation_Incl. symmetry. assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Permutation vs różne rzeczy

nth

remove

splitAt

unzip

unzipWith
head, tail i uncons
last, init i unsnoc


find i findLast
removeFirst i removeLast
findIndex

findIndices

Poza tym permutacje mają inny styl (można używać symmetry etc).
*)
(* end hide *)

(** ** Listy jako cykle *)

(** Zdefiniuj induktywną relację [Cycle]. Zdanie [Cycle l1 l2] zachodzi,
    gdy listy [l1] i [l2] reprezentują ten sam cykl. Intuicyjnie możesz
    sobie wyobrazić elementy [l1] ułożone po kolei wzdłuż okręgu tak, że
    ostatni element sąsiaduje z pierwszym. Jeżeli da się teraz przekręcić
    ten okrąg tak, żeby uzyskać listę [l2], to znaczy, że [Cycle l1 l2]
    zachodzi.

    Przykłady: *)

(** [Cycle [1; 2; 3; 4; 5] [4; 5; 1; 2; 3]] zachodzi. *)

(** [Cycle [1; 2; 3] [2; 1; 3]] nie zachodzi. *)

(* begin hide *)
Inductive Cycle {A : Type} : list A -> list A -> Prop :=
    | Cycle_refl : forall l : list A, Cycle l l
    | Cycle_cyc :
        forall (x : A) (l1 l2 : list A),
          Cycle l1 (snoc x l2) -> Cycle l1 (x :: l2).
(* end hide *)

Lemma lt_plus_S :
  forall n m : nat,
    n < m -> exists k : nat, m = S (n + k).
(* begin hide *)
Proof.
  intros n m. revert n.
  induction m as [| m']; cbn; intros.
    inv H.
    destruct n as [| n']; cbn.
      exists m'. reflexivity.
      destruct (IHm' _ (lt_S_n _ _ H)) as (k & IH). subst.
        exists k. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_spec :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 <->
    exists n : nat, n <= length l1 /\ l1 = drop n l2 ++ take n l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      exists 0. rewrite drop_0, take_0, app_nil_r. split.
        apply le_0_n.
        reflexivity.
      destruct IHCycle as (n & IH1 & IH2). subst.
        destruct (Nat.leb_spec0 n (length l2)).
          rewrite drop_snoc_le, take_snoc_le; try assumption.
            exists (S n). cbn. rewrite app_snoc_l. split.
              rewrite <- (@app_take_drop _ l2 n) in l.
                rewrite length_app in *. cbn. lia.
              reflexivity.
          assert (exists k : nat, n = S (length l2 + k)).
            apply lt_plus_S. lia.
            destruct H0 as (k & Hk). subst. rewrite drop_length'.
              rewrite take_length'.
                exists 1. cbn. rewrite drop_0, take_0. split.
                  rewrite length_snoc. lia.
                  apply snoc_app_singl.
                rewrite length_snoc. lia.
              rewrite length_snoc. lia.
    destruct 1 as (n & Hle & H); subst.
      revert l2 Hle. induction n as [| n']; intros.
        rewrite drop_0, take_0, app_nil_r. constructor.
        destruct l2 as [| h t]; cbn.
          constructor.
          destruct (Nat.leb_spec0 (length t) n').
            rewrite drop_length', take_length'.
              constructor.
              1-2: assumption.
            specialize (IHn' (snoc h t)). rewrite drop_snoc_le in IHn'.
              rewrite take_snoc_le in IHn'.
                constructor. rewrite app_snoc_l in IHn'. cbn in Hle.
                  apply IHn'. lia.
                lia.
              lia.
Qed.
(* end hide *)

Lemma Cycle_isEmpty :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> isEmpty l1 = isEmpty l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    cbn in *. rewrite isEmpty_snoc in *. assumption.
Qed.
(* end hide *)

Lemma Cycle_nil_l :
  forall (A : Type) (l : list A),
    Cycle [] l -> l = [].
(* begin hide *)
Proof.
  intros. apply Cycle_isEmpty in H. destruct l; inv H. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_nil_r :
  forall (A : Type) (l : list A),
    Cycle l [] -> l = [].
(* begin hide *)
Proof.
  intros. apply Cycle_isEmpty in H. destruct l; inv H. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_length :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> length l1 = length l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite length_snoc in IHCycle. assumption.
Qed.
(* end hide *)

Lemma Cycle_cons :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  exists nat, 0, [1; 2; 3], [3; 1; 2]. split.
    constructor. cbn. constructor.
    intro. apply Cycle_spec in H. destruct H as (n & H1 & H2).
      destruct n as [| [| [| [| n']]]]; cbn in H2; inv H2.
Qed.
(* end hide *)

Lemma Cycle_cons_inv :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Cycle  (x :: l1) (x :: l2) /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists nat, 3, [2; 3; 1], [1; 3; 2]. split.
    constructor. cbn. constructor. cbn. constructor.
    intro. apply Cycle_spec in H. destruct H as (n & H1 & H2).
      destruct n as [| [| [| n']]]; inv H2.
Qed.
(* end hide *)

Lemma Cycle_snoc :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  exists nat, 0, [1; 2; 3], [3; 1; 2]. split.
    constructor. cbn. constructor.
    intro. apply Cycle_spec in H. destruct H as (n & H1 & H2).
      destruct n as [| [| [| [| n']]]]; cbn in H2; inv H2.
Qed.
(* end hide *)

Lemma Cycle_sym :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle l2 l1.
(* begin hide *)
Proof.
  intros. rewrite Cycle_spec in *. destruct H as (n & H1 & H2). subst.
  destruct (Nat.leb_spec0 (length l2) n);
  eexists; rewrite drop_app, take_app, drop_drop, take_take, length_drop.
    instantiate (1 := 0). rewrite ?plus_0_r. cbn.
      rewrite Nat.min_0_r, ?take_0, drop_0, ?app_nil_r.
        rewrite drop_length', take_length'; try assumption. split.
          apply le_0_n.
          reflexivity.
    instantiate (1 := length l2 - n). rewrite <- le_plus_minus, drop_length.
      cbn. replace (length l2 - n - (length l2 - n)) with 0.
      rewrite drop_0, take_drop, <- le_plus_minus, take_length.
      rewrite Nat.min_0_r, take_0, app_nil_r, app_take_drop. split.
        2: reflexivity.
        all: lia.
Qed.
(* end hide *)

Lemma Cycle_snoc_cons :
  forall (A : Type) (x : A) (l : list A),
    Cycle  (snoc x l) (x :: l).
(* begin hide *)
Proof.
  repeat constructor.
Qed.
(* end hide *)

Lemma Cycle_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Cycle  (x :: l) (snoc x l).
(* begin hide *)
Proof.
  intros. apply Cycle_sym. apply Cycle_snoc_cons.
Qed.
(* end hide *)

Lemma Cycle_cons_snoc' :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Cycle l1 (x :: l2) -> Cycle l1 (snoc x l2).
(* begin hide *)
Proof.
  intros. inv H.
    apply Cycle_cons_snoc.
    assumption.
Qed.
(* end hide *)

Lemma Cycle_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Cycle l1 l2 -> Cycle l2 l3 -> Cycle l1 l3.
(* begin hide *)
Proof.
  intros until 1. revert l3.
  induction H; intros.
    assumption.
    apply IHCycle. apply Cycle_sym. apply Cycle_cons_snoc'.
      apply Cycle_sym. assumption.
Qed.
(* end hide *)

Lemma Cycle_app :
  forall (A : Type) (l1 l2 l3 : list A),
    Cycle l1 (l2 ++ l3) -> Cycle l1 (l3 ++ l2).
(* begin hide *)
Proof.
  intros A l1 l2 l3. revert l1 l2.
  induction l3 as [| h t]; cbn; intros.
    rewrite app_nil_r in *. assumption.
    specialize (IHt l1 (snoc h l2)). constructor. rewrite snoc_app.
      apply IHt. rewrite snoc_app_singl, <- app_assoc. cbn. assumption.
Qed.
(* end hide *)

Lemma Cycle_rev :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle (rev l1) (rev l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    rewrite <- snoc_app_singl. apply Cycle_cons_snoc'.
      rewrite rev_snoc in IHCycle. assumption.
Qed.
(* end hide *)

Lemma Cycle_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction 1; cbn; constructor.
    rewrite map_snoc in IHCycle. assumption.
Qed.
(* end hide *)

Lemma Cycle_join :
  forall (A : Type) (l1 l2 : list (list A)),
    Cycle l1 l2 -> Cycle (join l1) (join l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    rewrite join_snoc in IHCycle. apply Cycle_app. assumption. 
Qed.
(* end hide *)

Lemma Cycle_replicate :
  forall (A : Type) (n m : nat) (x : A),
    Cycle (replicate n x) (replicate m x) <-> n = m.
(* begin hide *)
Proof.
  split; intros.
    apply Cycle_length in H. rewrite ?length_replicate in H. assumption.
    subst. constructor.
Qed.
(* end hide *)

Lemma Cycle_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    Cycle (iterate f n x) (iterate f m x) <-> n = m.
(* begin hide *)
Proof.
  split; intro.
    apply Cycle_length in H. rewrite ?length_iterate in H. assumption.
    subst. constructor.
Qed.
(* end hide *)

Lemma Cycle_iterate' :
  forall (A : Type) (f : A -> A) (n m : nat) (x y : A),
    Cycle (iterate f n x) (iterate f m y) <-> n = m.
(* begin hide *)
Proof.
  split; intro.
    apply Cycle_length in H. rewrite ?length_iterate in H. assumption.
    subst. induction m as [| m']; cbn.
      constructor.
      constructor.
Abort.
(* end hide *)

(* begin hide *)
(* TODO: Cycle vs head, tail, etc. *)
(* end hide *)

Lemma Cycle_nth :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (n : nat) (x : A),
      nth n l1 = Some x -> exists m : nat, nth m l2 = Some x.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    exists n. assumption.
    destruct (IHCycle _ _ H0) as (m & IH).
      destruct (Nat.leb_spec0 (S m) (length l2)).
        rewrite nth_snoc_length_lt in IH.
          exists (S m). assumption.
          assumption.
        destruct (Nat.eqb_spec m (length l2)).
          exists 0. rewrite e, nth_snoc_length_eq in IH. assumption.
          rewrite nth_length_ge in IH.
            inv IH.
            rewrite length_snoc. lia.
Qed.
(* end hide *)

Lemma Cycle_cycle :
  forall (A : Type) (n : nat) (l : list A),
    Cycle (cycle n l) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    intro. apply Cycle_refl.
    destruct l as [| h t]; cbn.
      constructor.
      eapply Cycle_trans.
        apply IHn'.
        constructor. apply Cycle_refl.
Qed.
(* end hide *)

Lemma cycle_Cycle :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> exists n : nat, cycle n l1 = l2.
(* begin hide *)
Proof.
  induction 1.
    exists 0. cbn. reflexivity.
    destruct IHCycle as [n IH]. exists (n + length l2).
      apply (f_equal (cycle (length l2))) in IH.
      rewrite cycle_cycle in IH.
      rewrite IH, (plus_n_O (length l2)).
      rewrite snoc_app_singl, cycle_length_app. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_insert :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (n : nat) (x : A),
      exists m : nat, Cycle (insert l1 n x) (insert l2 m x) .
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    exists n. constructor.
    destruct (IHCycle n x0) as (m & IH). rewrite insert_snoc in IH.
      destruct (m <=? length l2) eqn: Hle.
        exists (S m). constructor. assumption.
        exists 1. rewrite insert_0. do 2 (constructor; cbn). assumption.
Qed.
(* end hide *)

Lemma Cycle_zip :
  exists (A B : Type) (la1 la2 : list A) (lb1 lb2 : list B),
    Cycle la1 la2 /\ Cycle lb1 lb2 /\ ~ Cycle (zip la1 lb1) (zip la2 lb2).
(* begin hide *)
Proof.
  exists
    bool, bool,
    [true; false], [false; true],
    [false; true; true], [true; true; false].
  repeat split.
    constructor. cbn. constructor.
    constructor. cbn. constructor. cbn. constructor.
    cbn. intro. assert (H' := Cycle_nth _ _ _ H 0 _ eq_refl).
      destruct H' as (m & H'). destruct m as [| [| m']]; inv H'.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Cycle vs zipW, unzip, unzipW *)
(* end hide *)

Lemma Cycle_any :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 -> any p l1 = any p l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite IHCycle, any_snoc, Bool.orb_comm. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_all :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 -> all p l1 = all p l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite IHCycle, all_snoc, Bool.andb_comm. reflexivity.
Qed.
(* end hide *)

Lemma Cycle_find :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A) (x : A),
    Cycle l1 l2 /\ find p l1 = Some x /\ find p l2 <> Some x.
(* begin hide *)
Proof.
  exists bool, (fun _ => true), [true; false], [false; true], true.
  repeat split.
    constructor. cbn. constructor.
    cbn. inversion 1.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Cycle vs findLast, removeFirst, removeLast *)
(* end hide *)

Lemma Cycle_findIndex :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A) (n : nat),
    Cycle l1 l2 /\ findIndex p l1 = Some n /\ findIndex p l2 <> Some n.
(* begin hide *)
Proof.
  exists bool, (fun b => b), [true; false], [false; true], 0.
  repeat split.
    constructor. cbn. constructor.
    cbn. inversion 1.
Qed.
(* end hide *)

Lemma Cycle_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    reflexivity.
    rewrite IHCycle, count_snoc.
      destruct (p x); rewrite plus_comm; reflexivity.
Qed.
(* end hide *)

Lemma Cycle_filter :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle (filter p l1) (filter p l2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    cbn. rewrite filter_snoc in IHCycle. destruct (p x).
      constructor. assumption.
      assumption.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Cycle vs findIndices *)
(* end hide *)

Lemma Cycle_takeWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (takeWhile p l1) (takeWhile p l2).
(* begin hide *)
Proof.
  exists bool, (fun b => b), [true; false], [false; true].
  repeat split.
    constructor. cbn. constructor.
    cbn. inversion 1.
Qed.
(* end hide *)

Lemma Cycle_dropWhile :
  exists (A : Type) (p : A -> bool) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (dropWhile p l1) (dropWhile p l2).
(* begin hide *)
Proof.
  exists bool, (fun b => b), [true; false], [false; true].
  repeat split.
    constructor. cbn. constructor.
    cbn. intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_pmap :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    Cycle l1 l2 -> Cycle (pmap f l1) (pmap f l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    rewrite pmap_snoc in IHCycle. destruct (f x).
      constructor. assumption.
      assumption.
Qed.
(* end hide *)

Lemma Cycle_intersperse :
  exists (A : Type) (x : A) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Cycle (intersperse x l1) (intersperse x l2).
(* begin hide *)
Proof.
  exists nat, 0, [1; 2], [2; 1]. split.
    do 2 constructor.
    cbn. intro. apply Cycle_spec in H. destruct H as (n & H1 & H2).
      destruct n as [| [| [| n']]]; inv H2.
Qed.
(* end hide *)

Lemma Cycle_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite Permutation_cons_snoc. assumption.
Qed.
(* end hide *)

Lemma Cycle_elem :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall x : A, elem x l1 <-> elem x l2.
(* begin hide *)
Proof.
  intros. apply Permutation_elem, Cycle_Permutation. assumption.
Qed.
(* end hide *)

Lemma Cycle_replicate' :
  forall (A : Type) (n m : nat) (x y : A),
    Cycle (replicate n x) (replicate m y) <->
    n = m /\ (n <> 0 -> m <> 0 -> x = y).
(* begin hide *)
Proof.
  split; intros.
    apply Cycle_Permutation, Permutation_replicate'' in H. assumption.
    destruct H. subst. destruct m as [| m']; cbn.
      constructor.
      specialize (H0 ltac:(inversion 1) ltac:(inversion 1)). subst.
        constructor.
Qed.
(* end hide *)

Lemma Cycle_In :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall x : A, In x l1 <-> In x l2.
(* begin hide *)
Proof.
  intros. apply Permutation_In, Cycle_Permutation, H.
Qed.
(* end hide *)

Lemma Cycle_NoDup :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> NoDup l1 -> NoDup l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_NoDup, Cycle_Permutation, H.
Qed.
(* end hide *)

Lemma Cycle_Dup :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Dup l1 -> Dup l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Dup, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Rep :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (x : A) (n : nat),
      Rep x n l1 -> Rep x n l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Rep, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Exists :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Cycle l1 l2 -> Exists P l1 -> Exists P l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Exists, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Forall :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    Cycle l1 l2 -> Forall P l1 -> Forall P l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Forall, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_AtLeast :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_AtLeast, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Exactly :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (P : A -> Prop) (n : nat),
      Exactly P n l1 -> Exactly P n l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_Exactly, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_AtMost :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall (P : A -> Prop) (n : nat),
      AtMost P n l1 -> AtMost P n l2.
(* begin hide *)
Proof.
  intros until 1. apply Permutation_AtMost, Cycle_Permutation, Cycle_sym, H.
Qed.
(* end hide *)

Lemma Cycle_Sublist :
  exists (A : Type) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Sublist l1 l2.
(* begin hide *)
Proof.
  exists unit, [], []. split.
    constructor.
    inversion 1.
Qed.
(* end hide *)

Lemma Sublist_Cycle :
  exists (A : Type) (l1 l2 : list A),
    Sublist l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists unit, [], [tt]. split.
    constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_Prefix :
  exists (A : Type) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Prefix l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    do 2 constructor.
    inversion 1.
Qed.
(* end hide *)

Lemma Prefix_Cycle :
  exists (A : Type) (l1 l2 : list A),
    Prefix l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists bool, [], [false]. split.
    constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_Subseq :
  exists (A : Type) (l1 l2 : list A),
    Cycle l1 l2 /\ ~ Subseq l1 l2.
(* begin hide *)
Proof.
  exists bool, [false; true], [true; false]. split.
    do 2 constructor.
    intro. inv H. inv H2.
      inv H0.
      inv H1.
Qed.
(* end hide *)

Lemma Subseq_Cycle :
  exists (A : Type) (l1 l2 : list A),
    Subseq l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists bool, [], [false]. split.
    constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_Incl :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> Incl l1 l2.
(* begin hide *)
Proof.
  induction 1.
    apply Incl_refl.
    unfold Incl in *. intros. specialize (IHCycle _ H0).
      rewrite elem_snoc in IHCycle. destruct IHCycle.
        right. assumption.
        subst. left.
Qed.
(* end hide *)

Lemma Incl_Cycle :
  exists (A : Type) (l1 l2 : list A),
    Incl l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. split.
    unfold Incl. destruct x. constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

Lemma Cycle_SetEquiv :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  intros. rewrite SetEquiv_Incl. split; apply Cycle_Incl.
    assumption.
    apply Cycle_sym. assumption.
Qed.
(* end hide *)

Lemma SetEquiv_Cycle :
  exists (A : Type) (l1 l2 : list A),
    SetEquiv l1 l2 /\ ~ Cycle l1 l2.
(* begin hide *)
Proof.
  exists unit, [tt; tt], [tt]. split.
    rewrite SetEquiv_Incl; unfold Incl. split; destruct x; constructor.
    intro. apply Cycle_length in H. inv H.
Qed.
(* end hide *)

(** ** Partycje list (TODO) *)

Module Partition.

Definition Partition
  {A : Type} (ll : list (list A)) (l : list A) : Prop :=
    Permutation (join ll) l.

Lemma Partition_rev :
  forall {A : Type} (ll : list (list A)) (l : list A),
    Partition ll l -> Partition (rev (map rev ll)) (rev l).
Proof.
  unfold Partition. intros.
  rewrite <- rev_join, !Permutation_rev.
  assumption.
Qed.

End Partition.

Module OPartition.

Record OPartition
  {A : Type} (ll : list (list A)) (l : list A) : Prop :=
{
    nonempty : forall l' : list A, elem l' ll -> l' <> [];
    all : join ll = l;
}.

End OPartition.

Module IPartition.

Inductive IPartition {A : Type} : list (list A) -> list A -> Prop :=
    | IP_nil : IPartition [] []
    | IP_cons :
        forall {ll : list (list A)} {l1 l2 : list A},
          l1 <> [] -> IPartition ll l2 ->
            IPartition (l1 :: ll) (l1 ++ l2).

Lemma IPartition_spec :
  forall {A : Type} {ll : list (list A)} {l : list A},
    IPartition ll l -> join ll = l.
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHIPartition. reflexivity.
Qed.

Lemma IPartition_spec_conv :
  forall {A : Type} (ll : list (list A)) (l : list A),
    (forall l' : list A, elem l' ll -> l' <> []) ->
      join ll = l -> IPartition ll l.
Proof.
  induction ll as [| hh tt]; cbn; intros; subst.
    constructor.
    constructor.
      apply H. constructor.
      apply IHtt.
        intros. apply H. constructor. assumption.
        reflexivity.
Qed.

Lemma IPartition_app :
  forall {A : Type} (ll1 ll2 : list (list A)) (l1 l2 : list A),
    IPartition ll1 l1 -> IPartition ll2 l2 ->
      IPartition (ll1 ++ ll2) (l1 ++ l2).
Proof.
  intros until 1. revert ll2 l2.
  induction H; cbn; intros.
    assumption.
    rewrite <- app_assoc. constructor.
      assumption.
      apply IHIPartition. assumption.
Qed.

Lemma IPartition_rev :
  forall {A : Type} (ll : list (list A)) (l : list A),
    IPartition ll l -> IPartition (map rev (rev ll)) (rev l).
Proof.
  induction 1; cbn.
    constructor.
    rewrite map_app, rev_app. cbn. apply IPartition_app.
      assumption.
      rewrite <- app_nil_r. constructor.
        intro. apply H. destruct l1.
          reflexivity.
          apply (f_equal length) in H1. rewrite length_rev in H1.
            cbn in H1. inv H1.
        constructor.
Qed.

Lemma IPartition_map :
  forall {A B : Type} {ll : list (list A)} {l : list A},
    IPartition ll l ->
      forall f : A -> B, IPartition (map (map f) ll) (map f l).
Proof.
  induction 1; cbn; intros.
    constructor.
    rewrite map_app. constructor.
      intro. apply H. destruct l1.
        reflexivity.
        inv H1.
      apply IHIPartition.
Qed.

End IPartition.

(** * Niestandardowe reguły indukcyjne (TODO) *)

(** Wyjaśnienia nadejdą już wkrótce. *)

Fixpoint list_ind_2
  (A : Type) (P : list A -> Prop)
  (H0 : P [])
  (H1 : forall x : A, P [x])
  (H2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
    (l : list A) : P l.
(* begin hide *)
Proof.
  destruct l as [| x [| y l]]; cbn; auto.
  apply H2. apply list_ind_2; auto.
Qed.
(* end hide *)

Lemma list_ind_rev :
  forall (A : Type) (P : list A -> Prop)
    (Hnil : P [])
    (Hsnoc : forall (h : A) (t : list A), P t -> P (t ++ [h]))
      (l : list A), P l.
(* begin hide *)
Proof.
  intros. cut (forall l : list A, P (rev l)); intro.
    specialize (H (rev l)). rewrite <- rev_inv. assumption.
    induction l0 as [| h t]; cbn.
      assumption.
      apply Hsnoc. assumption.
Qed.
(* end hide *)

Lemma list_ind_app_l :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l' ++ l))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    assumption.
    apply (IH _ [h]). assumption.
Qed.
(* end hide *)

Lemma list_ind_app_r :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t] using list_ind_rev; cbn.
    assumption.
    apply (IH t [h]). assumption.
Qed.
(* end hide *)

Lemma list_ind_app :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (IH : forall l l' : list A, P l -> P l' -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    assumption.
    apply (IH [h] t); auto.
Qed.
(* end hide *)

Lemma list_app_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (l l1 l2 : list A), P l -> P (l1 ++ l ++ l2)) ->
      forall l : list A, P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply H.
    specialize (H0 t [h] [] IHt). rewrite app_nil_r in H0.
      cbn in H0. assumption.
Qed.
(* end hide *)

(** ** Palindromy *)

(** Palindrom to słowo, które czyta się tak samo od przodu jak i od tyłu.

    Zdefiniuj induktywny predykat [Palindrome], które odpowiada powyższemu
    pojęciu palindromu, ale dla list elementów dowolnego typu, a nie tylko
    słów. *)

(* begin hide *)
Inductive Palindrome {A : Type} : list A -> Prop :=
    | Palindrome_nil : Palindrome []
    | Palindrome_singl :
        forall x : A, Palindrome [x]
    | Palindrome_1 :
        forall (x : A) (l : list A),
          Palindrome l -> Palindrome (x :: l ++ [x]).
(* end hide *)

(* begin hide *)

Lemma Palindrome_inv :
  forall (A : Type) (x : A) (l : list A),
    Palindrome (x :: l ++ [x]) -> Palindrome l.
(* begin hide *)
Proof.
  intros. inv H.
    apply (f_equal length) in H2. rewrite length_app in H2.
      cbn in H2. rewrite <- plus_n_Sm in H2. inv H2.
    apply app_inv_r in H2. subst. assumption.
Qed.
(* end hide *)

Lemma Palindrome_inv_2 :
  forall (A : Type) (x y : A),
    Palindrome [x; y] -> x = y.
(* begin hide *)
Proof.
  intros. inv H. apply (f_equal last) in H2.
  rewrite last_app in H2. inv H2. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_inv_3 :
  forall (A : Type) (x y : A) (l : list A),
    Palindrome (x :: l ++ [y]) -> x = y.
(* begin hide *)
Proof.
  intros. inv H.
    apply (f_equal isEmpty) in H2. rewrite isEmpty_app in H2.
      destruct l; inv H2.
    apply (f_equal last) in H2. rewrite ?last_app in H2. inv H2.
      reflexivity.
Qed.
(* end hide *)

Lemma nat_ind_2 :
  forall P : nat -> Prop,
    P 0 -> P 1 -> (forall n : nat, P n -> P (S (S n))) ->
      forall n : nat, P n.
(* begin hide *)
Proof.
  fix IH 5. destruct n as [| [| n']].
    1-2: assumption.
    apply H1, IH; assumption.
Qed.
(* end hide *)

Lemma Palindrome_length :
  forall (A : Type) (x : A) (n : nat),
    exists l : list A, Palindrome l /\ n <= length l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    exists []. split; constructor.
    destruct IHn' as (l & IH1 & IH2).
      exists (x :: l ++ [x]). split.
        constructor. assumption.
        cbn. rewrite length_app. cbn. lia.
Restart.
  induction n as [| | n'] using nat_ind_2.
    exists []. split; constructor.
    exists [x]. split; constructor.
    destruct IHn' as (l & IH1 & IH2). exists (x :: l ++ [x]). split.
      constructor. assumption.
      cbn. rewrite length_app. cbn. lia.
Qed.
(* end hide *)

Lemma Palindrome_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (x :: snoc x l).
(* begin hide *)
Proof.
  intros. rewrite snoc_app_singl. constructor. assumption.
Qed.
(* end hide *)

Lemma Palindrome_app :
  forall (A : Type) (l1 l2 : list A),
    Palindrome l1 -> Palindrome l2 -> Palindrome (l1 ++ l2 ++ rev l1).
(* begin hide *)
Proof.
  intros A l1 l2 H. revert l2.
  induction H; cbn; intros.
    rewrite app_nil_r. assumption.
    constructor. assumption.
    replace _ with
        (Palindrome (x :: (l ++ ([x] ++ l2 ++ [x]) ++ rev l) ++ [x])).
      constructor. apply IHPalindrome. cbn. constructor. assumption.
      rewrite rev_app, !app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_app' :
  forall (A : Type) (l1 l2 : list A),
    Palindrome l2 -> Palindrome (l1 ++ l2 ++ rev l1).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite app_nil_r. assumption.
    replace _ with (Palindrome (h1 :: (t1 ++ l2 ++ rev t1) ++ [h1])).
      constructor. apply IHt1. assumption.
      rewrite ?app_assoc. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_rev :
  forall (A : Type) (l : list A),
    Palindrome l <-> Palindrome (rev l).
(* begin hide *)
Proof.
  assert (forall (A : Type) (l : list A),
            Palindrome l -> Palindrome (rev l)).
    induction 1; cbn.
      1-2: constructor.
      rewrite rev_app. cbn. constructor. assumption.
    split; intro.
      apply H. assumption.
      rewrite <- rev_inv. apply H. assumption.
Qed.
(* end hide *)

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Lemma lengthOrder_wf :
  forall A : Type, well_founded (@lengthOrder A).
(* begin hide *)
Proof.
  unfold well_founded. induction a as [| h t]; cbn.
    constructor. intros. inv H.
    inv IHt. constructor. intros. constructor. intros. apply H.
      cbn in *. unfold lengthOrder in *. cbn in *. lia.
Qed.
(* end hide *)

Lemma Palindrome_spec :
  forall (A : Type) (l : list A),
    Palindrome l <-> l = rev l.
(* begin hide *)
(* TODO: Palindrome_spec bez używania indukcji dobrze ufundowanej *)
Proof.
  split.
    induction 1; cbn.
      1-2: reflexivity.
      rewrite rev_app, <- IHPalindrome; cbn. reflexivity.
    revert l.
    eapply
    (@well_founded_ind _
      _ (@lengthOrder_wf A)
      (fun l : list A => l = rev l -> Palindrome l) _) .
Unshelve.
  unfold lengthOrder.
  destruct x as [| h t]; cbn; intros.
    constructor.
    destruct (rev t) eqn: Heq.
      inv H0. constructor.
      rewrite H0. inv H0. constructor. apply H.
        rewrite length_app. apply le_n_S. cbn.
          rewrite <- plus_n_Sm, <- plus_n_O. apply le_S, le_n.
        rewrite rev_app in Heq. cbn in Heq. inv Heq.
          rewrite H1. symmetry. assumption.
Qed.
(* end hide *)

Lemma Palindrome_spec' :
  forall (A : Type) (l : list A),
    Palindrome l -> exists l1 l2 : list A,
      l = l1 ++ l2 ++ rev l1 /\ length l2 <= 1.
(* begin hide *)
Proof.
  induction 1; cbn.
    exists [], []. cbn. split; [reflexivity | apply le_0_n].
    exists [], [x]. cbn. split; [reflexivity | apply le_n].
    destruct IHPalindrome as (l1 & l2 & IH1 & IH2). subst.
      exists (x :: l1), l2. cbn. split.
        rewrite ?app_assoc. reflexivity.
        assumption.
Qed.
(* end hide *)

Lemma Palindrome_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    Palindrome l -> Palindrome (map f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    1-2: constructor.
    rewrite map_app. cbn. constructor. assumption.
Qed.
(* end hide *)

Lemma replicate_S :
  forall (A : Type) (n : nat) (x : A),
    replicate (S n) x = x :: replicate n x.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma Palindrome_replicate :
  forall (A : Type) (n : nat) (x : A),
    Palindrome (replicate n x).
(* begin hide *)
Proof.
  induction n as [| | n'] using nat_ind_2; intros.
    constructor.
    constructor.
    rewrite replicate_S, <- rev_replicate. cbn. constructor.
      rewrite rev_replicate. apply IHn'.
Qed.
(* end hide *)

Lemma Palindrome_cons_replicate :
  forall (A : Type) (n : nat) (x y : A),
    Palindrome (x :: replicate n y) -> n = 0 \/ x = y.
(* begin hide *)
Proof.
  destruct n as [| n']; intros.
    left. reflexivity.
    right. rewrite <- snoc_replicate, snoc_app_singl in H.
      apply Palindrome_inv_3 in H. assumption.
Qed.
(* end hide *)

Lemma Palindrome_iterate :
  forall (A : Type) (f : A -> A),
    (forall (n : nat) (x : A), Palindrome (iterate f n x)) ->
      forall x : A, f x = x.
(* begin hide *)
Proof.
  intros. specialize (H 2 x). cbn in H. inv H. destruct l; inv H2.
    rewrite <- ?H0. reflexivity.
    apply (f_equal isEmpty) in H3. rewrite isEmpty_app in H3.
      destruct l; inv H3.
Qed.
(* end hide *)

Lemma Palindrome_nth :
  forall (A : Type) (l : list A),
    Palindrome l -> forall n : nat,
      n < length l -> nth n l = nth (length l - S n) l.
(* begin hide *)
Proof.
  intros. apply Palindrome_spec in H.
  rewrite H at 1. apply nth_rev. assumption.
Qed.
(* end hide *)

Lemma Palindrome_drop :
  forall (A : Type) (l : list A),
    (forall n : nat, Palindrome (drop n l)) ->
      l = [] \/ exists (n : nat) (x : A), l = replicate n x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. reflexivity.
    right. destruct IHt.
      intro. specialize (H (S n)). cbn in H. assumption.
      subst. exists 1, h. cbn. reflexivity.
      destruct H0 as (n & x & IH). subst. exists (S n), h. cbn.
        specialize (H 0). cbn in H. apply Palindrome_cons_replicate in H.
          destruct H; subst; cbn; reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_take :
  forall (A : Type) (l : list A),
    (forall n : nat, Palindrome (take n l)) ->
      l = [] \/ exists (n : nat) (x : A), l = replicate n x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. reflexivity.
    right. destruct IHt.
      intro. specialize (H n). destruct n as [| n']; cbn in *.
        rewrite take_0. constructor. admit.
        exists 1, h. cbn. subst. reflexivity.
        destruct H0 as (n & x & IH). subst. exists (S n), h. cbn. f_equal.
          specialize (H (S n)). cbn in H. rewrite take_replicate in H.
            rewrite Nat.min_id in H. inversion H; subst.
              destruct n; inversion H2; cbn. reflexivity.
              pose (H2' := H2). apply (f_equal last) in H2'. rewrite last_app, last_replicate in H2'.
                destruct n; cbn in *; inversion H2'; subst. assumption.
Admitted.
(* end hide *)

Lemma replace_Palindrome :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' -> Palindrome l ->
      Palindrome l' <-> length l = 1 /\ n = 0 \/ nth n l = Some x.
(* begin hide *)
Proof.
  split.
    Focus 2. destruct 1 as [[H1 H2] | H1].
      subst. destruct l as [| h [| h' t]]; inv H; inv H1. constructor.
      assert (l = l').
        rewrite replace_nth_eq; eassumption.
        subst. assumption.
    intros. apply Palindrome_spec in H0. apply Palindrome_spec in H1.
      rewrite H0, H1 in H. rewrite replace_rev in H.
        unfold omap in H.
Abort.
(* end hide *)

Lemma Palindrome_zip :
  exists (A B : Type) (la : list A) (lb : list B),
    Palindrome la /\ Palindrome lb /\ ~ Palindrome (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool, [true; true], [false; true; false].
  cbn. repeat split.
    apply (Palindrome_1 true []). constructor.
    apply (Palindrome_1 false [true]). constructor.
    intro. apply Palindrome_inv_2 in H. inv H.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Palindrome vs unzip, zipWith, unzipWith *)
(* end hide *)

Lemma Palindrome_find_findLast :
  forall (A : Type) (p : A -> bool) (l : list A),
    Palindrome l -> find p l = findLast p l.
(* begin hide *)
Proof.
  intros. rewrite find_findLast. apply Palindrome_spec in H.
  rewrite <- H. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    Palindrome l -> Palindrome (pmap f l).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    destruct (f x); constructor.
    destruct (f x) eqn: Heq; cbn.
      rewrite pmap_app. cbn. rewrite Heq. constructor. assumption.
      rewrite pmap_app. cbn. rewrite Heq, app_nil_r. assumption.
Qed.
(* end hide *)

Lemma Palindrome_intersperse :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (intersperse x l).
(* begin hide *)
Proof.
  intros. rewrite Palindrome_spec in *.
  rewrite <- intersperse_rev, <- H. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Palindrome vs groupBy *)
(* end hide *)

Lemma Palindrome_Dup :
  forall (A : Type) (l : list A),
    Palindrome l -> length l <= 1 \/ Dup l.
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    left. apply le_0_n.
    left. apply le_n.
    right. constructor. rewrite elem_app. right. left.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: Palindrome vs Incl, Sublist, subseq *)
(* end hide *)

Lemma Sublist_Palindrome :
  forall (A : Type) (l1 l2 : list A),
    Sublist l1 l2 -> Palindrome l1 -> Palindrome l2 -> l1 = [].
(* begin hide *)
Proof.
  induction 1; intros.
Abort.
(* end hide *)

Lemma Prefix_Palindrome :
  forall (A : Type) (l : list A),
    Prefix (rev l) l <-> Palindrome l.
(* begin hide *)
Proof.
  split; intro.
    apply Prefix_rev_l in H. rewrite Palindrome_spec. assumption.
    apply Palindrome_spec in H. rewrite <- H. apply Prefix_refl.
Qed.
(* end hide *)

Lemma Subseq_rev_l :
  forall (A : Type) (l : list A),
    Subseq (rev l) l <-> Palindrome l.
(* begin hide *)
Proof.
  split.
    intro. apply Palindrome_spec. induction l as [| h t]; cbn; intros.
      reflexivity.
Abort.
(* end hide *)

Lemma Subseq_rev_r :
  forall (A : Type) (l : list A),
    Subseq l (rev l) <-> Palindrome l.
(* begin hide *)
Proof.
  split.
    Focus 2. intro. apply Palindrome_spec in H. rewrite <- H.
      apply Subseq_refl.
Abort.
(* end hide *)