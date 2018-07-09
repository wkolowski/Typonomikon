(** * X3: Listy *)

(** Lista to najprostsza i najczęściej używana w programowaniu funkcyjnym
    struktura danych. Czas więc przeżyć na własnej skórze ich implementację.

    UWAGA: ten rozdział wyewoluował do stanu dość mocno odbiegającego od
    tego, co jest w bibliotece standardowej — moim zdanem na korzyść. *)

Require Export Arith.
(* begin hide *)
Require Export Omega.
(* end hide *)

(** W części dowodów przydadzą nam się fakty dotyczące arytmetyki liczb
    naturalnych, które możemy znaleźć w module [Arith]. *)

(** Zdefiniuj [list] (bez podglądania). *)

(* begin hide *)
Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.
(* end hide *)

Arguments nil [A].
Arguments cons [A] _ _.

(*Notation "[ ]" := nil.*)
Notation "[ ]" := nil (format "[ ]").
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** * Proste funkcje *)

(** ** [isEmpty] (TODO) *)

(** Zdefiniuj funkcję [isEmpty], która sprawdza, czy lista jest pusta. *)

(* begin hide *)
Definition isEmpty {A : Type} (l : list A) : bool :=
match l with
    | [] => true
    | _ => false
end.
(* end hide *)

(** ** [length] *)

(** Zdefiniuj funkcję [length], która oblicza długość listy. *)

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

(** ** [snoc] (TODO) *)

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

(** ** [app] *)

(** Zdefiniuj funkcję [app], która skleja dwie listy. *)

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

(** Zdefiniuj funkcję [rev], która odwraca listę. *)

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
    elementu listy. *)

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

(** Napisz funkcję [join], która spłaszcza listę list. *)

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

(** ** [bind] (TODO) *)

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

(** Napsiz funkcję [replicate], która powiela dany element [n] razy, tworząc
    listę. *)

(* begin hide *)
Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
match n with
    | 0 => []
    | S n' => x :: replicate n' x
end.
(* end hide *)

(* TODO *)
Lemma isEmpty_replicate :
  forall (A : Type) (n : nat) (x : A),
    isEmpty (replicate n x) =
    match n with
        | 0 => true
        | _ => false
    end.
(* begin hide *)
Proof.
  destruct n as [| n']; cbn; reflexivity.
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

(** ** [iterate] i [iter] (TODO) *)

(** Napisz funkcję [iterate]. [iterate f n x] to lista postaci
    [x, f x, f (f x), ..., f (... (f x) ...)] o długości [n].

    (TODO) Napisz też funkcję [iter], która przyda się do podania
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
Lemma rev_iterate :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      iterate f n x = rev (iterate g n (iter f n x)).
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

Lemma map_iter_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    map (iter f m) (iterate f n x) =
    iterate f n (iter f m x).
(* begin ihde *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. revert x. induction m as [| m']; cbn; intros.
      reflexivity.
      rewrite IHm'. reflexivity.
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

(** ** [head], [tail] i [uncons] *)

(** *** [head] *)

(** Zdefiniuj funkcję [head], która zwraca głowę (pierwszy element)
    listy lub [None], gdy lista jest pusta. *)

(* begin hide *)
Fixpoint head {A : Type} (l : list A) : option A :=
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
    jej elementy poza głową) lub [None], gdy lista jest pusta. *)

(* begin hide *)
Fixpoint tail {A : Type} (l : list A) : option (list A) :=
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

(** Napisz funkcję [uncons], która zwraca parę złożoną z głowy i ogona
    listy lub [None], gdy lista jest pusta. Nie używaj funkcji [head]
    ani [tail]. Udowodnij poniższą specyfikację. *)

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
    [None], gdy lista jest pusta. *)

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
    ostatnim lub [None], gdy lista jest pusta. *)

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

(* TODO *)
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

(** *** [unsnoc] *)

(** Zdefiniuj funkcję [unsnoc], która rozbija listę na parę złożoną z
    ostatniego elementu oraz całej reszty lub zwraca [None] gdy lista
    jest pusta. Nie używaj funkcji [last] ani [init]. Udowodnij poniższą
    specyfikację. *)

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
    gdy nie ma n-tego elementu. *)

(* begin hide *)
Fixpoint nth {A : Type} (n : nat) (l : list A) : option A :=
match n, l with
    | _, [] => None
    | 0, h :: t => Some h
    | S n', h :: t => nth n' t
end.
(* end hide *)

Lemma nth_nil :
  forall (A : Type) (n : nat),
    nth n (@nil A) = None.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma nth_isEmpty_true :
  forall (A : Type) (n : nat) (l : list A),
    isEmpty l = true -> nth n l = None.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; intros.
    rewrite nth_nil. reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma isEmpty_nth_not_None :
  forall (A : Type) (n : nat) (l : list A),
    nth n l <> None -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct n as [| n'], l as [| h t]; cbn; intros.
    1,3: contradiction.
    all: reflexivity.
Qed.
(* end hide *)

Lemma nth_length :
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> exists x : A, nth n l = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    destruct l.
      inversion H.
      exists a. cbn. trivial.
    destruct l; cbn in *.
      inversion H.
      destruct (IHn' _ (lt_S_n _ _ H)) as [x IH]. exists x. assumption.
Qed.
(* end hide *)

Lemma nth_overflow :
  forall (A : Type) (n : nat) (l : list A),
    length l <= n -> ~ exists x : A, nth n l = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l; cbn; intros.
    destruct 1. inversion H0.
    inversion H.
    destruct 1. inversion H0.
    apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_overflow' :
  forall (A : Type) (n : nat) (l : list A),
    length l <= n -> nth n l = None.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn.
    1,3: reflexivity.
    all: inversion 1; subst.
      apply IHn', le_n.
      apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_snoc_lt :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l -> nth n (snoc x l) = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      reflexivity.
      apply lt_S_n in H. rewrite ?(IHt _ H).
        reflexivity.
Qed.
(* end hide *)

Lemma nth_snoc_length :
  forall (A : Type) (x : A) (l : list A),
    nth (length l) (snoc x l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma nth_app_l :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    n < length l1 -> nth n (l1 ++ l2) = nth n l1.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l1; cbn; intros.
    inversion H.
    trivial.
    inversion H.
    apply IHn'. apply lt_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_app_r :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 <= n -> nth n (l1 ++ l2) = nth (n - length l1) l2.
(* begin hide *)
Proof.
  induction n as [| n'].
    destruct l1 as [| h1 t1]; intros.
      destruct l2; cbn; trivial.
      destruct l2; cbn; inversion H.
    destruct l1 as [| h1 t1]; intros.
      cbn. trivial.
      cbn in *. apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma nth_split :
  forall (A : Type) (n : nat) (l : list A) (x : A),
    nth n l = Some x -> exists l1 l2 : list A,
      l = l1 ++ x :: l2 /\ length l1 = n.
(* begin hide *)
Proof.
  induction n as [| n'].
    destruct l as [| h t]; cbn; inversion 1; subst. exists [], t.
      cbn. split; trivial.
    destruct l as [| h t]; cbn; inversion 1; subst.
      destruct (IHn' _ _ H) as [l1 [l2 [Heq Hlen]]].
      exists (h :: l1), l2. split.
        rewrite Heq. trivial.
        cbn. rewrite Hlen. trivial.
Qed.
(* end hide *)

Lemma nth_None :
  forall (A : Type) (n : nat) (l : list A),
    nth n l = None -> length l <= n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
    trivial.
    inversion H.
    apply le_0_n.
    apply le_n_S. apply IHn'. assumption.
Qed.
(* end hide *)

Lemma nth_Some :
  forall (A : Type) (n : nat) (l : list A) (x : A),
    nth n l = Some x -> n < length l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
    inversion H.
    red. apply le_n_S. apply le_0_n.
    inversion H.
    apply lt_n_S. eapply IHn'. eassumption.
Qed.
(* end hide *)

Lemma nth_map :
  forall (A B : Type) (f : A -> B) (n : nat) (l : list A) (x : A),
    nth n l = Some x -> nth n (map f l) = Some (f x).
(* begin hide *)
Proof.
  induction n as [| n'].
    destruct l as [| h t]; cbn; inversion 1; trivial.
    destruct l as [| h t]; cbn; inversion 1; trivial.
      rewrite (IHn' t x); [trivial | assumption].
Qed.
(* end hide *)

Lemma nth_replicate :
  forall (A : Type) (i n : nat) (x : A),
    i < n -> nth i (replicate n x) = Some x.
(* begin hide *)
Proof.
  induction i as [| i']; destruct n as [| n']; cbn; intros.
    inversion H.
    reflexivity.
    inversion H.
    rewrite IHi'.
      trivial.
      apply lt_S_n. assumption.
Qed.
(* end hide *)

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

Lemma head_nth :
  forall (A : Type) (l : list A), head l = nth 0 l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; trivial.
Qed.
(* end hide *)

Lemma last_nth :
  forall (A : Type) (l : list A),
    last l = nth (length l - 1) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct t.
      cbn. reflexivity.
      rewrite IHt. cbn. rewrite <- minus_n_O. reflexivity.
Qed.
(* end hide *)

(** ** [insert] *)

(** TODO *)

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
  forall (A : Type) (l : list A) (x : A),
    insert l (length l) x = snoc x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; rewrite ?IHt; reflexivity.
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
        rewrite insert_snoc, snoc_app, rev_app, rev_snoc, rev_inv.
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

(* TODO: [join], [bind] *)

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

(* TODO: [iterate] *)

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

(* TODO: init *)

Lemma nth_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n <= length l -> nth n (insert l n x) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    1,3: reflexivity.
    inversion H.
    apply le_S_n in H. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma nth_insert' :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n (insert l n x) =
    if leb n (length l) then Some x else None.
(* begin hide *)
Proof.
  induction l as [| h t]; destruct n as [| n']; cbn; intros.
    1,3: reflexivity.
    rewrite nth_nil. reflexivity.
    apply IHt.
Qed.
(* end hide *)

(** ** [remove] (TODO) *)

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

(*
Lemma isEmpty_remove :
  forall (A : Type) (l : list A) (n : nat),
    isEmpty (remove n l) =
    orb (isEmpty l) (andb (leb (length l) 1) (isZero n)).
(* begin hide *)
Proof.
  destruct l; cbn.
Abort.
*)

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
  induction l as [| h t]; cbn.
    destruct n; inversion 1.
    destruct n as [| n']; cbn; intros.
      reflexivity.
      apply lt_S_n in H. rewrite (IHt _ H). destruct (remove n' t).
        destruct p. all: reflexivity.
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
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      destruct t.
        cbn. reflexivity.
        rewrite remove_app_lt. cbn in *.
          rewrite (IHt 0), <- minus_n_O.
            destruct (length t); cbn.
              reflexivity.
              destruct (remove n t).
                destruct p; cbn. 1-2: reflexivity.
            apply le_n_S, le_0_n.
          rewrite length_rev; cbn. apply le_n_S, le_0_n.
      destruct (rev t) eqn: Heq; cbn.
        apply (f_equal rev) in Heq. rewrite rev_inv in Heq.
          rewrite Heq in H. cbn in H. apply lt_S_n in H.
          destruct n'; inversion H.
Abort.
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

(** ** [take] *)

(** Zdefiniuj funkcję [take], która bierze z listy [n] początkowych
    elementów. *)

(* begin hide *)
Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.
(* end hide *)

Lemma take_0 :
  forall (A : Type) (l : list A),
    take 0 l = [].
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma take_nil :
  forall (A : Type) (n : nat),
    take n [] = @nil A.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma take_S_cons :
  forall (A : Type) (n : nat) (h : A) (t : list A),
    take (S n) (h :: t) = h :: take n t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma isEmpty_take :
  forall (A : Type) (n : nat) (l : list A),
    isEmpty (take n l) = orb (beq_nat 0 n) (isEmpty l).
(* begin hide *)
Proof.
  destruct n as [| n'], l as [| h t]; cbn; intros; trivial.
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
  forall (A : Type) (n : nat) (l : list A),
    length l <= n -> take n l = l.
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    cbn. destruct l; inversion H; trivial.
    destruct l as [| h t]; simpl.
      reflexivity.
      rewrite IHn'.
        reflexivity.
        cbn in H. apply le_S_n in H. assumption.
Qed.
(* end hide *)

Lemma length_take :
  forall (A : Type) (n : nat) (l : list A),
    length (take n l) = min n (length l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma take_snoc_lt :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l -> take n (snoc x l) = take n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?(IHt _ (lt_S_n _ _ H)). reflexivity.
Qed.
(* end hide *)

Lemma take_app_l :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    n <= length l1 -> take n (l1 ++ l2) = take n l1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    induction l1 as [| h1 t1]; cbn; intros.
      inversion H.
      rewrite IHn'.
        reflexivity.
        apply le_S_n. assumption.
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

Lemma take_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    take n (l1 ++ l2) = take n l1 ++ take (n - length l1) l2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l1 as [| h t]; cbn; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma take_map :
  forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
    take n (map f l) = map f (take n l).
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    destruct l as [| h t]; simpl.
      trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

(* TODO: join, bind *)

Lemma take_replicate :
  forall (A : Type) (m n : nat) (x : A),
    take m (replicate n x) = replicate (min m n) x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct n as [| n'];
  cbn; intros; rewrite ?IHm'; reflexivity.
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
Restart.
  intros A f n m. revert n.
  induction m as [| m']; cbn; intros.
    rewrite Nat.min_0_r. cbn. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHm'. reflexivity.
Qed.
(* end hide *)

Lemma head_take :
  forall (A : Type) (n : nat) (l : list A),
    head (take n l) =
    if beq_nat 0 n then None else head l.
(* begin hide *)
Proof.
  destruct n, l; reflexivity.
Qed.
(* end hide *)

Lemma last_take :
  forall (A : Type) (n : nat) (l : list A),
    last (take (S n) l) = nth (min n (length l - 1)) l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn.
    1-3: reflexivity.
    destruct t; cbn.
      reflexivity.
      specialize (IHn' (a :: t)). cbn in IHn'.
        rewrite IHn', <- minus_n_O. reflexivity.
Qed.
(* end hide *)

(* TODO: lepsze last_take *)

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
  forall (A : Type) (n : nat) (l : list A),
    init (take n l) =
    match n, l with
        | 0, _ => None
        | _, [] => None
        | S n', h :: t => Some (take (min n' (length l - 1)) l)
    end.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn.
    1-3: reflexivity.
    rewrite IHn'. destruct n', t; cbn.
      1-3: reflexivity.
      rewrite <- minus_n_O. reflexivity.
Qed.
(* end hide *)

Lemma nth_take :
  forall (A : Type) (n m : nat) (l : list A),
    nth m (take n l) =
    if leb (S m) n then nth m l else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    apply nth_nil.
    destruct l as [| h t]; cbn.
      rewrite ?nth_nil. destruct (_ <=? _); reflexivity.
      destruct m as [| m']; cbn.
        reflexivity.
        rewrite IHn'. destruct n'; reflexivity.
Qed.
(* end hide *)

(* TODO: take_remove *)

Lemma insert_take :
  forall (A : Type) (l : list A) (n m : nat) (x : A),
    insert (take n l) m x =
    if leb m n
    then take (S n) (insert l m x)
    else snoc x (take n l).
(* begin hide *)
Proof.
  intros A l n. revert l.
  induction n as [| n']; cbn; intros.
    destruct m as [| m']; cbn.
      rewrite insert_0. 1-2: reflexivity.
    destruct l as [| h t]; cbn.
      destruct (_ <=? _); reflexivity.
      destruct m as [| m']; cbn.
        reflexivity.
        rewrite IHn'. destruct (m' <=? n'), (insert t m' x); reflexivity.
Qed.
(* end hide *)

Lemma take_S_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    take (S n) (insert l n x) = snoc x (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite ?take_nil. cbn. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      specialize (IHt n' x). destruct (insert t n' x).
        rewrite <- IHt, take_nil. reflexivity.
        rewrite <- IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma take_take :
  forall (A : Type) (n m : nat) (l : list A),
    take m (take n l) = take (min n m) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite take_nil. reflexivity.
    destruct l as [| h t]; cbn.
      rewrite !take_nil. reflexivity.
      destruct m as [| m']; cbn.
        reflexivity.
        rewrite IHn'. reflexivity.
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

(** ** [drop] *)

(** Zdefiniuj funkcję [drop], która wyrzuca z listy [n] początkowych
    elementów i zwraca to, co zostało. *)

(* begin hide *)
Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => l
    | _, [] => []
    | S n', h :: t => drop n' t
end.
(* end hide *)

Lemma drop_0 :
  forall (A : Type) (l : list A),
    drop 0 l = l.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma drop_nil :
  forall (A : Type) (n : nat),
    drop n [] = @nil A.
(* begin hide *)
Proof.
  destruct n; reflexivity.
Qed.
(* end hide *)

Lemma drop_S_cons :
  forall (A : Type) (n : nat) (h : A) (t : list A),
    drop (S n) (h :: t) = drop n t.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma isEmpty_drop :
  forall (A : Type) (n : nat) (l : list A),
    isEmpty (drop n l) = leb (length l) n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn.
    1-3: reflexivity.
    rewrite IHn'. reflexivity.
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
  forall (A : Type) (n : nat) (l : list A),
    length l <= n -> drop n l = [].
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    simpl. destruct l; inversion H; trivial.
    destruct l as [| h t]; simpl.
      trivial.
      rewrite IHn'.
        trivial.
        simpl in H. apply le_S_n in H. assumption.
Qed.
(* end hide *)

Lemma length_drop :
  forall (A : Type) (n : nat) (l : list A),
    length (drop n l) = length l - n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn;
  rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma drop_snoc_lt :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l -> drop n (snoc x l) = snoc x (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?(IHt _ (lt_S_n _ _ H)). reflexivity.
Qed.
(* end hide *)

Lemma drop_app_l :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    n <= length l1 -> drop n (l1 ++ l2) = drop n l1 ++ l2.
(* begin hide *)
Proof.
  induction n as [| n']; induction l1 as [| h1 t2]; cbn; firstorder.
  inversion H.
Qed.
(* end hide *)

Lemma drop_app_r :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 < n -> drop n (l1 ++ l2) = drop (n - length l1) l2.
(* begin hide *)
Proof.
  induction n as [| n']; induction l1 as [| h1 t2]; cbn; firstorder.
  inversion H.
Qed.
(* end hide *)

Lemma drop_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    drop n (l1 ++ l2) = drop n l1 ++ drop (n - length l1) l2.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l1;
  cbn; intros; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma drop_map :
  forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
    drop n (map f l) = map f (drop n l).
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    destruct l as [| h t]; simpl.
      trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

(* TODO: join, bind *)

Lemma drop_replicate :
  forall (A : Type) (m n : nat) (x : A),
    drop m (replicate n x) = replicate (n - m) x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct n as [| n']; cbn; intros; trivial.
Qed.
(* end hide *)

Lemma drop_iterate :
  forall (A : Type) (f : A -> A) (n m : nat) (x : A),
    drop m (iterate f n x) =
    iterate f (n - m) (iter f (min n m) x).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite drop_nil. reflexivity.
    destruct m as [| m']; cbn.
      reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma head_drop :
  forall (A : Type) (n : nat) (l : list A),
    head (drop n l) = nth n l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; trivial.
Qed.
(* end hide *)

Lemma last_drop :
  forall (A : Type) (n : nat) (l : list A),
    last (drop n l) = if leb (S n) (length l) then last l else None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct l; reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      rewrite IHn'. destruct t; reflexivity.
Qed.
(* end hide *)

Lemma tail_drop :
  forall (A : Type) (n : nat) (l : list A),
    tail (drop n l) =
    if leb (S n) (length l) then Some (drop (S n) l) else None.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn.
    1-3: reflexivity.
    rewrite IHn'. destruct t; reflexivity.
Qed.
(* end hide *)

(* TODO: init_drop *)
(*Lemma init_drop :
  forall (A : Type) (n : nat) (l : list A),
    init (drop n l) =
    if leb (S n) (length l) then Some (drop (n - 1) l) else None.*)
(* begin hide *)
(*Proof.
Abort.*)
(* end hide *)

Lemma nth_drop :
  forall (A : Type) (n m : nat) (l : list A),
    nth m (drop n l) = nth (n + m) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn.
      apply nth_nil.
      apply IHn'.
Qed.
(* end hide *)

(* TODO: nowe *)
Lemma nth_spec :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> l = take n l ++ x :: drop (S n) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite nth_nil in H. inversion H.
    destruct n as [| n']; cbn in *.
      inversion H. reflexivity.
      rewrite (IHt _ _ H) at 1. reflexivity.
Qed.
(* end hide *)

(* TODO: drop_remove *)

Lemma drop_S_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    drop (S n) (insert l n x) = drop n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite <- (IHt n' x). cbn. reflexivity.
Qed.
(* end hide *)

(* TODO: insert_drop *)
Lemma insert_drop :
  forall (A : Type) (l : list A) (n m : nat) (x : A),
    insert (drop n l) m x =
    drop (n - 1) (insert l (n + m) x).
(* begin hide *)
Proof.
  intros A l n. revert l.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn.
Abort.
(* end hide *)

Lemma drop_drop :
  forall (A : Type) (n m : nat) (l : list A),
    drop m (drop n l) = drop (n + m) l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      rewrite drop_nil. reflexivity.
      apply IHn'.
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

(** *** Dualność [take] i [drop] *)

(* TODO: napisz coś *)

(* begin hide *)
Lemma take_rev_aux :
  forall (A : Type) (n : nat) (l : list A),
    take n l = rev (drop (length (rev l) - n) (rev l)).
Proof.
  induction n as [| n']; intros.
    rewrite <- minus_n_O. rewrite drop_length. cbn. reflexivity.
    induction l as [| h t]; cbn; auto.
      rewrite IHn'. rewrite length_app, plus_comm. cbn. rewrite drop_app_l.
        rewrite rev_app. cbn. reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma take_rev :
  forall (A : Type) (n : nat) (l : list A),
    take n (rev l) = rev (drop (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma rev_take :
  forall (A : Type) (n : nat) (l : list A),
    rev (take n l) = drop (length l - n) (rev l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_inv, length_rev. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma drop_rev_aux :
  forall (A : Type) (n : nat) (l : list A),
    drop n l = rev (take (length (rev l) - n) (rev l)).
Proof.
  (*TODO: drop_rev_aux using rewriting *)
  intros. rewrite take_rev_aux, ?rev_inv, length_rev.
Restart.
  induction n as [| n']; intros.
    rewrite <- minus_n_O, take_length, rev_inv. cbn. reflexivity.
    induction l as [| h t]; cbn; auto.
      rewrite IHn'. rewrite length_app, plus_comm. cbn. rewrite take_app_l.
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

Lemma rev_drop :
  forall (A : Type) (n : nat) (l : list A),
    drop n (rev l) = rev (take (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite drop_rev_aux, !rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma take_drop :
  forall (A : Type) (n m : nat) (l : list A),
    take m (drop n l) = drop n (take (n + m) l).
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    cbn. trivial.
    destruct l as [| h t]; cbn.
      rewrite take_nil. trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

Lemma drop_take :
  forall (A : Type) (n m : nat) (l : list A),
    drop m (take n l) = take (n - m) (drop m l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite drop_nil. reflexivity.
    destruct l as [| h t], m as [| m']; cbn.
      1,3: reflexivity.
      rewrite take_nil. reflexivity.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma app_take_drop :
  forall (A : Type) (n : nat) (l : list A),
    take n l ++ drop n l = l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma insert_take_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    insert l n x = take n l ++ x :: drop n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite take_nil, drop_nil. cbn. reflexivity.
    destruct n as [| n']; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

(* TODO: zip, unzip, zipWith, intersperse *)

Lemma remove_nth_take_drop :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    nth n l = Some x <->
    remove n l = Some (x, take n l ++ drop (S n) l).
(* begin hide *)
Proof.
  split; revert n x.
    induction l as [| h t]; cbn; intros.
      rewrite nth_nil in H. inversion H.
      destruct n as [| n']; cbn in *.
        inversion H; subst. reflexivity.
        rewrite (IHt _ _ H). reflexivity.
    induction l as [| h t]; cbn; intros.
      inversion H.
      destruct n as [| n'].
        inversion H; subst; clear H. cbn. reflexivity.
        cbn. apply IHt. destruct (remove n' t).
          destruct p. inversion H; subst; clear H.
            destruct t; cbn; reflexivity.
          inversion H.
Qed.
(* end hide *)

(** ** [splitAt] *)

(** Zdefiniuj przez rekursję funkcję [splitAt], która spełnia poniższą
    specyfikację. *)

(* begin hide *)
Fixpoint splitAt {A : Type} (n : nat) (l : list A) : list A * list A :=
match n with
    | 0 => ([], l)
    | S n' =>
        match l with
            | [] => ([], [])
            | h :: t =>
                let '(l1, l2) := splitAt n' t
                in (h :: l1, l2)
        end
end.
(* end hide *)

Lemma splitAt_spec :
  forall (A : Type) (n : nat) (l : list A),
    splitAt n l = (take n l, drop n l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

(** ** [zip] *)

(** Napisz funkcję [zip : forall A B : Type, list A -> list B -> list (A * B)],
    która spełnia poniższą specyfikację. Co robi ta funkcja? *)

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

Lemma zip_take :
  forall (A B : Type) (n : nat) (la : list A) (lb : list B),
    zip (take n la) (take n lb) = take n (zip la lb).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    trivial.
    destruct la, lb; cbn; trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

Lemma zip_drop :
  forall (A B : Type) (n : nat) (la : list A) (lb : list B),
    zip (drop n la) (drop n lb) = drop n (zip la lb).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    trivial.
    destruct la, lb; cbn; trivial.
      rewrite zip_nil_r. trivial.
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

(** ** [unzip] *)

(** Zdefiniuj funkcję [unzip], która jest w pewnym sensie "odwrotna"
    do [zip]. *)

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

(** ** [zipWith] *)

(** Zdefiniuj funkcję [zipWith], która spełnia poniższą specyfikację. *)

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

(** Zaimplementuj funkcję [unzipWith], która ma się tak do [zipWith], jak
    [unzip] do [zip]. *)

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

(** * Funkcje z predykatem boolowskim *)

(** ** [any] *)

(** TODO: napisz coś *)

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
        exists 0, h. cbn. split; [reflexivity | assumption].
        destruct (IHt H) as (n & x & H1 & H2).
          exists (S n), x. cbn. split; assumption.
    destruct 1 as (n & x & H1 & H2).
    generalize dependent l.
    induction n as [| n']; destruct l as [| h t]; cbn in *; intros.
      1-3: inversion H1; subst.
        cbn. rewrite H2. cbn. reflexivity.
      rewrite (IHn' _ H1). rewrite Bool.orb_comm. cbn. reflexivity.
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

Lemma any_take :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    any p (take n l) = true -> any p l = true.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    inversion 1.
    destruct l as [| h t]; cbn; intro.
      inversion H.
      destruct (p h) ; cbn in *.
        reflexivity.
        apply IHn'. assumption.
Qed.
(* end hide *)

Lemma any_take_conv :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    any p l = false -> any p (take n l) = false.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn in *.
      reflexivity.
      destruct (p h) ; cbn in *.
        assumption.
        apply IHn'. assumption.
Qed.
(* end hide *)

Lemma any_drop :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    any p (drop n l) = true -> any p l = true.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn in *.
      assumption.
      destruct (p h) ; cbn in *.
        reflexivity.
        apply IHn'. assumption.
Qed.
(* end hide *)

Lemma any_drop_conv :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    any p l = false -> any p (drop n l) = false.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn in *.
      reflexivity.
      destruct (p h) ; cbn in *.
        inversion H.
        apply IHn'. assumption.
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

(** TODO: napisz coś *)

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
    all p (replicate n x) = orb (leb n 0) (p x).
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

(* TODO: przenieść *)
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
          cbn in H0. omega.
          destruct (H 1 ltac:(omega)) as (x & H1 & H2); cbn in *.
            destruct n as [| n']; cbn in *.
              exists h'. inversion H1; subst. split; trivial.
              destruct (H (S (S n')) ltac:(omega)) as (x' & H1' & H2').
                cbn in H1'. exists x'. split; trivial.
        destruct (H 0 ltac:(omega)) as (x & H1 & H2); cbn in *.
          inversion H1; subst. congruence.
Qed.
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

Lemma all_take :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    all p (take n l) = false -> all p l = false.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    inversion 1.
    destruct l as [| h t]; cbn; intro.
      inversion H.
      destruct (p h) ; cbn in *.
        apply IHn'. assumption.
        reflexivity.
Qed.
(* end hide *)

Lemma all_take_conv :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    all p l = true -> all p (take n l) = true.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn in *.
      reflexivity.
      destruct (p h) ; cbn in *.
        apply IHn'. assumption.
        assumption.
Qed.
(* end hide *)

Lemma all_drop :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    all p (drop n l) = false -> all p l = false.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn in *.
      assumption.
      destruct (p h) ; cbn in *.
        apply IHn'. assumption.
        reflexivity.
Qed.
(* end hide *)

Lemma all_drop_conv :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    all p l = true -> all p (drop n l) = true.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn in *.
      reflexivity.
      destruct (p h) ; cbn in *.
        apply IHn'. assumption.
        inversion H.
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

(** Napisz funkcję [find], która znajduje pierwszy element na liście,
    który spełnia podany predykat boolowski. Podaj i udowodnij jej
    specyfikację.

    Napisz też funkcję [findLast], która znajduje ostatni element na
    liście, który spełnia podany predykat boolowski. *)

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

(* TODO: [iterate] od [removeFirst] wzwyż. *)
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
    destruct 1 as (n & x & H1 & H2). generalize dependent l.
      induction n as [| n']; destruct l as [| h t]; cbn in *;
      inversion 1; subst; clear H1.
        rewrite H2. inversion 1.
        destruct (p h).
          inversion 1.
          apply IHn'. assumption.
    induction l as [| h t]; cbn; intros.
      contradiction H. reflexivity.
      destruct (p h) eqn: Hph.
        exists 0, h. cbn. split; [reflexivity | assumption].
        destruct (IHt H) as (n & x & H1 & H2).
          exists (S n), x. cbn. split; assumption.
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
  forall (A : Type) (p : A -> bool) (n : nat) (x : A) (l : list A),
    find p (take n l) = Some x -> find p l = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H.
    destruct l as [| h t]; cbn in *; intros.
      inversion H.
      destruct (p h).
        assumption.
        apply IHn'. assumption.
Qed.
(* end hide *)

Lemma find_take_None :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    find p l = None -> find p (take n l) = None.
(* begin hide *)
Proof.
  intros A p n l. revert n.
  induction l as [| h t]; cbn; intros.
    rewrite take_nil. cbn. reflexivity.
    destruct (p h) eqn: Hph.
      inversion H.
      destruct n as [| n']; cbn.
        reflexivity.
        rewrite Hph. apply IHt, H.
Qed.
(* end hide *)
 
Lemma find_drop_not_None :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    find p (drop n l) <> None -> find p l <> None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn in *.
      contradiction H. reflexivity.
      destruct (p h) eqn: Hph.
        inversion 1.
        apply IHn'. assumption.
Qed.
(* end hide *)

Lemma find_drop_None :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    find p l = None -> find p (drop n l) = None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn.
      reflexivity.
      apply IHn'. cbn in H. destruct (p h); congruence.
Qed.
(* end hide *)

Lemma findLast_take :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    findLast p (take n l) <> None -> findLast p l <> None.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    contradiction H. reflexivity.
    destruct l as [| h t]; cbn in *.
      assumption.
      destruct (findLast p (take n' t)) eqn: Heq.
        specialize (IHn' _ ltac:(rewrite Heq; inversion 1)).
          destruct (findLast p t) eqn: Heq'.
            inversion 1.
            contradiction IHn'. reflexivity.
        destruct (findLast p t) eqn: Heq'.
          inversion 1.
          assumption.
Qed.
(* end hide *)

Lemma findLast_drop :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A) (l : list A),
    findLast p (drop n l) = Some x -> findLast p l = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn in *.
      inversion H.
      rewrite (IHn' _ _ H). reflexivity.
Qed.
(* end hide *)

(** ** [removeFirst] i [removeLast] *)

(** Napisz funkcje [removeFirst] i [removeLast] o sygnaturach
    [forall A : Type, (A -> bool) -> list A -> option (A * list A)],
    które zwracają pierwszy/ostatni element z listy spełniający
    predykat boolowski [p] oraz resztę listy bez tego elementu. *)

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
    intros H n. generalize dependent l.
    induction n as [| n']; destruct l as [| h t];
    inversion 2; subst; cbn in *.
      destruct (p x).
        inversion H.
        reflexivity.
      destruct (p h).
        inversion H.
        destruct (removeFirst p t) eqn: Heq.
          destruct p0. inversion H.
          apply (IHn' _ Heq _ H0).
    induction l as [| h t]; cbn; intros.
      reflexivity.
      destruct (p h) eqn: Hph.
        specialize (H 0 h eq_refl). congruence.
        rewrite IHt.
          reflexivity.
          intros. apply H with (S n). cbn. assumption.
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

(* begin hide *)
Ltac inv H := inversion H; subst; clear H.
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

(* TODO: removeFirst_zip *)

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

(** Napisz funkcję [findIndex], która znajduje indeks pierwszego elementu,
    który spełnia predykat boolowski [p]. *)

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
  induction l as [| h t]; cbn.
    inversion 1.
    case_eq (p h); intros.
      inversion H0; subst; clear H0; cbn. exists h. auto. 
      case_eq (findIndex p t); intros.
        rewrite H1 in H0. inversion H0; subst; clear H0.
          destruct (IHt _ H1). exists x. cbn. assumption.
        rewrite H1 in H0. inversion H0.
Restart.
  intros A p l. functional induction @findIndex A p l;
  intros; inversion H; subst; clear H; cbn in *.
    exists h. auto.
    destruct (IHo _ e1) as [x H]. exists x. assumption.
Qed.
(* end hide *)

Lemma findIndex_nth_conv :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A) (x : A),
    nth n l = Some x -> p x = true ->
      exists m : nat, findIndex p l = Some m /\ m <= n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct l as [| h t]; inversion H; subst; clear H.
      exists 0. cbn. rewrite H0. split; trivial.
    destruct l as [| h t].
      inversion H.
      destruct (IHn' _ _ H H0) as (m & H1 & H2). cbn. case_eq (p h); intros.
        exists 0. split; [reflexivity | apply le_0_n].
        exists (S m). rewrite H1. split.
          reflexivity.
          apply le_n_S, H2.
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
          specialize (H3 0 h ltac:(omega) eq_refl); cbn in H3. congruence.
        destruct t; inversion H1; subst; clear H1; cbn in *.
          congruence.
          destruct (p a) eqn: Hpa.
            destruct t; inversion H0; subst; cbn in *.
              reflexivity.
              specialize (H3 1 a ltac:(omega) eq_refl). congruence.
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
        destruct (findIndex p t).
          inv H. apply (IHt _ eq_refl _ (lt_S_n _ _ H0)).
          inv H.
Qed.
(* end hide *)

(** TODO: [findIndex] [init], [tail] *)

Lemma findIndex_take :
  forall (A : Type) (p : A -> bool) (n m : nat) (l : list A),
    findIndex p (take n l) = Some m ->
      findIndex p l = Some m /\ m <= n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H.
    destruct l as [| h t]; cbn in *.
      inversion H.
      destruct (p h).
        inversion H; subst; clear H. split; [reflexivity | apply le_0_n].
        case_eq (findIndex p (take n' t)); intros; rewrite H0 in *.
          destruct (IHn' _ _ H0). rewrite H1. inversion H; subst; clear H.
            split; try reflexivity. apply le_n_S. assumption.
          inversion H.
Qed.
(* end hide *)

Lemma findIndex_drop :
  forall (A : Type) (p : A -> bool) (n m : nat) (l : list A),
    findIndex p l = Some m -> n <= m ->
      findIndex p (drop n l) = Some (m - n).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite <- minus_n_O. assumption.
    destruct l as [| h t]; cbn in *.
      inversion H.
      destruct (p h).
        inversion H; subst; clear H. inversion H0.
        case_eq (findIndex p t); intros; rewrite H1 in *.
          inversion H; subst; clear H; cbn. apply IHn'.
            assumption.
            apply le_S_n. assumption.
          inversion H.
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
            rewrite H2. exists 0, (S nb). inv H. repeat split; omega.
          inv H.
      destruct (findIndex _ (zip ta tb)).
        destruct (IHl _ eq_refl) as (na & nb & H1 & H2 & H3 & H4).
          rewrite H1, H2. destruct (pb hb).
            exists (S na), 0. inv H. repeat split; omega.
            exists (S na), (S nb). inv H. repeat split; omega.
        inv H.
Qed.
(* end hide *)

(** ** [count] *)

(** Napisz funkcję [count], która liczy, ile jest na liście [l] elementów
    spełniających predykat boolowski [p]. *)

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
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    count p (take n l) <= n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    apply le_0_n.
    destruct l as [| h t]; cbn.
      apply le_0_n.
      destruct (p h).
        apply le_n_S, IHn'.
        apply le_S, IHn'.
Qed.
(* end hide *)

Lemma count_take' :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    count p (take n l) <= min n (count p l).
(* begin hide *)
Proof.
  intros A p n l. revert n.
  induction l as [| h t]; cbn; intros.
    rewrite take_nil, Nat.min_0_r. cbn. apply le_n.
    destruct n as [| n']; cbn.
      apply le_n.
      destruct (p h).
        apply le_n_S, IHt. apply le_trans with (min n' (count p t)).
          apply IHt.
          destruct (count p t).
            rewrite Nat.min_0_r. apply le_n.
            apply le_trans with (min (S n') (S n)).
              apply Nat.min_le_compat_r. apply le_S, le_n.
              cbn. reflexivity.
Qed.
(* end hide *)

Lemma count_drop :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    count p (drop n l) <= length l - n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite <- minus_n_O. apply count_length.
    destruct l as [| h t]; cbn.
      apply le_0_n.
      apply IHn'.
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

(** Napisz funkcję [filter], która zostawia na liście elementy, dla których
    funkcja [p] zwraca [true], a usuwa te, dla których zwraca [false]. *)

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

(* TODO: tail, init *)

Lemma filter_nth :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A) (x : A),
    nth n l = Some x -> p x = true ->
      exists m : nat, m <= n /\ nth m (filter p l) = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
  1-3: inversion H; subst; clear H.
    exists 0. rewrite H0. cbn. split; reflexivity.
    destruct (IHn' _ _ H H0) as (m & H1 & H2).
      destruct (p h).
        exists (S m). cbn. split.
          apply le_n_S. assumption.
          assumption.
        exists m. split.
          apply le_S, H1.
          assumption.
Qed.
(* end hide *)

Lemma filter_insert :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat) (x : A),
    filter p (insert l n x) =
      filter p (take n l) ++
      (if p x then [x] else []) ++
      filter p (drop n l).
(* begin hide *)
Proof.
  intros. rewrite insert_take_drop, filter_app. cbn.
  destruct (p x); reflexivity.
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
    all p l = isEmpty (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (p h); cbn; reflexivity.
Qed.
(* end hide *)

Lemma all_filter' :
  forall (A : Type) (p : A -> bool) (l : list A),
    all p (filter p l) = true.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h) eqn: Hph; cbn; rewrite ?Hph; cbn; assumption.
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

(** *** [partition] *)

(** Napisz funkcję [partition], która dzieli listę [l] na listy
    elementów spełniających i niespełniających pewnego warunku
    boolowskiego. *)

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

(** Napisz funkcję [findIndices], która znajduje indeksy wszystkich
    elementów listy, które spełniają predykat boolowski [p]. *)

(* begin hide *)
(*Definition findIndices {A : Type} (p : A -> bool) (l : list A) : list nat :=
  (fix f (l : list A) (n : nat) : list nat :=
  match l with
      | [] => []
      | h :: t => if p h then n :: f t (S n) else f t (S n)
  end) l 0.
*)

(* TODO *)
Fixpoint findIndices {A : Type} (p : A -> bool) (l : list A) : list nat :=  
match l with
    | [] => []
    | h :: t =>
        if p h
        then 0 :: map S (findIndices p t)
        else map S (findIndices p t)
end.

(* TODO:
Lemma findIndices'_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    map (plus 0) (findIndices' p l) = findIndices p l.
Proof.
  unfold findIndices. intros.
  remember 0 as n. clear Heqn. generalize dependent n.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h); cbn.
      rewrite plus_0_r. f_equal. rewrite <- IHt, map_map. f_equal.
        admit.
      rewrite <- IHt, map_map. f_equal. cbn. admit.
Admitted.
(* end hide *)
*)

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

(* TODO: [join], [bind] *)

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
          destruct p0. inversion IHt.
          rewrite Heq. reflexivity.
        destruct (init l), (removeLast p t); cbn.
          destruct p0. cbn. rewrite Hph. inversion IHt; subst. cbn.
            reflexivity.
          inversion IHt.
          destruct p0. cbn. rewrite Hph. inversion IHt; subst; cbn.
            reflexivity.
          inversion IHt.
      rewrite init_map. destruct (findIndices p t) eqn: Heq; cbn in *.
        destruct (removeLast p t).
          destruct p0. inversion IHt.
          reflexivity.
        destruct (init l), (removeLast p t); cbn.
          destruct p0. cbn. rewrite Hph. inversion IHt; subst; cbn.
            reflexivity.
          inversion IHt.
          destruct p0. cbn. rewrite Hph. inversion IHt; subst; cbn.
            reflexivity.
          inversion IHt.
Restart.
  intros. pose (init_rev _ (rev (findIndices p l))).
  rewrite rev_inv in e.
  pose (removeLast_rev _ p (rev l)). rewrite rev_inv in e0.
  rewrite e, e0. rewrite rev_findIndices. rewrite tail_map.
  rewrite findIndices_rev.
Admitted.
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
    rewrite take_nil, drop_nil, app_nil_r. cbn. reflexivity.
    destruct n as [| n']; cbn.
      destruct (p x), (p h); reflexivity.
      rewrite ?IHt, ?map_app, map_map.
        destruct (p h), (p x); reflexivity.
Qed.
(* end hide *)

(* TODO: takeWhile, dropWhile *)

Lemma findIndices_take :
  forall (A : Type) (p : A -> bool) (n : nat) (l : list A),
    findIndices p (take n l) =
    take (count p (take n l)) (findIndices p l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    destruct l as [| h t]; cbn.
      reflexivity.
      destruct (p h); cbn; rewrite IHn', take_map; reflexivity.
Qed.
(* end hide *)

(** ** [takeWhile] i [dropWhile] *)

(** Zdefiniuj funkcje [takeWhile] oraz [dropWhile], które, dopóki
    funkcja [p] zwraca [true], odpowiednio biorą lub usuwają elementy
    z listy. *)

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
      takeWhile p (snoc x l) =
      if p x then snoc x l else l.
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
(* TODO *)
Lemma dropWhile_snoc_all :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all (fun x : A => negb (p x)) l = true ->
      dropWhile p (snoc x l) = snoc x l.
Proof.
  induction l as [| h t]; cbn; intros.
    inversion H.
Abort.
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

(* TODO *)
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

(** *** [span] *)

(** Zdefiniuj rekurencyjną funkcję [span], która spełnia poniższą
    specyfikację. *)

(* begin hide *)
Fixpoint span
  {A : Type} (p : A -> bool) (l : list A) : list A * list A :=
match l with
    | [] => ([], [])
    | h :: t =>
        let
          '(l1, l2) := span p t
        in
          if p h
          then (h :: l1, l2)
          else ([], h :: t)
end.
(* end hide *)

Lemma span_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    span p l = (takeWhile p l, dropWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct (p h); reflexivity.
Qed.
(* end hide *)

(** * Sekcja mocno ad hoc *)

(** ** [pmap] *)

(** TODO: napisz coś *)

(* TODO: iterate, nth, last, tail i init, take i drop, takedrop, zip,
         unzip, zipWith, unzipWith, removeFirst i removeLast, findIndex,
         findIndices
*)

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

(* TODO: iterate *)

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

(* TODO: tail, last, init *)

Lemma pmap_zip :
  forall
    (A B C : Type)
    (fa : A -> option C) (fb : B -> option C)
    (la : list A) (lb : list B),
      pmap
        (fun '(a, b) =>
        match fa a, fb b with
            | Some a', Some b' => Some (a', b')
            | _, _ => None
        end)
        (zip la lb) =
      zip (pmap fa la) (pmap fb lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    reflexivity.
    destruct lb as [| hb tb]; cbn.
      destruct (fa ha); cbn.
        reflexivity.
        rewrite zip_nil_r. reflexivity.
      destruct (fa ha) eqn: Ha; cbn.
        destruct (fb hb) eqn: Hb; cbn.
          rewrite IHta. reflexivity.
          rewrite IHta. destruct (pmap fb tb); cbn.
            rewrite zip_nil_r. reflexivity.
            destruct ta; cbn.
Admitted.
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

Definition aux {A B : Type} (p : B -> bool) (f : A -> option B)
  (dflt : bool) (x : A) : bool :=
match f x with
    | Some b => p b
    | None => dflt
end.

(* TODO *) Lemma pmap_filter :
  forall (A B : Type) (p : B -> bool) (f : A -> option B) (l : list A),
    filter p (pmap f l) =
    pmap f (filter (aux p f false) l).
(*      (filter
        (fun x : A => match f x with | Some b => p b | _ => false end)
        l).*)
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


(** * Bardziej skomplikowane funkcje *)

(** TODO: napisz wstęp *)

(** ** [intersperse] *)

(** Napisz funkcję [intersperse], który wstawia element [x : A] między
    każde dwa elementy z listy [l : list A]. *)

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
        | Some (h :: t) => Some (x :: intersperse x t)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct t; cbn in *.
      reflexivity.
      destruct (intersperse x t).
Abort.
(* end hide *)

(* TODO: init *)

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
        rewrite nth_nil. destruct t; cbn in *.
          rewrite nth_nil. reflexivity.
          apply lt_S_n in H. specialize (IHt _ H).
            rewrite nth_nil in IHt. destruct n'; cbn in *; inversion IHt.
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

(* TODO: insert, remove *)

Lemma take_intersperse :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    1 < n -> 1 < length l ->
      take (2 * n) (intersperse x l) =
      intersperse x (take n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite ?take_nil. cbn. reflexivity.
    destruct (intersperse x t).
      destruct n as [| [| n']]; cbn.
        1-2: reflexivity.
        destruct t; cbn.
          reflexivity.
          destruct t; cbn in *.
Abort.
(* end hide *)

(* TODO drop, zip, unzip, zipWith *)

Lemma any_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    any p (intersperse x l) =
    orb (any p l) (andb (leb 2 (length l)) (p x)).
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
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (any p t); reflexivity.
          destruct t; cbn in *.
            inv Heq'.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (any p t); reflexivity.
Qed.
(* end hide *)

Lemma all_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all p (intersperse x l) =
    andb (all p l) (orb (leb (length l) 1) (p x)).
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn in *.
    reflexivity.
    destruct t; cbn in *.
      rewrite ?Bool.andb_true_r. reflexivity.
      rewrite e0 in *. cbn in *. destruct t; cbn in *.
        inversion e0.
        rewrite (IHl0 p). rewrite Bool.andb_assoc. reflexivity.
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
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (all p t); reflexivity.
          destruct t; cbn in *.
            inv Heq'.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (all p t); reflexivity.
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
              inversion IHt; cbn. f_equal. omega.
              inversion IHt.
            rewrite Hpa in *.
              destruct (findIndex p t); inversion IHt.
                f_equal. omega.
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
    destruct (p h), (p x), t; cbn; try reflexivity.
      admit.
      admit.
      admit.
      admit.
    rewrite e0 in IHl0. cbn in *. specialize (IHl0 p).
    destruct (p h), (p x), (p h') eqn: Hph';
    cbn in *; rewrite IHl0; try omega.
Abort.
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
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (intersperse x t); cbn.
      rewrite <- (IHt H). cbn. reflexivity.
      rewrite H, <- (IHt H). destruct (f h); cbn; destruct (f a); reflexivity.
Qed.
(* end hide *)

(** ** [groupBy] *)

(** TODO *)

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
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> exists x : A, nth n l = Some x /\ elem x l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
    inversion H.
    exists h. split; [trivial | constructor].
    inversion H.
    apply lt_S_n in H. destruct (IHn' _ H) as [x [Hx1 Hx2]].
      exists x. split; try constructor; assumption.
Qed.
(* end hide *)

Lemma nth_elem_conv :
  forall (A : Type) (x : A) (l : list A),
    elem x l -> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; inversion 1; subst.
    exists 0. cbn. trivial.
    destruct (IHt H2) as [n Hn]. exists (S n). cbn. assumption.
Qed.
(* end hide *)

Lemma nth_elem_Some :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    nth n l = Some x -> elem x l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn.
    1-3: inversion 1; subst; clear H. constructor.
    intro. right. apply IHn', H.
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
    destruct n as [| n']; cbn in *.
      inversion H; subst; clear H.
        contradiction H0. reflexivity.
        assumption.
      inversion H; subst; clear H.
        destruct (remove n' t).
          destruct p. left.
          trivial.
        specialize (IHt _ H3 H0). destruct (remove n' t).
          destruct p. right. assumption.
          trivial.
Qed.
(* end hide *)

Lemma elem_take :
  forall (A : Type) (n : nat) (l : list A) (x : A),
    elem x (take n l) -> elem x l.
(* begin hide *)
Proof.
  induction n as [| n'].
    cbn. inversion 1.
    destruct l as [| h t]; cbn.
      inversion 1.
      intros. inversion H; subst; constructor. apply IHn'. assumption.
Qed.
(* end hide *)

Lemma elem_drop :
  forall (A : Type) (n : nat) (l : list A) (x : A),
    elem x (drop n l) -> elem x l.
(* begin hide *)
Proof.
  induction n as [| n'].
    cbn. trivial.
    destruct l as [| h t]; cbn.
      inversion 1.
      intros. constructor. apply IHn'. assumption.
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
    elem x l -> elem x (takeWhile p l) \/ elem x (dropWhile p l).
(* begin hide *)
Proof.
  intros. apply elem_app. rewrite takeWhile_dropWhile_spec. assumption.
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
              right. split; trivial. omega.
            destruct (IHt H3).
              left. right. assumption.
              destruct H0. right. split; [assumption | omega].
    destruct 1.
      induction H; cbn.
        destruct (intersperse y l); left.
        destruct (intersperse y t).
          inversion IHelem.
          do 2 right. assumption.
      destruct H; subst. destruct l as [| h [| h' t]]; cbn.
        1-2: cbn in H0; omega.
        destruct (intersperse y t); cbn.
          right. left.
          right. left.
Qed.
(* end hide *)

(** ** [In] *)

(** Gratuluję, udało ci się zdefiniować predykat [elem] i dowieść wszystkich
    jego właściwości. To jednak nie koniec zabawy, gdyż predykaty możemy
    definiować nie tylko przez indukcję, ale także przez rekursję. Być może
    taki sposób definiowania jest nawet lepszy? Przyjrzyjmy się poniższej
    definicji — tak właśnie "bycie elementem" jest zdefiniowane w bibliotece
    standardowej. *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
match l with
    | [] => False
    | h :: t => x = h \/ In x t
end.

(** Powyższa definicja jest bardzo podobna do tej induktywnej. [In x]
    dla listy pustej redukuje się do [False], co oznacza, że w pustej
    liście nic nie ma, zaś dla listy mającej głowę i ogon redukuje się do
    zdania "[x] jest głową lub jest elementem ogona".

    Definicja taka ma swoje wady i zalety. Największą moim zdaniem wadą jest
    to, że nie możemy robić indukcji po dowodzie, gdyż dowód faktu [In x l]
    nie jest induktywny. Największą zaletą zaś jest fakt, że nie możemy robić
    indukcji po dowodzie — im mniej potencjalnych rzeczy, po których można
    robić indukcję, tym mniej zastanawiania się. Przekonajmy się zatem na
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

Lemma nth_In :
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> exists x : A, nth n l = Some x /\ In x l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
    inversion H.
    exists h. split; repeat constructor.
    inversion H.
    apply lt_S_n in H. destruct (IHn' _ H) as [x [Hx1 Hx2]].
      exists x. split; try constructor; assumption.
Qed.
(* end hide *)

Lemma nth_In_conv :
  forall (A : Type) (x : A) (l : list A),
    In x l -> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; inversion 1; subst.
    exists 0. cbn. trivial.
    destruct (IHt H0) as [n Hn]. exists (S n). cbn. assumption.
Qed.
(* end hide *)

Lemma nth_In_Some :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    nth n l = Some x -> In x l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn.
    1-3: inversion 1; subst; clear H. left. reflexivity.
    intro. right. apply IHn', H.
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
  forall (A : Type) (n : nat) (l : list A) (x : A),
    In x (take n l) -> In x l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    contradiction.
    destruct l as [| h t]; cbn in *.
      assumption.
      destruct H; subst; [left | right].
        reflexivity.
        apply IHn', H.
Qed.
(* end hide *)

Lemma In_drop :
  forall (A : Type) (n : nat) (l : list A) (x : A),
    In x (drop n l) -> In x l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn.
      inversion H.
      right. apply IHn'. assumption.
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

(** ** [NoDup] *)

(** Zdefiniuj induktywny predykat [NoDup]. Zdanie [NoDup l] jest prawdziwe,
    gdy w [l] nie ma powtarzających się elementów. Udowodnij, że zdefiniowall
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
  forall (A : Type) (n : nat) (l : list A),
    NoDup l -> NoDup (take n l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    constructor.
    inversion H; subst; clear H; constructor.
      intro. apply H0. apply elem_take with n'. assumption.
      apply IHn'. assumption.
Qed.
(* end hide *)

Lemma NoDup_drop :
  forall (A : Type) (n : nat) (l : list A),
    NoDup l -> NoDup (drop n l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    inversion H; subst; clear H.
      constructor.
      apply IHn', H1.
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
  forall (A B : Type) (la : list A) (lb : list B),
    NoDup (zip la lb) -> NoDup la \/ NoDup lb.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    left. constructor.
    destruct lb as [| hb tb]; cbn.
      right. constructor.
      inversion H; subst; clear H. destruct (IHta _ H3).
Abort.
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
Abort.
(* end hide *)

(** ** [Dup] *)

(** Powodem problemów z predykatem [NoDup] jest fakt, że jest on w pewnym
    sensie niekonstruktywny. Wynika to wprost z jego definicji: [NoDup l]
    zachodzi, gdy w [l] nie ma duplikatów. Parafrazując: [NoDup l] zachodzi,
    gdy _nieprawda_, że w [l] są duplikaty.

    Jak widać, w naszej definicji implicité występuje negacja. Wobec tego
    jeżeli spróbujemy za pomocą [NoDup] wyrazić zdanie "na liście [l] są
    duplikaty", to tak naprawdę dostaniemy zdanie "nieprawda, że nieprawda,
    że [l] ma duplikaty".

    Dostaliśmy więc po głowie nagłym atakiem podwójnej negacji. Nie ma się
    co dziwić w takiej sytuacji, że nasza "negatywna" definicja predykatu
    [NoDup] jest nazbyt klasyczna. Możemy jednak uratować sytuację, jeżeli
    zdefiniujemy predykat [Dup] i zanegujemy go. [Dup l] jest spełniony,
    gdy lista [l] ma duplikaty. *)

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
        omega.
        rewrite nth_app_r.
          rewrite <- minus_n_n. cbn. reflexivity.
          apply le_n.
        rewrite nth_app_r.
          rewrite <- app_cons_l, nth_app_r.
            replace (nth _ (x :: l3)) with (nth 0 (x :: l3)).
              cbn. reflexivity.
              f_equal. 1-3: simpl; omega.
    destruct 1 as (x & n1 & n2 & H1 & H2 & H3).
    generalize dependent n2. generalize dependent l.
    induction n1 as [| n1']; cbn; intros.
      destruct l as [| h t]; cbn in *; inversion H2; subst; clear H2.
        destruct n2 as [| n2']; cbn in *.
          omega.
          apply nth_elem_Some in H3. left. assumption.
      destruct l as [| h t], n2 as [| n2']; cbn in *;
      inversion H3; subst; clear H3.
        omega.
        right. apply lt_S_n in H1. apply (IHn1' t H2 n2' H1 H0).
Qed.
(* end hide *)

Lemma Dup_take :
  forall (A : Type) (n : nat) (l : list A),
    Dup (take n l) -> Dup l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H.
    destruct l as [| h t]; cbn.
      assumption.
      inversion H; subst; clear H.
        left. apply elem_take in H1. assumption.
        right. apply IHn'. assumption.
Qed.
(* end hide *)

Lemma Dup_drop :
  forall (A : Type) (n : nat) (l : list A),
    Dup (drop n l) -> Dup l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn in *.
      assumption.
      right. apply IHn', H.
Qed.
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

(** Jeżeli zastanowimy się chwilę, to dojdziemy do wniosku, że [Dup l]
    znaczy "istnieje x, który występuje na liście l co najmniej dwa
    razy". Widać więc, że [Dup] jest jedynie specjalnym przypadkiem
    pewngo bardziej ogólnego predykatu [Rep x n] dla dowolnego [x] oraz
    n = 2. Zdefiniuj relację [Rep]. Zdanie [Rep x n l] zachodzi, gdy
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
    Rep x n l -> x <> y -> Rep x n (snoc y l).
(* begin hide *)
Proof.
  induction 1; cbn; intro; constructor.
    1-2: apply IHRep, H0.
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

(* TODO *)
(*Lemma Rep_join :
  forall (A : Type) (x : A) (n : nat) (ll : list A),
    Rep x n (join ll) <->
      exists *)

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

(* TODO *)
(*Lemma Rep_nth :
  forall (A : Type) (n : nat)
*)

Lemma Rep_take :
  forall (A : Type) (x : A) (n m : nat) (l : list A),
    Rep x n (take m l) -> Rep x n l.
(* begin hide *)
Proof.
  intros A x n m. generalize dependent n.
  induction m as [| m']; cbn; intros.
    destruct n as [| n'].
      constructor.
      inversion H.
    destruct l as [| h t].
      assumption.
      destruct n as [| n'].
        constructor.
        inversion H; subst; clear H.
          constructor. apply IHm', H2.
          constructor. apply IHm'. assumption.
Qed.
(* end hide *)

Lemma Rep_drop :
  forall (A : Type) (x : A) (n m : nat) (l : list A),
    Rep x n (drop m l) -> Rep x n l.
(* begin hide *)
Proof.
  intros A x n m. generalize dependent n.
  induction m as [| m']; cbn; intros.
    assumption.
    destruct l as [| h t].
      assumption.
      constructor. apply IHm', H.
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
    Exists P l -> exists (n : nat) (x : A),
      nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  induction 1; cbn.
    exists 0, h. cbn. split; trivial.
    destruct IHExists as [n [x [H1 H2]]].
      exists (S n), x. cbn. split; assumption.
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
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exists P (take n l) -> Exists P l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H.
    destruct l as [| h t]; cbn; inversion H; subst; clear H.
      left. assumption.
      right. apply IHn', H1.
Qed.
(* end hide *)

Lemma Exists_drop :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exists P (drop n l) -> Exists P l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t].
      assumption.
      right. apply IHn', H.
Qed.
(* end hide *)

Lemma Exists_take_drop :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Exists P l -> Exists P (take n l) \/ Exists P (drop n l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    right. assumption.
    destruct l as [| h t]; inversion H; subst; clear H.
      left; left. assumption.
      destruct (IHn' _ H1).
        left; right. assumption.
        right. assumption.
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
    | Forall_nil : Forall P []
    | Forall_cons :
        forall (h : A) (t : list A), P h -> Forall P t -> Forall P (h :: t).
(* end hide *)

Lemma Forall_cons' :
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
      apply Nat.nlt_0_r in H. contradiction.
      destruct n as [| n']; cbn.
        exists h. split; trivial.
        apply IHForall. apply lt_S_n. assumption.
    induction l as [| h t]; cbn; intros.
      constructor.
      destruct (H 0 (Nat.lt_0_succ _)) as [x [H1 H2]]; cbn in *.
        inversion H1; subst; clear H1. constructor.
          assumption.
          apply IHt. intros. apply (H (S n)). apply lt_n_S. assumption.
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
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Forall P l -> Forall P (take n l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    constructor.
    destruct l as [| h t]; cbn.
      constructor.
      inversion H; subst; clear H. constructor.
        assumption.
        apply IHn'. assumption.
Qed.
(* end hide *)

Lemma Forall_drop :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Forall P l -> Forall P (drop n l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn.
      constructor.
      inversion H; subst; clear H. apply IHn', H3.
Qed.
(* end hide *)

Lemma Forall_take_drop :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    Forall P (take n l) -> Forall P (drop n l) -> Forall P l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t]; cbn.
      constructor.
      inversion H; subst; clear H. constructor.
        assumption.
        apply IHn'; assumption.
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
            omega.
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
  rewrite Forall_cons' in H0; destruct H0; contradiction.
Qed.
(* end hide *)

(** ** [AtLeast] *)

(** Czas uogólnić relację [Rep] oraz predykaty [Exists] i [Forall]. Zdefiniuj
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
        apply AtLeast_length in H2. omega.
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

(** TODO: [AtLeast] i [nth], [head], [last], [init], [tail]. *)

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
  forall (A : Type) (P : A -> Prop) (n m : nat) (l : list A),
    AtLeast P m (take n l) -> AtLeast P m l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H. constructor.
    destruct l as [| h t].
      assumption.
      inversion H; subst; clear H; constructor; auto.
Qed.
(* end hide *)

Lemma AtLeast_drop :
  forall (A : Type) (P : A -> Prop) (n m : nat) (l : list A),
    AtLeast P m (drop n l) -> AtLeast P m l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    assumption.
    destruct l as [| h t].
      assumption.
      constructor. apply IHn', H.
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
  induction l as [| h t]; cbn; intros.
    inversion H0. apply le_n.
    destruct (p h) eqn: Hph.
Restart.
  induction 2.
    apply le_0_n.
    cbn.
Abort.
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

(** TODO: [Exactly_join] *)

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
      apply Exactly_length in H4. rewrite length_replicate in H4. omega.
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

(** TODO: [Exactly_nth], [head], [tail], [init], [last] *)

Lemma Exactly_take :
  forall (A : Type) (P : A -> Prop) (n m1 m2 : nat) (l : list A),
    Exactly P m1 (take n l) -> Exactly P m2 l -> m1 <= m2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    inversion H. apply le_0_n.
    destruct l as [| h t].
      inversion H. apply le_0_n.
      inversion H; inversion H0; subst; clear H H0.
        apply le_n_S, (IHn' _ _ _ H5 H10).
        contradiction.
        contradiction.
        apply (IHn' _ _ _ H5 H10).
Qed.
(* end hide *)

Lemma Exactly_drop :
  forall (A : Type) (P : A -> Prop) (n m1 m2 : nat) (l : list A),
    Exactly P m1 (drop n l) -> Exactly P m2 l -> m1 <= m2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    replace m2 with m1.
      apply le_n.
      apply (Exactly_eq _ _ _ _ _ H H0).
    destruct l as [| h t].
      inv H; inv H0. apply le_n.
      inv H0.
        apply le_S, (IHn' _ _ _ H H5).
        apply (IHn' _ _ _ H H5).
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

(** TODO: [Exactly_zip] *)

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

(** ** [AtMost] (TODO) *)

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

Lemma AtMost_NoDup :
  forall (A : Type) (l : list A),
    (forall x : A, AtMost (fun y : A => x = y) 1 l) <-> NoDup l.
(* begin hide *)
Proof.
  split.
    Focus 2.
      induction 1; intros.
        constructor.
Abort.
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

(** ** Zawieranie *)

Definition incl {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 -> elem x l2.

(** Przyjrzyjmy się powyższej definicji. Intuicyjnie można ją rozumieć tak,
    że [incl l1 l2] zachodzi, gdy każdy element listy [l1] choć raz występuje
    też na liście [l2]. Udowodnij, że relacja ta ma poniższe właściwości. *)

Lemma incl_nil :
  forall (A : Type) (l : list A), incl [] l.
(* begin hide *)
Proof.
  unfold incl; intros. inversion H.
Qed.
(* end hide *)

Lemma incl_nil_conv :
  forall (A : Type) (l : list A),
    incl l [] -> l = [].
(* begin hide *)
Proof.
  unfold incl; intros. destruct l as [| h t].
    reflexivity.
    specialize (H h ltac:(left)). inversion H.
Qed.
(* end hide *)

Lemma incl_cons :
  forall (A : Type) (h : A) (t1 t2 : list A),
    incl t1 t2 -> incl (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  unfold incl; intros.
  inversion H0; subst; clear H0.
    left.
    right. apply H, H3.
Qed.
(* end hide *)

Lemma incl_cons' :
  forall (A : Type) (h : A) (t : list A),
    incl t (h :: t).
(* begin hide *)
Proof.
  inversion 1; subst.
    right. left.
    do 2 right. assumption.
Qed.
(* end hide *)

Lemma incl_cons'' :
  forall (A : Type) (h : A) (t l : list A),
    incl l t -> incl l (h :: t).
(* begin hide *)
Proof.
  unfold incl; intros. right. apply H, H0.
Qed.
(* end hide *)

Lemma incl_refl :
  forall (A : Type) (l : list A), incl l l.
(* begin hide *)
Proof.
  unfold incl. trivial.
Qed.
(* end hide *)

Lemma incl_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    incl l1 l2 -> incl l2 l3 -> incl l1 l3.
(* begin hide *)
Proof.
  unfold incl; intros. apply H0, H, H1.
Qed.
(* end hide *)

Lemma incl_snoc :
  forall (A : Type) (x : A) (l : list A),
    incl l (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply incl_nil.
    apply incl_cons. assumption.
Qed.
(* end hide *)

Lemma incl_singl_snoc :
  forall (A : Type) (x : A) (l : list A),
    incl [x] (snoc x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply incl_refl.
    apply incl_cons''. assumption.
Qed.
(* end hide *)

Lemma incl_snoc_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    incl l1 l2 -> incl (snoc x l1) (snoc x l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    apply incl_singl_snoc.
    unfold incl in *. intros x' H'. inversion H'; subst.
      rewrite elem_snoc. left. apply H. left.
      apply IHt.
        intros. apply H. right. assumption.
        assumption.
Qed.
(* end hide *)

Lemma incl_app_l :
  forall (A : Type) (l l1 l2 : list A),
    incl l l1 -> incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_app_l, H, H0.
Qed.
(* end hide *)

Lemma incl_app_r :
  forall (A : Type) (l l1 l2 : list A),
    incl l l2 -> incl l (l1 ++ l2).
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_app_r, H, H0.
Qed.
(* end hide *)

Lemma incl_app_l_conv :
  forall (A : Type) (l1 l2 : list A),
    incl (l1 ++ l2) l1 -> incl l2 l1.
(* begin hide *)
Proof.
  unfold incl; intros. apply H, elem_app_r, H0.
Qed.
(* end hide *)

Lemma incl_app_r_conv :
  forall (A : Type) (l1 l2 : list A),
    incl (l1 ++ l2) l2 -> incl l1 l2.
(* begin hide *)
Proof.
  unfold incl; intros. apply H, elem_app_l, H0.
Qed.
(* end hide *)

Lemma incl_app_sym :
  forall (A : Type) (l1 l2 l : list A),
    incl (l1 ++ l2) l -> incl (l2 ++ l1) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply H. rewrite elem_app in *.
  destruct H0; [right | left]; assumption.
Qed.
(* end hide *)

Lemma incl_rev :
  forall (A : Type) (l : list A), incl (rev l) l.
(* begin hide *)
Proof.
  unfold incl; intros. rewrite <- elem_rev. assumption.
Qed.
(* end hide *)

Lemma incl_map :
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    incl l1 l2 -> incl (map f l1) (map f l2).
(* begin hide *)
Proof.
  unfold incl; intros. rewrite elem_map_conv in *.
  destruct H0 as [x' [H1 H2]]. exists x'. split.
    assumption.
    apply H, H2.
Qed.
(* end hide *)

Lemma incl_join :
  forall (A : Type) (ll : list (list A)) (l : list A),
    elem l ll -> incl l (join ll).
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_join. exists l. split; assumption.
Qed.
(* end hide *)

Lemma incl_replicate :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    elem x l -> incl (replicate n x) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_replicate in H0.
  destruct H0. subst. assumption.
Qed.
(* end hide *)

Lemma incl_replicate' :
  forall (A : Type) (n m : nat) (x : A),
    n <> 0 -> incl (replicate m x) (replicate n x).
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_replicate in H0.
  destruct H0. subst. apply elem_replicate. split; trivial.
Qed.
(* end hide *)

Lemma incl_nth :
  forall (A : Type) (l1 l2 : list A),
    incl l1 l2 <->
    forall (n1 : nat) (x : A), nth n1 l1 = Some x ->
      exists n2 : nat, nth n2 l2 = Some x.
(* begin hide *)
Proof.
  unfold incl; split; intros.
    apply nth_elem_Some in H0. specialize (H _ H0). induction H.
      exists 0. cbn. reflexivity.
      destruct (IHelem H0) as [n2 IH]. exists (S n2). cbn. assumption.
    apply nth_elem_conv in H0. destruct H0 as [n Hn].
      destruct (H _ _ Hn) as [n2 Hn2]. apply nth_elem_Some in Hn2. assumption.
Qed.
(* end hide *)

Lemma incl_remove :
  forall (A : Type) (l : list A) (n : nat),
    match remove n l with
        | None => True
        | Some (_, l') => incl l' l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    destruct n as [| n'].
      apply incl_cons'.
      specialize (IHt n'). destruct (remove n' t).
        destruct p. apply incl_cons, IHt.
        trivial.
Qed.
(* end hide *)

Lemma incl_take :
  forall (A : Type) (n : nat) (l : list A),
    incl (take n l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_take in H. assumption.
Qed.
(* end hide *)

Lemma incl_drop :
  forall (A : Type) (n : nat) (l : list A),
    incl (drop n l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_drop in H. assumption.
Qed.
(* end hide *)

Lemma incl_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl (filter p l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_filter in H. destruct H. assumption.
Qed.
(* end hide *)

Lemma incl_filter_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl l (filter p l) <-> filter p l = l.
(* begin hide *)
Proof.
  unfold incl. split.
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

Lemma incl_takeWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl (takeWhile p l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_takeWhile in H. destruct H. assumption.
Qed.
(* end hide *)

Lemma incl_dropWhile :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl (dropWhile p l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_dropWhile in H. assumption.
Qed.
(* end hide *)

Lemma incl_takeWhile_conv :
  forall (A : Type) (p : A -> bool) (l : list A),
    incl l (takeWhile p l) <-> takeWhile p l = l.
(* begin hide *)
Proof.
  unfold incl. split.
    Focus 2. intros -> *. trivial.
    induction l as [| h t]; cbn; intros.
      reflexivity.
      case_eq (p h); intros; rewrite H0 in *.
        Focus 2. specialize (H h ltac:(left)). inversion H.
        rewrite IHt.
          reflexivity.
          induction 1; cbn in *.
            case_eq (p x); intros; rewrite H1 in *.
              left.
              specialize (H x ltac:(right; left)). inversion H; subst; clear H.
                congruence.
                assumption.
            case_eq (p h0); intros; rewrite ?H2 in *.
              Focus 2. specialize (H h0 ltac:(right; left)).
                inversion H; subst; clear H.
                  congruence.
                  inversion H5.
Abort.
(* end hide *)

Lemma incl_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    incl (map Some (pmap f l)) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply incl_refl.
    destruct (f h); cbn; rewrite ?IHt.
      apply incl_cons. assumption.
      apply incl_cons''. assumption.
Qed.
(* end hide *)

Lemma incl_intersperse :
  forall (A : Type) (x : A) (l1 l2 : list A),
    incl l1 (intersperse x l2) -> incl l1 (x :: l2).
(* begin hide *)
Proof.
  unfold incl; intros.
  specialize (H _ H0). rewrite elem_intersperse in H.
  decompose [and or] H; subst; [right | left]; assumption.
Qed.
(* end hide *)

Lemma incl_intersperse_conv :
  forall (A : Type) (x : A) (l1 l2 : list A),
    2 <= length l2 -> incl l1 (x :: l2) -> incl l1 (intersperse x l2).
(* begin hide *)
Proof.
  unfold incl; intros.
  specialize (H0 _ H1). rewrite elem_intersperse.
  inversion H0; subst; firstorder.
Qed.
(* end hide *)

(** ** Podlisty jako podtermy (TODO) *)

(** TODO: napisz coś *)

(* begin hide *)
Inductive sublist {A : Type} : list A -> list A -> Prop :=
    | sublist_direct :
        forall (h : A) (t : list A), sublist t (h :: t)
    | sublist_trans :
        forall l1 l2 l3 : list A,
          sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
(* end hide *)

Lemma sublist_nil_l :
  forall (A : Type) (l : list A),
    l <> nil -> sublist nil l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intro.
    contradiction H. reflexivity.
    destruct t as [| h' t'].
      constructor.
      apply sublist_trans with (h' :: t').
        apply IHt. inversion 1.
        constructor.
Qed.
(* end hide *)

(** ** Palindromy (TODO) *)

(** Palindrom to słowo, które czyta się tak samo od przodu jak i od tyłu.

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

(* Palindromowa indukcja *)
Lemma list_palindrome_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall x : A, P [x]) ->
    (forall (x y : A) (l : list A), P l -> P (x :: l ++ [y])) ->
      forall l : list A, P l.
Proof.
  fix 6. destruct l as [| h t].
    assumption.
    destruct (init_decomposition A t); subst.
      apply H0.
      destruct H2 as (h' & t' & H1' & H2' & H3'). rewrite H3'.
        apply H1. apply list_palindrome_ind; assumption.
Admitted.
(* end hide *)

Lemma Palindrome_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (x :: snoc x l).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply (Palindrome_1 x []). constructor.
    apply (Palindrome_1 x [x0]). constructor.
    rewrite snoc_app. cbn. rewrite snoc_app_singl in *.
      inversion IHPalindrome; subst.
        apply (f_equal isEmpty) in H2. rewrite isEmpty_app in H2.
          cbn in H2. rewrite Bool.andb_false_r in H2. congruence.
        replace (x :: x0 :: l ++ [x0; x]) with
                (x :: (x0 :: l ++ [x0]) ++ [x]).
          apply app_inv_r in H2. subst. do 2 constructor. assumption.
          cbn. rewrite <- app_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Palindrome_rev :
  forall (A : Type) (l : list A),
    Palindrome l <-> Palindrome (rev l).
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      constructor.
      constructor.
      rewrite rev_app. cbn. constructor. assumption.
    remember (rev l) as l'. intro. generalize dependent l.
    induction H; intros; apply (f_equal rev) in Heql';
    rewrite rev_inv in Heql'; rewrite <- Heql'; cbn.
      constructor.
      constructor.
      rewrite rev_app. cbn. constructor. apply IHPalindrome.
        rewrite rev_inv. reflexivity.
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

Lemma Palindrome_spec :
  forall (A : Type) (l : list A),
    Palindrome l <-> l = rev l.
(* begin hide *)
Proof.
  split.
    induction 1; cbn.
      1-2: reflexivity.
      rewrite rev_app, <- IHPalindrome; cbn. reflexivity.
    induction l as [| x | x y l'] using list_palindrome_ind; cbn; intros.
      1-2: constructor.
      rewrite rev_app in H. cbn in H. inversion H; subst; clear H.
        constructor. apply IHl'. apply app_inv_r in H2. assumption.
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