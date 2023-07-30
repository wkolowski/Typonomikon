(** * D5a: Proste funkcje na listach *)

(** Lista to najprostsza i najczęściej używana w programowaniu funkcyjnym
    struktura danych. Czas więc przeżyć na własnej skórze ich implementację.

    UWAGA: ten rozdział wyewoluował do stanu dość mocno odbiegającego od
    tego, co jest w bibliotece standardowej — moim zdanem na korzyść. *)

Require Export Lia Arith Recdef Bool Nat.

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

(** * Bardzo proste funkcje *)

(** ** [isEmpty] *)

(** Zdefiniuj funkcję [isEmpty], która sprawdza, czy lista jest pusta. *)

(* begin hide *)
Definition isEmpty {A : Type} (l : list A) : bool :=
match l with
| [] => true
| _ => false
end.
(* end hide *)

(** ** [head] *)

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

(** ** [tail] *)

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

(** ** [uncons] *)

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

(** * Proste funkcje *)

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

Lemma head_snoc :
  forall (A : Type) (x : A) (l : list A),
    head (snoc x l) =
    if isEmpty l then Some x else head l.
(* begin hide *)
Proof.
  destruct l; reflexivity.
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
  - destruct l2; inv H.
    + split; reflexivity.
    + destruct l2; inv H2.
  - destruct l2 as [| h2 t2]; inv H.
    + destruct t1; inv H2.
    + destruct (IHt1 _ _ _ H2). subst. split; reflexivity.
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

Lemma isEmpty_app :
  forall (A : Type) (l1 l2 : list A),
    isEmpty (l1 ++ l2) = andb (isEmpty l1) (isEmpty l2).
(* begin hide *)
Proof.
  destruct l1, l2; cbn; reflexivity.
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
  induction l as [| h t]; cbn; intros.
  - now rewrite !app_nil_r in H.
  - rewrite <- !app_snoc_l in H.
    now apply IHt, snoc_inv in H.
Qed.
(* end hide *)

Lemma no_infinite_app_l :
  forall (A : Type) (l l' : list A),
    l = l ++ l' -> l' = [].
(* begin hide *)
Proof.
  intros A l l' Heq.
  rewrite <- app_nil_r in Heq at 1.
  now apply app_inv_l in Heq.
Qed.
(* end hide *)

Lemma no_infinite_app_r :
  forall (A : Type) (l l' : list A),
    l = l' ++ l -> l' = [].
(* begin hide *)
Proof.
  intros A l l' Heq.
  rewrite <- app_nil_l in Heq at 1.
  now apply app_inv_r in Heq.
Qed.
(* end hide *)

Lemma no_infinite_app :
  forall (A : Type) (l l' : list A),
    l' <> [] -> l = l' ++ l -> False.
(* begin hide *)
Proof.
  intros A l l' Hneq Heq.
  apply no_infinite_app_r in Heq.
  now contradiction.
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
| h :: t => snoc h (rev t)
end.
(* end hide *)

Lemma isEmpty_rev :
  forall (A : Type) (l : list A),
    isEmpty (rev l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    apply isEmpty_snoc.
Qed.
(* end hide *)

Lemma length_rev :
  forall (A : Type) (l : list A),
    length (rev l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma snoc_rev :
  forall (A : Type) (l : list A) (x : A),
    snoc x (rev l) = rev (x :: l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
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
    rewrite app_nil_r. reflexivity.
    rewrite IHt1, snoc_app, snoc_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_rev :
  forall (A : Type) (l : list A),
    rev (rev l) = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite rev_snoc, IHt. reflexivity.
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

Lemma isEmpty_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    isEmpty (map f l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn; reflexivity.
Qed.
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
    reflexivity.
    rewrite map_snoc, IHt. reflexivity.
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
    rewrite rev_app, join_snoc, IHt. reflexivity.
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

Lemma bind_app :
  forall {A B : Type} (f : A -> list B) (l1 l2 : list A),
    bind f (l1 ++ l2) = bind f l1 ++ bind f l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite IHt1, app_assoc. reflexivity.
Qed.
(* end hide *)

Lemma rev_bind :
  forall (A B : Type) (f : A -> list B) (l : list A),
    rev (bind f l) = bind (fun x : A => rev (f x)) (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite rev_app, IHt, bind_snoc. reflexivity.
Qed.
(* end hide *)

Lemma bind_bind :
  forall {A B C : Type} (f : A -> list B) (g : B -> list C) (l : list A),
    bind g (bind f l) = bind (fun x : A => bind g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite bind_spec, map_app, join_app, <- !bind_spec, IHt. reflexivity.
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

Lemma replicate_add_comm :
  forall (A : Type) (n m : nat) (x : A),
    replicate (n + m) x = replicate (m + n) x.
(* begin hide *)
Proof.
  intros. f_equal. apply Nat.add_comm.
Qed.
(* end hide *)

Lemma rev_replicate :
  forall (A : Type) (n : nat) (x : A),
    rev (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn', snoc_replicate. cbn. reflexivity.
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

(* TODO: przemieścić funkcję iter? *)
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
    snoc (iter f n x) (iterate f n x) = iterate f (S n) x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?IHn'; reflexivity.
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

(* begin hide *)
Lemma iter_out :
  forall (A : Type) (f : A -> A) (n : nat) (x : A),
    iter f n (f x) = f (iter f n x).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

Lemma map_iterate_inv :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      map g (iterate f n (f x)) = iterate f n x.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite H, IHn'.
      reflexivity.
      assumption.
Qed.

Lemma rev_iterate_aux :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      rev (iterate g n (iter f n x)) = iterate f n (f x).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite <- map_iterate, <- map_rev, IHn', map_iterate_inv,
    snoc_iterate.
      cbn. reflexivity.
      all: assumption.
Qed.

Lemma rev_iterate_aux' :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      iterate f (S n) x = rev (iterate g (S n) (iter f n x)).
Proof.
  induction n as [| n']; cbn in *; intros.
    reflexivity.
    rewrite IHn'. rewrite ?iter_out, ?H. rewrite <- IHn'. cbn.
      do 2 f_equal. apply rev_iterate_aux. all: assumption.
Qed.
(* end hide *)

Lemma rev_iterate :
  forall (A : Type) (f g : A -> A) (n : nat) (x : A),
    (forall x : A, g (f x) = x) ->
      rev (iterate f n x) = iterate g n (iter f (n - 1) x).
(* begin hide *)
Proof.
  destruct n; intros.
    cbn. reflexivity.
    rewrite (rev_iterate_aux' _ _ _ n _ H), rev_rev. 
      cbn. rewrite Nat.sub_0_r. reflexivity.
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

Lemma last_None :
  forall {A : Type} {l : list A},
    last l = None -> l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct t.
      inversion H.
      specialize (IHt H). inversion IHt.
Qed.
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
| h :: t =>
  match init t with
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

(* TODO *) Lemma rev_unsnoc :
  forall (A : Type) (x : A) (l l' : list A),
    unsnoc l = Some (x, l') -> Some (rev l') = tail (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; inv H.
    destruct (unsnoc t) eqn: H.
      destruct p. inv H1. rewrite tail_snoc, <- (IHt _ eq_refl).
        cbn. reflexivity.
      inv H1. destruct t; inv H; cbn.
        reflexivity.
        destruct (unsnoc t); try destruct p; inv H1.
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
    rewrite last_snoc. reflexivity.
Qed.
(* end hide *)

Lemma head_rev :
  forall (A : Type) (l : list A),
    head (rev l) = last l.
(* begin hide *)
Proof.
  intros. rewrite <- last_rev, rev_rev. reflexivity.
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
    rewrite tail_snoc. destruct (rev t); cbn in *.
      destruct (init t).
        inversion IHt.
        reflexivity.
      destruct (init t); cbn; inversion IHt; subst. reflexivity.
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
  intros. rewrite <- (rev_rev _ l) at 2. rewrite tail_rev.
  destruct (init (rev l)); rewrite ?rev_rev; reflexivity.
Qed.
(* end hide *)

Lemma rev_uncons :
  forall (A : Type) (x : A) (l l' : list A),
    uncons l = Some (x, l') -> Some (rev l') = init (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; inv H.
    rewrite init_snoc. reflexivity.
Qed.
(* end hide *)

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
              rewrite length_app, Nat.add_comm in Heq. cbn in Heq. inversion Heq.
            reflexivity.
Qed.
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
      rewrite <- Nat.succ_lt_mono in H.
      destruct (IHt _ H) as [x IH]. exists x. assumption.
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

Lemma nth_snoc_lt :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    n < length l -> nth n (snoc x l) = nth n l.
(* begin hide *)
Proof.
  induction n as [| n'];
  destruct l as [| h t];
  cbn; intro H; inv H.
    reflexivity.
    reflexivity.
    apply IHn'. red. rewrite H1. constructor.
    apply IHn'. red. eapply Nat.le_trans.
      2: eassumption.
      do 2 constructor.
Qed.
(* end hide *)

Lemma nth_snoc_eq :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    n = length l -> nth n (snoc x l) = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
    reflexivity.
    all: inv H. apply IHn'. reflexivity.
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
    rewrite Nat.sub_0_r. reflexivity.
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

Lemma nth_rev_aux :
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> nth n l = nth (length l - S n) (rev l).
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; cbn; intros.
    1,3: reflexivity.
    rewrite Nat.sub_0_r, nth_snoc_eq.
      2: rewrite length_rev. 1-2: reflexivity.
      rewrite nth_snoc_lt.
        apply IHn', Nat.succ_lt_mono, H.
        rewrite length_rev. lia.
Qed.
(* end hide *)

Lemma nth_rev :
  forall (A : Type) (n : nat) (l : list A),
    n < length l -> nth n (rev l) = nth (length l - S n) l.
(* begin hide *)
Proof.
  intros. rewrite nth_rev_aux, rev_rev; rewrite length_rev.
    reflexivity.
    assumption.
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
    apply Nat.le_0_l.
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
      apply le_n_S, Nat.le_0_l.
      rewrite <- Nat.succ_lt_mono. apply (IHt _ _ H).
Qed.
(* end hide *)

Lemma nth_spec' :
  forall (A : Type) (l : list A) (n : nat),
    match nth n l with
    | None => length l <= n
    | Some x =>
        exists l1 l2 : list A,
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
      apply IHn', Nat.succ_lt_mono, H.
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
      rewrite IHt, Nat.sub_0_r. reflexivity.
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
    isEmpty (take n l) = orb (Nat.eqb 0 n) (isEmpty l).
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

Lemma take_snoc :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n <= length l -> take n (snoc x l) = take n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      f_equal. apply IHt. apply le_S_n. assumption.
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
        apply Nat.succ_lt_mono. assumption.
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
    head (take n l) = if Nat.eqb 0 n then None else head l.
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
        rewrite IHt, Nat.sub_0_r. reflexivity.
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
        rewrite Nat.sub_0_r. reflexivity.
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
    apply Nat.le_max_r.
    apply Nat.le_max_l.
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

Lemma drop_snoc :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n <= length l -> drop n (snoc x l) = snoc x (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      apply IHt. apply le_S_n. assumption.
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
    apply Nat.le_trans with (S (length l1)).
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
    apply Nat.le_0_l.
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
    destruct n as [ |n'].
      rewrite drop_length'.
        reflexivity.
        rewrite length_snoc, length_rev, <- Nat.sub_0_r. apply le_n.
      rewrite IHt, length_snoc, drop_snoc; cbn.
        rewrite rev_snoc. reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma take_rev :
  forall (A : Type) (l : list A) (n : nat),
    take n (rev l) = rev (drop (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_take :
  forall (A : Type) (l : list A) (n : nat),
    rev (take n l) = drop (length l - n) (rev l).
(* begin hide *)
Proof.
  intros. rewrite take_rev_aux, !rev_rev, length_rev. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Lemma drop_rev_aux :
  forall (A : Type) (l : list A) (n : nat),
    drop n l = rev (take (length (rev l) - n) (rev l)).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [ |n'].
      rewrite take_length'.
        rewrite rev_snoc, rev_rev. reflexivity.
        rewrite length_snoc, length_rev, <- Nat.sub_0_r. apply le_n.
      rewrite IHt, length_snoc, take_snoc; cbn.
        reflexivity.
        apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma drop_rev :
  forall (A : Type) (l : list A) (n : nat),
    drop n (rev l) = rev (take (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite drop_rev_aux, rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_drop :
  forall (A : Type) (l : list A) (n : nat),
    drop n (rev l) = rev (take (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite drop_rev_aux, rev_rev. reflexivity.
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
(* ===> [[4; 5; 1; 2; 3]] : list nat *)

Compute cycle 6 [1; 2; 3; 4; 5].
(* ===> [[2; 3; 4; 5; 1]] : list nat *)

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
    apply Nat.le_0_l.
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
    apply Nat.le_0_l.
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
        apply le_n_S, Nat.le_0_l.
        rewrite <- Nat.succ_lt_mono.
        apply IHt. destruct (splitAt n' t); congruence.
    induction l as [| h t]; cbn; intros.
      inv H.
      destruct n as [| n'].
        inversion 1.
        destruct (splitAt n' t) eqn: Heq.
          destruct p, p. congruence.
          intro. apply (IHt n'); [| easy].
            now apply Nat.succ_lt_mono in H.
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
          rewrite <- Nat.succ_lt_mono. apply (IHt _ _ _ _ Heq).
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
      apply Nat.succ_lt_mono in H. destruct (IHt _ H) as [x IH].
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
      if Nat.eqb n (length l)
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
    rewrite Nat.sub_0_r. destruct (splitAt n l2).
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
      rewrite splitAt_snoc, splitAt_length_ge.
        1-2: rewrite length_rev, Nat.sub_0_r.
        rewrite Nat.ltb_irrefl, Nat.eqb_refl, rev_rev. cbn. reflexivity.
        reflexivity.
      rewrite IHt, splitAt_snoc; clear IHt.
        replace (length t - S n' <? length (rev t)) with true.
          destruct (splitAt (length t - S n') (rev t)) eqn: Heq.
            destruct p, p. cbn. rewrite rev_snoc. reflexivity.
            reflexivity.
          rewrite length_rev. destruct (Nat.ltb_spec (length t - S n') (length t)); lia.
        apply Nat.succ_lt_mono. assumption.
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
  rewrite length_rev, rev_rev. reflexivity.
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
      rewrite Nat.sub_0_r. reflexivity.
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
      rewrite Nat.sub_0_r. reflexivity.
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
    rewrite Nat.min_r.
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
      replace (S (length t)) with (length (snoc h (rev t))).
        rewrite insert_length, ?rev_snoc, rev_rev. reflexivity.
        rewrite length_snoc, length_rev. reflexivity.
      rewrite ?IHt, snoc_app_singl, insert_app, length_rev.
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
  intros. rewrite insert_rev_aux, rev_rev, length_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_insert :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    rev (insert l n x) = insert (rev l) (length l - n) x.
(* begin hide *)
Proof.
  intros. pose (insert_rev _ (rev l)).
  rewrite rev_rev in e.
  rewrite e, rev_rev, length_rev. reflexivity.
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
          rewrite drop_app, drop_length, Nat.sub_diag, drop_0 in H.
            cbn in H. assumption.
        exists (length hl + m). rewrite <- H, insert_app.
          destruct (Nat.leb_spec (length hl + m) (length hl)).
            assert (m = 0) by lia. subst.
              rewrite drop_app, drop_length, Nat.sub_diag, drop_0, insert_0 in IH.
              rewrite Nat.add_0_r, insert_length, app_snoc_l, <- IH. reflexivity.
            rewrite <- H, drop_app, drop_length, Nat.sub_diag, drop_0 in IH.
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
      (* TODO: take_insert *)
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
      apply Nat.succ_lt_mono in H.
      destruct (IHt _ x H) as [l' IH].
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
    if Nat.eqb n (length l)
    then Some (snoc y l)
    else
      match replace l n y with
      | None => None
      | Some l' => Some (snoc x l')
      end.
(* begin hide *)
Proof.
  intros. destruct (n =? length l) eqn: Heq.
    apply Nat.eqb_eq in Heq as ->.
      apply replace_snoc_eq. reflexivity.
    apply Nat.eqb_neq in Heq.
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
    rewrite Nat.sub_0_r. destruct (replace l2 n x); reflexivity.
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
      rewrite Nat.sub_0_r, replace_snoc,
        length_rev, Nat.eqb_refl, rev_snoc, rev_rev. reflexivity.
      apply Nat.succ_lt_mono in H.
      rewrite replace_snoc, (IHt _ _ H).
        destruct (replace (rev t) (length t - S n') x) eqn: Heq.
          destruct (Nat.eqb_spec (length t - S n') (length (rev t))).
            rewrite length_rev in e. lia.
            rewrite rev_snoc. reflexivity.
          rewrite replace_spec' in Heq.
            inv Heq.
            rewrite length_rev. unfold lt. lia.
Qed.
(* end hide *)

Lemma replace_rev :
  forall (A : Type) (l : list A) (n : nat) (x : A),
    n < length l ->
      replace (rev l) n x = option_map rev (replace l (length l - S n) x).
(* begin hide *)
Proof.
  intros. rewrite (replace_rev_aux _ (rev l));
  rewrite ?rev_rev, length_rev.
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
      rewrite Nat.sub_0_r. reflexivity.
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
      rewrite Nat.sub_0_r. reflexivity.
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
        rewrite Nat.sub_0_r, drop_0. reflexivity.
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
            rewrite ?drop_0 in IHt. rewrite IHt, Nat.sub_0_r. reflexivity.
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
      apply Nat.succ_lt_mono in H. rewrite (IHt _ H). destruct (remove n' t).
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
        apply Nat.succ_lt_mono in H. specialize (IHt _ H). contradiction.
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
      apply Nat.succ_lt_mono in H. rewrite (IHt _ H). destruct (remove n' t).
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
    rewrite Nat.sub_0_r. destruct (remove n l2).
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
      apply Nat.succ_lt_mono in H. rewrite (IHt _ _ H).
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
    rewrite Nat.sub_0_r. destruct (remove n l2).
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
    destruct n as [| n'].
      rewrite Nat.sub_0_r, <- length_rev, remove_length_snoc, rev_rev.
        reflexivity.
      apply Nat.succ_lt_mono in H. rewrite (IHt _ H), remove_snoc_lt.
        destruct (remove (length t - S n') (rev t)).
          destruct p. rewrite rev_snoc. 1-2: reflexivity.
        rewrite length_rev. lia.
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
  intros. rewrite remove_rev_aux, rev_rev; rewrite length_rev.
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
      rewrite Nat.sub_0_r. reflexivity.
      apply Nat.succ_lt_mono in H. rewrite (IHn' _ _ H). destruct n'; cbn.
        destruct m'; inversion H.
        rewrite Nat.sub_0_r. reflexivity.
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
      rewrite Nat.sub_0_r. reflexivity.
      rewrite IHn'.
        cbn. reflexivity.
        apply Nat.succ_lt_mono. assumption.
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
        apply Nat.succ_lt_mono. assumption.
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

Lemma rev_unzip :
  forall (A B : Type) (l : list (A * B)) (la : list A) (lb : list B),
    unzip l = (la, lb) -> unzip (rev l) = (rev la, rev lb).
(* begin hide *)
Proof.
  induction l as [| [ha ta] t]; cbn; intros.
    inv H. cbn. reflexivity.
    destruct (unzip t). inv H. rewrite unzip_snoc, (IHt _ _ eq_refl).
      cbn. reflexivity.
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

Lemma zipWith_not_rev :
  exists (A B C : Type) (f : A -> B -> C) (la : list A) (lb : list B),
    zipWith f (rev la) (rev lb) <> rev (zipWith f la lb).
(* begin hide *)
Proof.
  exists bool, bool, (prod bool bool),
         pair, [true; false; true], [false; true].
  cbn. inversion 1.
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

Lemma rev_unzipWith :
  forall (A B C : Type) (f : A -> B * C) (l : list A),
    unzipWith f (rev l) =
      let (la, lb) := unzipWith f l in (rev la, rev lb).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (unzipWith f t), (f h) eqn: Heq.
      rewrite unzipWith_spec, map_snoc, map_rev, unzip_snoc, IHt, Heq in *.
        cbn. reflexivity.
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
    intro. apply le_n_S, Nat.le_0_l.
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
    rewrite any_snoc, IHt, ?Bool.orb_assoc, Bool.orb_comm. reflexivity.
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
    apply le_n_S, Nat.le_0_l.
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
    rewrite all_snoc, IHt, Bool.andb_comm. reflexivity.
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
          apply Nat.succ_lt_mono in H0. destruct (IHt H _ H0) as (x & H1 & H2).
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
    apply le_n_S, Nat.le_0_l.
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
    rewrite find_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma findLast_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    findLast p (rev l) = find p l.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l), find_rev, rev_rev. reflexivity.
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
    rewrite removeFirst_snoc, IHt. destruct (removeLast p t).
      destruct p0. cbn. reflexivity.
      destruct (p h); reflexivity.
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
  intros. rewrite <- (rev_rev _ l) at 2. rewrite removeFirst_rev.
  destruct (removeLast p (rev l)).
    destruct p0. rewrite rev_rev. all: reflexivity.
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
      inversion H; subst; clear H. apply le_n_S, Nat.le_0_l.
      case_eq (findIndex p t); intros; rewrite H1 in *.
        inversion H; subst; clear H. rewrite <- Nat.succ_lt_mono. apply IHt. reflexivity.
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
      exists 0. split; [reflexivity | apply Nat.le_0_l].
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
            rewrite Nat.sub_0_r in IHt. specialize (IHt eq_refl).
            destruct IHt as (x & H1 & H2 & H3). exists x.
              repeat split; trivial. intros. destruct n as [| n']; cbn in *.
                inversion H0; subst. assumption.
                apply (H3 n').
                  apply Nat.succ_lt_mono. assumption.
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
              rewrite Nat.sub_0_r. reflexivity.
              assumption.
              intros. apply H3 with (S n).
                rewrite <- Nat.succ_lt_mono, <- Nat.sub_0_r. assumption.
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
        now apply (IHt _ eq_refl), Nat.succ_lt_mono.
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
        inv H. split; [reflexivity | apply Nat.le_0_l].
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
      rewrite Nat.sub_0_r. assumption.
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
    let H := fresh "H" in destruct x eqn: H
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
        inv H. exists 0, 0. repeat split; apply Nat.le_0_l.
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
    apply Nat.le_0_l.
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
    rewrite count_snoc, IHt. destruct (p h); cbn.
      rewrite Nat.add_comm. cbn. reflexivity.
      apply Nat.add_0_r.
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
    rewrite Nat.add_0_r. reflexivity.
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
        destruct p0. inversion H; subst; clear H.
          cbn. destruct (p h), (p x) eqn: Hpx; cbn;
          rewrite (IHt _ _ _ Heq), Hpx; reflexivity.
        inversion H.
Qed.
(* end hide *)

Lemma count_take :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    count p (take n l) <= n.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply Nat.le_0_l.
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
    apply Nat.le_0_l.
    destruct n as [| n']; cbn.
      apply le_n.
      destruct (p h).
        apply le_n_S, IHt.
        apply Nat.le_trans with (min n' (count p t)).
          apply IHt.
          destruct (count p t).
            rewrite Nat.min_0_r. apply le_n.
            apply Nat.le_trans with (min (S n') (S n)).
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
          rewrite Nat.sub_0_r, drop_0 in IHt. assumption.
        apply le_S. specialize (IHt 0).
          rewrite Nat.sub_0_r, drop_0 in IHt. assumption.
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
        rewrite Nat.add_comm. cbn. reflexivity.
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
        rewrite Nat.sub_0_r. reflexivity.
        rewrite <- Nat.sub_succ_l; cbn.
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
    apply Nat.le_0_l.
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
    apply Nat.le_0_l.
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
      rewrite <- plus_n_Sm, Nat.sub_succ_l.
        reflexivity.
        etransitivity.
          apply count_andb_le_l.
          apply Nat.le_add_r.
      rewrite <- Nat.sub_succ_l; cbn.
        reflexivity.
        etransitivity.
          apply count_andb_le_l.
          apply Nat.le_add_r.
      rewrite <- plus_n_Sm, Nat.sub_succ_l; cbn.
        reflexivity.
        etransitivity.
          apply count_andb_le_l.
          apply Nat.le_add_r.
      reflexivity.
Restart.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    pose (count_andb_le_l A p q).
      destruct (p h) eqn: Hph, (q h) eqn: Hqh; cbn;
      rewrite IHt, <- ?plus_n_Sm, <- ?Nat.sub_succ_l; auto.
        all: etransitivity; [apply count_andb_le_l | apply Nat.le_add_r].
Qed.
(* end hide *)

Lemma count_orb_le :
  forall (A : Type) (p q : A -> bool) (l : list A),
    count (fun x : A => orb (p x) (q x)) l <=
    count p l + count q l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply Nat.le_0_l.
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
      rewrite <- plus_n_Sm, Nat.sub_succ_l.
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
      apply Nat.le_trans with (length t).
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
    reflexivity.
    rewrite filter_snoc. destruct (p h); cbn; rewrite IHt; reflexivity.
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
            apply Nat.le_trans with (S m).
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
Fixpoint partition {A : Type} (p : A -> bool) (l : list A) : list A * list A :=
match l with
| [] => ([], [])
| h :: t =>
  let (l1, l2) := partition p t in
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
      rewrite Nat.add_0_r, IHt, map_map. do 2 f_equal.
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
    rewrite findIndices_snoc, length_rev. destruct (p h); cbn.
      all: rewrite ?rev_snoc, ?Nat.sub_0_r, map_map, IHt; reflexivity.
Qed.
(* end hide *)

Lemma findIndices_rev :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndices p (rev l) =
    rev (map (fun n : nat => length l - S n) (findIndices p l)).
(* begin hide *)
Proof.
  intros. rewrite <- findIndices_rev_aux, rev_rev. reflexivity.
Qed.
(* end hide *)

Lemma rev_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    rev (findIndices p l) =
    map (fun n : nat => length l - S n) (findIndices p (rev l)).
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l) at 1.
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
  rewrite <- head_rev, <- (rev_rev _ l) at 1.
  rewrite findIndices_rev_aux, <- head_findIndices.
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
          destruct (p h), (p x); cbn; rewrite ?map_app, ?Nat.add_0_r.
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
      inversion H0. apply Nat.le_0_l.
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
      inversion H0. apply Nat.le_0_l.
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
    apply Nat.le_0_l.
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
      rewrite Nat.sub_0_r. reflexivity.
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
      all p l = andb (Nat.eqb (length b) 0) (all p e).
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
Lemma naps_snoc :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    naps p (snoc x l) =
    if p x
    then Some (l, x, [])
    else
      match naps p l with
      | None => None
      | Some (b, y, e) => Some (b, y, snoc x e)
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
      rewrite naps_snoc, Hph, rev_rev. cbn. reflexivity.
      rewrite naps_snoc, Hph, IHt. destruct (naps p (rev t)).
        destruct p0, p0. rewrite rev_snoc. reflexivity.
        reflexivity.
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
  intros. rewrite span_rev_aux, rev_rev. reflexivity.
Qed.
(* end hide *)

(** * Rozstrzyganie równości list (TODO) *)

Fixpoint list_eq_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| [], _ => false
| _, [] => false
| h1 :: t1, h2 :: t2 => eq_dec h1 h2 && list_eq_dec eq_dec t1 t2
end.

Lemma list_eq_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (l1 = l2) (list_eq_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
    1-3: constructor; reflexivity + inversion 1.
    destruct (eq_dec_spec h1 h2); cbn.
      destruct (IHt1 t2); constructor.
        f_equal; assumption.
        intro. inv H. contradiction.
      constructor. intro. inv H. contradiction.
Qed.
(* end hide *)