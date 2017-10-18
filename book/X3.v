(** * X3: Listy *)

Require Import Arith.

(** Lista to najprostsza i najczęściej używana w programowaniu funkcyjnym
    struktura danych. Czas więc przeżyć na własnej skórze ich implementację
    w bibliotece standardowej. *)

(** Zdefiniuj [list] (bez podglądania). *)

(* begin hide *)
Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.
(* end hide *)

Arguments nil [A].
Arguments cons [A] _ _.

Notation "[]" := nil.
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** Zdefiniuj funkcję [length], która oblicza długość listy. *)

(* begin hide *)
Fixpoint length {A : Type} (l : list A) : nat :=
match l with
    | [] => 0
    | _ :: t => S (length t)
end.
(* end hide *)

Theorem length_nil : forall A : Type, length (@nil A) = 0.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Theorem length_cons : forall (A : Type) (h : A) (t : list A),
    exists n : nat, length (h :: t) = S n.
(* begin hide *)
Proof.
  intros. exists (length t). simpl. trivial.
Qed.
(* end hide *)

Theorem length_0 : forall (A : Type) (l : list A),
    length l = 0 -> l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    trivial.
    inversion H.
Qed.
(* end hide *)

(** *** [app] *)

(** Zdefiniuj funkcję [app], która skleja dwie listy. *)

(* begin hide *)
Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
match l1 with
    | [] => l2
    | h :: t => h :: app t l2
end.
(* end hide *)

Notation "l1 ++ l2" := (app l1 l2).

Theorem app_nil_l : forall (A : Type) (l : list A),
    [] ++ l = l.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Theorem app_nil_r : forall (A : Type) (l : list A),
    l ++ [] = l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem app_assoc : forall (A : Type) (l1 l2 l3 : list A),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Theorem app_length : forall (A : Type) (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intro.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Theorem app_cons : forall (A : Type) (x : A) (l1 l2 : list A),
    (x :: l1) ++ l2 = x :: (l1 ++ l2).
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

Theorem app_cons2 : forall (A : Type) (x : A) (l1 l2 : list A),
    l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    f_equal. rewrite IHt1. trivial.
Qed.
(* end hide *)

Theorem no_infinite_cons : forall (A : Type) (x : A) (l : list A),
    l = x :: l -> False.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    inversion H. apply IHt. assumption.
Qed.
(* end hide *)

Theorem no_infinite_app : forall (A : Type) (l l' : list A),
    l' <> [] -> l = l' ++ l -> False.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    rewrite app_nil_r in H0. subst. apply H. trivial.
    destruct l'.
      contradiction H. trivial.
      inversion H0. apply IHt with (l' ++ [a]).
        intro. assert (length (l' ++ [a]) = length (@nil A)).
          rewrite H1. trivial.
          rewrite app_length in H4. simpl in H4. rewrite plus_comm in H4.
            inversion H4.
        rewrite <- app_cons2. assumption.
Qed.
(* end hide *)

Theorem app_inv1 : forall (A : Type) (l l1 l2 : list A),
    l ++ l1 = l ++ l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    assumption.
    apply IHt. inversion H. trivial.
Qed.
(* end hide *)

Theorem app_inv2 : forall (A : Type) (l l1 l2 : list A),
    l1 ++ l = l2 ++ l -> l1 = l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    destruct l2.
      trivial.
      cut False. inversion 1. eapply no_infinite_app; eauto. inversion 1.
    destruct l2.
      simpl in H. cut False. inversion 1. symmetry in H.
        rewrite <- app_cons in H. eapply no_infinite_app; eauto. inversion 1.
      inversion H. f_equal. apply IHt1. assumption.
Qed.
(* end hide *)

Theorem app_eq_nil : forall (A : Type) (l1 l2 : list A),
    l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    split; trivial.
    inversion H.
Qed.
(* end hide *)

(** Zdefiniuj funkcję [rev], która odwraca listę. *)

(* begin hide *)
Fixpoint rev {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => rev t ++ [h]
end.
(* end hide *)

Theorem rev_length : forall (A : Type) (l : list A),
    length (rev l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite app_length, plus_comm. simpl. rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem rev_app : forall (A : Type) (l1 l2 : list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intro.
    rewrite app_nil_r. trivial.
    rewrite IHt1. rewrite app_assoc. trivial.
Qed.
(* end hide *)

Theorem rev_inv : forall (A : Type) (l : list A),
    rev (rev l) = l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite rev_app. rewrite IHt. simpl. trivial.
Qed.
(* end hide *)

(** Zdefiniuj induktywny predykat [elem]. [elem x l] jest spełniony, gdy
    [x] jest elementem listy [l]. *)

(* begin hide *)
Inductive elem {A : Type} : A -> list A -> Prop :=
    | elem_head : forall (x : A) (l : list A),
        elem x (x :: l)
    | elem_cons : forall (x h : A) (t : list A),
        elem x t -> elem x (h :: t).
(* end hide *)

Theorem elem_nil : forall (A : Type) (x : A), ~ elem x [].
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Theorem elem_inv_head : forall (A : Type) (x h : A) (t : list A),
    ~ elem x (h :: t) -> x <> h.
(* begin hide *)
Proof.
  intros; intro. apply H. subst. constructor.
Qed.
(* end hide *)

Theorem elem_inv_tail : forall (A : Type) (x h : A) (t : list A),
    ~ elem x (h :: t) -> ~ elem x t.
(* begin hide *)
Proof.
  intros; intro. apply H. constructor. assumption.
Qed.
(* end hide *)

Lemma elem_app1 : forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; simpl; intros.
    assumption.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Theorem elem_app2 : forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l1 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  induction 1; simpl.
    constructor.
    constructor. assumption.
Qed.
(* end hide *)

Theorem elem_app_or : forall (A : Type) (x : A) (l1 l2 : list A),
    elem x (l1 ++ l2) -> elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    right. assumption.
    inversion H; subst.
      left. constructor.
      destruct (IHt1 _ H2).
        left. constructor. assumption.
        right. assumption.
Qed.
(* end hide *)

Theorem elem_or_app : forall (A : Type) (x : A) (l1 l2 : list A),
    elem x l1 \/ elem x l2 -> elem x (l1 ++ l2).
(* begin hide *)
Proof.
  destruct 1.
    inversion H; subst.
      simpl. constructor.
      simpl. constructor. apply elem_app2. assumption.
    apply elem_app1. assumption.
Qed.
(* end hide *)

Theorem elem_rev : forall (A : Type) (x : A) (l : list A),
    elem x l -> elem x (rev l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    assumption.
    inversion H; subst.
      apply elem_app1. constructor.
      apply elem_app2. apply IHt. assumption.
Qed.
(* end hide *)

Theorem elem_rev_conv :
  forall (A : Type) (x : A) (l : list A),
    elem x (rev l) -> elem x l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    trivial.
    apply elem_app_or in H. destruct H.
      specialize (IHt H). right. assumption.
      inversion H; subst.
        left.
        inversion H2.
Qed.
(* end hide *)

Theorem elem_split : forall (A : Type) (x : A) (l : list A),
    elem x l -> exists l1 l2 : list A, l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    inversion H; subst.
      exists [], t. simpl. trivial.
      destruct (IHt H2) as [l1 [l2 H']]. exists (h :: l1), l2.
        rewrite H'. simpl. trivial.
Qed.
(* end hide *)

(** Zdefiniuj funkcję [map], która aplikuje funkcję [f] do każdego
    elementu listy. *)

(* begin hide *)
Fixpoint map {A B : Type} (f : A -> B) (la : list A) : list B :=
match la with
    | [] => []
    | h :: t => f h :: map f t
end.
(* end hide *)

Theorem map_id : forall (A : Type) (l : list A),
    map id l = l.
(* begin hide *)
Proof.
  unfold id. induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem map_comp : forall (A B C : Type) (f : A -> B) (g : B -> C)
    (l : list A), map g (map f l) = map (fun x : A => g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem map_length : forall (A B : Type) (f : A -> B) (l : list A),
    length (map f l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem map_app : forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1. trivial.
Qed.
(* end hide *)

Theorem elem_map :
    forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    elem x l -> elem (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; inversion 1; subst.
    constructor.
    constructor. apply IHt. assumption.
Qed.
(* end hide *)

Theorem elem_map_conv : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    elem y (map f l) <-> exists x : A, f x = y /\ elem x l.
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; simpl; intros.
      inversion H.
      inversion H; subst.
        exists h. split; trivial. constructor.
        destruct (IHt H2) as [x [Hx1 Hx2]]. exists x.
          split; trivial. constructor. assumption.
    induction l as [| h t]; simpl; destruct 1 as [x [Hx1 Hx2]].
      inversion Hx2.
      inversion Hx2; subst.
        constructor.
        constructor. apply IHt. exists x. split; trivial.
Qed.
(* end hide *)

Theorem map_rev : forall (A B : Type) (f : A -> B) (l : list A),
    map f (rev l) = rev (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite map_app, IHt. simpl. trivial.
Qed.
(* end hide *)

Theorem map_ext_elem : forall (A B : Type) (f g : A -> B) (l : list A),
    (forall x : A, elem x l -> f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    trivial.
    rewrite H, IHt.
      trivial.
      intros. apply H. constructor. assumption.
      constructor.
Qed.
(* end hide *)

Theorem map_ext : forall (A B : Type) (f g : A -> B) (l : list A),
    (forall x : A, f x = g x) -> map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intro.
    trivial.
    rewrite H, IHt; trivial.
Qed.
(* end hide *)

(** Napisz funkcję [join], która spłaszcza listę list. *)

(* begin hide *)
Fixpoint join {A : Type} (lla : list (list A)) : list A :=
match lla with
    | [] => []
    | h :: t => h ++ join t
end.
(* end hide *)

Theorem join_app : forall (A : Type) (l1 l2 : list (list A)),
    join (l1 ++ l2) = join l1 ++ join l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1, app_assoc. trivial.
Qed.
(* end hide *)

Theorem join_map : forall (A B : Type) (f : A -> B) (l : list (list A)),
    map f (join l) = join (map (map f) l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    trivial.
    rewrite map_app, IHt. trivial.
Qed.
(* end hide *)

(** *** [repeat] (TODO: nastąpiła duplikacja) *)

(** Zdefiniuj funkcję [repeat], która zwraca listę [n] powtórzeń wartości
    [x]. *)

(* begin hide *)
Fixpoint repeat {A : Type} (n : nat) (x : A) : list A :=
match n with
    | 0 => []
    | S n' => x :: repeat n' x
end.
(* end hide *)

Theorem repeat_length : forall (A : Type) (n : nat) (x : A),
    length (repeat n x) = n.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intro; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem repeat_elem : forall (A : Type) (n : nat) (x y : A),
    elem x (repeat n y) -> x = y.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; inversion H; subst.
    trivial.
    apply IHn'. assumption.
Qed.
(* end hide *)

(** *** [nth] *)

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

Theorem nth_length : forall (A : Type) (n : nat) (l : list A),
    n < length l -> exists x : A, nth n l = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    destruct l.
      inversion H.
      exists a. simpl. trivial.
    destruct l; simpl in *.
      inversion H.
      unfold lt in H. simpl in H. apply le_S_n in H.
        destruct (IHn' _ H) as [x Hx]. exists x. assumption.
Qed.
(* end hide *)

Theorem nth_elem : forall (A : Type) (n : nat) (l : list A),
    n < length l -> exists x : A, nth n l = Some x /\ elem x l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; simpl; intros.
    inversion H.
    exists h. split; [trivial | constructor].
    inversion H.
    apply lt_S_n in H. destruct (IHn' _ H) as [x [Hx1 Hx2]].
      exists x. split; try constructor; assumption.
Qed.
(* end hide *)

Theorem nth_elem_conv : forall (A : Type) (x : A) (l : list A),
    elem x l -> exists n : nat, nth n l = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; inversion 1; subst.
    exists 0. simpl. trivial.
    destruct (IHt H2) as [n Hn]. exists (S n). simpl. assumption.
Qed.
(* end hide *)

Theorem nth_overflow : forall (A : Type) (n : nat) (l : list A),
    length l <= n -> ~ exists x : A, nth n l = Some x.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l; simpl; intros.
    destruct 1. inversion H0.
    inversion H.
    destruct 1. inversion H0.
    apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem nth_app1 : forall (A : Type) (n : nat) (l1 l2 : list A),
    n < length l1 -> nth n (l1 ++ l2) = nth n l1.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l1; simpl; intros.
    inversion H.
    trivial.
    inversion H.
    apply IHn'. apply lt_S_n. assumption.
Qed.
(* end hide *)

Theorem nth_app2 : forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 <= n -> nth n (l1 ++ l2) = nth (n - length l1) l2.
(* begin hide *)
Proof.
  induction n as [| n'].
    destruct l1 as [| h1 t1]; intros.
      destruct l2; simpl; trivial.
      destruct l2; simpl; inversion H.
    destruct l1 as [| h1 t1]; intros.
      simpl. trivial.
      simpl in *. apply IHn'. apply le_S_n. assumption.
Qed.
(* end hide *)

Theorem nth_split : forall (A : Type) (n : nat) (l : list A) (x : A),
    nth n l = Some x -> exists l1 l2 : list A,
        l = l1 ++ x :: l2 /\ length l1 = n.
(* begin hide *)
Proof.
  induction n as [| n'].
    destruct l as [| h t]; simpl; inversion 1; subst. exists [], t.
      simpl. split; trivial.
    destruct l as [| h t]; simpl; inversion 1; subst.
      destruct (IHn' _ _ H) as [l1 [l2 [Heq Hlen]]].
      exists (h :: l1), l2. split.
        rewrite Heq. trivial.
        simpl. rewrite Hlen. trivial.
Qed.
(* end hide *)

Theorem nth_None : forall (A : Type) (n : nat) (l : list A),
    nth n l = None -> length l <= n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; simpl; intros.
    trivial.
    inversion H.
    apply le_0_n.
    apply le_n_S. apply IHn'. assumption.
Qed.
(* end hide *)

Theorem nth_Some : forall (A : Type) (n : nat) (l : list A) (x : A),
    nth n l = Some x -> n < length l.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t]; simpl; intros.
    inversion H.
    red. apply le_n_S. apply le_0_n.
    inversion H.
    apply lt_n_S. eapply IHn'. eassumption.
Qed.
(* end hide *)

Theorem map_nth :
    forall (A B : Type) (f : A -> B) (n : nat) (l : list A) (x : A),
        nth n l = Some x -> nth n (map f l) = Some (f x).
(* begin hide *)
Proof.
  induction n as [| n'].
    destruct l as [| h t]; simpl; inversion 1; trivial.
    destruct l as [| h t]; simpl; inversion 1; trivial.
      rewrite (IHn' t x); [trivial | assumption].
Qed.
(* end hide *)

(** *** [head] i [last] *)

(** Zdefiniuj funkcje [head] i [last], które zwracają odpowiednio pierwszy
    i ostatni element listy (lub [None], jeżeli jest pusta). *)

(* begin hide *)
Fixpoint head {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | h :: _ => Some h
end.

Fixpoint last {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | [x] => Some x
    | h :: t => last t
end.
(* end hide *)

Theorem head_nil : forall (A : Type),
    head [] = (@None A).
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem last_nil : forall (A : Type), last [] = (@None A).
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem head_nth: forall (A : Type) (l : list A),
    head l = nth 0 l.
(* begin hide *)
Proof.
  destruct l as [| h t]; simpl; trivial.
Qed.
(* end hide *)

Theorem last_nth : forall (A : Type) (l : list A),
    last l = nth (length l - 1) l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    destruct t.
      simpl. trivial.
      rewrite IHt. simpl. rewrite <- minus_n_O. trivial.
Qed.
(* end hide *)

(** *** [tail] i [init] *)

(** Zdefiniuj funkcje [tail] i [init], które zwracają odpowiednio ogon
    listy oraz wszystko poza jej ostatnim elementem (lub [None], gdy
    lista jest pusta). *)

(* begin hide *)
Fixpoint tail {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | _ :: t => Some t
end.

Fixpoint init {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | h :: t => match init t with
        | None => Some [h]
        | Some t' => Some (h :: t')
    end
end.
(* end hide *)

(** *** [take] i [drop] *)

(** Zdefiniuj funkcje [take] i [drop], które odpowiednio biorą lub
    odrzucają n pierwszych elementów listy. *)

(* begin hide *)
Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => l
    | _, [] => []
    | S n', h :: t => drop n' t
end.
(* end hide *)

Theorem take_nil : forall (A : Type) (n : nat),
    take n [] = @nil A.
(* begin hide *)
Proof.
  destruct n; simpl; trivial.
Qed.
(* end hide *)

Theorem drop_nil : forall (A : Type) (n : nat),
    drop n [] = @nil A.
(* begin hide *)
Proof.
  destruct n; simpl; trivial.
Qed.
(* end hide *)

Theorem take_cons : forall (A : Type) (n : nat) (h : A) (t : list A),
    take (S n) (h :: t) = h :: take n t.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Theorem drop_cons : forall (A : Type) (n : nat) (h : A) (t : list A),
    drop (S n) (h :: t) = drop n t.
(* begin hide *)
Proof.
  trivial.
Qed.
(* end hide *)

Theorem take_0 : forall (A : Type) (l : list A),
    take 0 l = [].
(* begin hide *)
Proof.
  destruct l; simpl; trivial.
Qed.
(* end hide *)

Theorem drop_0 : forall (A : Type) (l : list A),
    drop 0 l = l.
(* begin hide *)
Proof.
  destruct l; simpl; trivial.
Qed.
(* end hide *)

Theorem take_length : forall (A : Type) (l : list A),
    take (length l) l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem drop_length : forall (A : Type) (l : list A),
    drop (length l) l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem take_length' : forall (A : Type) (n : nat) (l : list A),
  length l <= n -> take n l = l.
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

Theorem drop_length' : forall (A : Type) (n : nat) (l : list A),
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

Theorem length_take : forall (A : Type) (n : nat) (l : list A),
    n <= length l -> length (take n l) = n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t];
  simpl; inversion 1; subst; trivial;
  f_equal; apply IHn'; apply le_S_n in H; assumption.
Qed.
(* end hide *)

Theorem length_take' :
  forall (A : Type) (n : nat) (l : list A),
    length (take n l) <= n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    trivial.
    destruct l as [| h t]; cbn.
      apply le_0_n.
      apply le_n_S. apply IHn'.
Qed.
(* end hide *)

Theorem drop_take : forall (A : Type) (n : nat) (l : list A),
    n <= length l -> length (drop n l) = length l - n.
(* begin hide *)
Proof.
  induction n as [| n']; destruct l as [| h t];
  simpl; inversion 1; subst; trivial;
  f_equal; apply IHn'; apply le_S_n in H; assumption.
Qed.
(* end hide *)

Theorem take_map :
    forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
        map f (take n l) = take n (map f l).
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    destruct l as [| h t]; simpl.
      trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem drop_map :
    forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
        map f (drop n l) = drop n (map f l).
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    destruct l as [| h t]; simpl.
      trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem take_elem : forall (A : Type) (n : nat) (l : list A) (x : A),
    elem x (take n l) -> elem x l.
(* begin hide *)
Proof.
  induction n as [| n'].
    simpl. inversion 1.
    destruct l as [| h t]; simpl.
      inversion 1.
      intros. inversion H; subst; constructor. apply IHn'. assumption.
Qed.
(* end hide *)

Theorem drop_elem : forall (A : Type) (n : nat) (l : list A) (x : A),
    elem x (drop n l) -> elem x l.
(* begin hide *)
Proof.
  induction n as [| n'].
    simpl. trivial.
    destruct l as [| h t]; simpl.
      inversion 1.
      intros. constructor. apply IHn'. assumption.
Qed.
(* end hide *)

Theorem take_take : forall (A : Type) (n m : nat) (l : list A),
    take m (take n l) = take n (take m l).
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    destruct m; trivial.
    destruct m as [| m'].
      simpl. trivial.
      destruct l as [| h t]; simpl.
        trivial.
        rewrite IHn'. trivial.
Qed.
(* end hide *)

Lemma drop_S : forall (A : Type) (n m : nat) (l : list A),
    drop (S m) (drop n l) = drop m (drop (S n) l).
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    destruct l; simpl; try rewrite drop_nil; trivial.
    destruct l as [| h t].
      simpl. rewrite drop_nil. trivial.
      do 2 rewrite drop_cons. rewrite IHn'. trivial.
Qed.
(* end hide *) 

Theorem drop_drop : forall (A : Type) (n m : nat) (l : list A),
    drop m (drop n l) = drop n (drop m l).
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    destruct m; trivial.
    induction m as [| m'].
      simpl. trivial.
      induction l as [| h t].
        simpl. trivial.
        repeat rewrite drop_cons in *. rewrite IHn'. rewrite drop_S. trivial. 
Qed.
(* end hide *)

(* begin hide *)
Theorem take_drop_rev :
  forall (A : Type) (n : nat) (l : list A),
    take n (rev l) = rev (drop (length l - n) l).
Proof.
  induction n as [| n']; intros.
    rewrite <- minus_n_O. rewrite drop_length. simpl. trivial.
    destruct l as [| h t]; simpl; trivial.
Restart.
  intros A n l. generalize dependent n.
  induction l as [| h t]; simpl; intros.
    apply take_nil.
    destruct n as [| n'].
      simpl. rewrite drop_length. simpl. trivial.
Restart.
(*  intros. remember (rev l) as revl.
  functional induction @take A n revl; subst.
    rewrite <- minus_n_O, drop_length. trivial.
    destruct l; simpl in *.
      trivial.
      change [a] with (rev [a]) in Heqrevl. rewrite <- rev_app in Heqrevl.
        assert (length (@nil A) = length (a :: l)).
          rewrite <- (rev_length _ (a :: l)). simpl in *. rewrite <- Heqrevl.
            trivial.
          inversion H.*)
Abort. (* TODO *)
(* end hide *)

Theorem take_drop : forall (A : Type) (n m : nat) (l : list A),
    take m (drop n l) = drop n (take (n + m) l).
(* begin hide *)
Proof.
  induction n as [| n']; intros.
    simpl. trivial.
    destruct l as [| h t]; simpl.
      rewrite take_nil. trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

(** *** [filter] *)

(** Napisz funkcję [filter], która zostawia na liście elementy, dla których
    funkcja [p] zwraca [true], a usuwa te, dla których zwraca [false]. *)

(* begin hide *)
Fixpoint filter {A : Type} (f : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if f h then h :: filter f t else filter f t
end.
(* end hide *)

Theorem filter_false : forall (A : Type) (l : list A),
    filter (fun _ => false) l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; trivial.
Qed.
(* end hide *)

Theorem filter_true : forall (A : Type) (l : list A),
    filter (fun _ => true) l = l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem filter_spec :
    forall (A : Type) (p : A -> bool) (l : list A) (x : A),
        p x = false -> ~ elem x (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    inversion 1.
    case_eq (p h); intro.
      inversion 1; subst.
        rewrite H0 in H. inversion H.
        unfold not in IHt. apply IHt with x; assumption.
      apply IHt. assumption.
Qed.
(* end hide *)

Theorem filter_app :
    forall (A : Type) (p : A -> bool) (l1 l2 : list A),
        filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    destruct (p h1); rewrite IHt1; trivial.
Qed.
(* end hide *)

Theorem filter_rev :
    forall (A : Type) (p : A -> bool) (l : list A),
        filter p (rev l) = rev (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    rewrite filter_app; simpl. destruct (p h); simpl.
      rewrite IHt. trivial.
      rewrite app_nil_r. rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem filter_comm :
    forall (A : Type) (f g : A -> bool) (l : list A),
        filter f (filter g l) = filter g (filter f l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    case_eq (f h); case_eq (g h); intros;
    simpl; repeat rewrite H; repeat rewrite H0; rewrite IHt; trivial.
Qed.
(* end hide *)

Theorem filter_idempotent :
    forall (A : Type) (f : A -> bool) (l : list A),
        filter f (filter f l) = filter f l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    case_eq (f h); simpl; intro; try rewrite H, IHt; trivial.
Qed.
(* end hide *)

Theorem filter_map :
    forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
        filter p (map f l) = map f (filter (fun x : A => p (f x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    destruct (p (f h)); simpl; rewrite IHt; trivial.
Qed.
(* end hide *)

Theorem filter_repeat_false :
    forall (A : Type) (p : A -> bool) (n : nat) (x : A),
        p x = false -> filter p (repeat n x) = [].
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    trivial.
    rewrite H. apply IHn'. assumption.
Qed.
(* end hide *)

Theorem filter_repeat_true :
    forall (A : Type) (p : A -> bool) (n : nat) (x : A),
        p x = true -> filter p (repeat n x) = repeat n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    trivial.
    rewrite H. rewrite IHn'; [trivial | assumption].
Qed.
(* end hide *)

Theorem filter_length :
    forall (A : Type) (p : A -> bool) (l : list A),
        length (filter p l) <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    trivial.
    destruct (p h).
      simpl. apply le_n_S. assumption.
      apply le_trans with (length t).
        assumption.
        apply le_S. apply le_n.
Qed.
(* end hide *)

Theorem filter_join :
    forall (A : Type) (p : A -> bool) (lla : list (list A)),
        join (map (filter p) lla) = filter p (join lla).
(* begin hide *)
Proof.
  induction lla as [| hl tl]; simpl.
    trivial.
    rewrite filter_app. rewrite IHtl. trivial.
Qed.
(* end hide *)

(** *** [takeWhile] i [dropWhile] *)

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

Theorem takeWhile_false : forall (A : Type) (l : list A),
    takeWhile (fun _ => false) l = [].
(* begin hide *)
Proof.
  destruct l; simpl; trivial.
Qed.
(* end hide *)

Theorem dropWhile_false : forall (A : Type) (l : list A),
    dropWhile (fun _ => false) l = l.
(* begin hide *)
Proof.
  destruct l; simpl; trivial.
Qed.
(* end hide *)

Theorem takeWhile_spec :
    forall (A : Type) (p : A -> bool) (l : list A) (x : A),
        elem x (takeWhile p l) -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    case_eq (p h); intro.
      rewrite H0 in H. inversion H; subst.
        trivial.
        apply IHt. assumption.
      rewrite H0 in H. inversion H.
Qed.
(* end hide *)

(* begin hide *)
(*Theorem takeWhile_spec' :
    forall (A : Type) (p : A -> bool) (l : list A) (x : A),
        elem x l -> ~ elem x (takeWhile p l) -> p x = false.
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    case_eq (p h); inversion H; subst; intro; rewrite H1 in H0.
      cut False. inversion 1. apply H0. constructor.
      apply IHt.
        assumption.
        apply elem_inv_tail with h. assumption.
      assumption.
      apply IHt.
        assumption.
        apply elem_inv_tail with h. assumption.
  *)
(* end hide *)  

Theorem dropWhile_spec :
    forall (A : Type) (p : A -> bool) (l : list A) (x : A),
        elem x l -> ~ elem x (dropWhile p l) -> p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    case_eq (p h); intro.
      rewrite H1 in H0. inversion H; subst.
        assumption.
        apply IHt; assumption.
      rewrite H1 in H0. contradiction H.
Qed.
(* end hide *)

Theorem takeWhile_idempotent :
    forall (A : Type) (p : A -> bool) (l : list A),
        takeWhile p (takeWhile p l) = takeWhile p l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    case_eq (p h); simpl; intro.
      rewrite H. rewrite IHt. trivial.
      trivial.
Qed.
(* end hide *)

Theorem dropWhile_idempotent :
    forall (A : Type) (p : A -> bool) (l : list A),
        dropWhile p (dropWhile p l) = dropWhile p l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    case_eq (p h); simpl; intro; [rewrite IHt | rewrite H]; trivial.
Qed.
(* end hide *)

Theorem takeWhile_repeat :
    forall (A : Type) (p : A -> bool) (n : nat) (x : A),
        p x = true -> takeWhile p (repeat n x) = repeat n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    trivial.
    rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem dropWhile_repeat :
    forall (A : Type) (p : A -> bool) (n : nat) (x : A),
        p x = true -> dropWhile p (repeat n x) = [].
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros.
    trivial.
    rewrite H, IHn'; trivial.
Qed.
(* end hide *)

(** *** [partition] *)

(** Napisz funkcję [partition], która dzieli listę [l] na listy
    elementów spełniających i niespełniających pewnego warunku boolowskiego. *)

(* begin hide *)
Fixpoint partition {A : Type} (p : A -> bool) (l : list A)
    : list A * list A :=
match l with
    | [] => ([], [])
    | h :: t => let (l1, l2) := partition p t in
        if p h then (h :: l1, l2) else (l1, h :: l2)
end.
(* end hide *)

Theorem partition_spec : forall (A : Type) (p : A -> bool) (l : list A),
    partition p l = (filter p l, filter (fun x => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    trivial.
    destruct (partition p t). destruct (p h); simpl; inversion IHt; trivial.
Qed.
(* end hide *)

(** *** [zip] *)

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

Theorem zip_nil_l :
  forall (A B : Type) (l : list B), zip (@nil A) l = [].
(* begin hide *)
Proof. simpl. trivial. Qed.
(* end hide *)

Theorem zip_nil_r :
  forall (A B : Type) (l : list A), zip l (@nil B) = [].
(* begin hide *)
Proof. destruct l; simpl; trivial. Qed.
(* end hide *)

Theorem zip_length :
  forall (A B : Type) (la : list A) (lb : list B),
    length (zip la lb) = min (length la) (length lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; intros.
    simpl. trivial.
    destruct lb as [| hb tb]; simpl.
      trivial.
      rewrite IHta. trivial.
Qed.
(* end hide *)

Theorem zip_not_rev :
  exists (A B : Type) (la : list A) (lb : list B),
    zip (rev la) (rev lb) <> rev (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists [true; false; true], [false; true].
  simpl. inversion 1.
Qed.
(* end hide *)

Theorem zip_head :
  forall (A B : Type) (la : list A) (lb : list B) (a : A) (b : B),
    head la = Some a -> head lb = Some b -> head (zip la lb) = Some (a, b).
(* begin hide *)
Proof.
  induction la as [| ha ta]; destruct lb as [| hb tb]; simpl; intros;
  inversion H; inversion H0; trivial.
Qed.
(* end hide *)

Theorem zip_tail :
  forall (A B : Type) (la ta : list A) (lb tb : list B),
    tail la = Some ta -> tail lb = Some tb ->
      tail (zip la lb) = Some (zip ta tb).
(* begin hide *)
Proof.
  induction la as [| ha ta']; simpl.
    inversion 1.
    destruct lb as [| hb tb']; simpl.
      inversion 2.
      do 2 inversion 1. trivial.
Qed.
(* end hide *)

Theorem zip_not_app :
  exists (A B : Type) (la la' : list A) (lb lb' : list B),
    zip (la ++ la') (lb ++ lb') <> zip la lb ++ zip la' lb'.
(* begin hide *)
Proof.
  exists bool, bool. exists [true], [false], [true; false; true], [].
  simpl. inversion 1.
Qed.
(* end hide *)

Theorem zip_map :
  forall (A B A' B' : Type) (f : A -> A') (g : B -> B')
  (la : list A) (lb : list B),
    zip (map f la) (map g lb) =
    map (fun x => (f (fst x), g (snd x))) (zip la lb).
(* begin hide *)
Proof.
  induction la; destruct lb; simpl; trivial.
    rewrite IHla. trivial.
Qed.
(* end hide *)

Theorem zip_not_filter :
  exists (A B : Type) (pa : A -> bool) (pb : B -> bool)
  (la : list A) (lb : list B),
    zip (filter pa la) (filter pb lb) <>
    filter (fun x => andb (pa (fst x)) (pb (snd x))) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (fun a : bool => if a then true else false). exists negb.
  exists [false; true], [false; true].
  simpl. inversion 1.
Qed.
(* end hide *)

Theorem zip_take :
  forall (A B : Type) (n : nat) (la : list A) (lb : list B),
    zip (take n la) (take n lb) = take n (zip la lb).
(* begin hide *)
Proof.
  induction n as [| n']; simpl.
    trivial.
    destruct la, lb; simpl; trivial.
      rewrite IHn'. trivial.
Qed.
(* end hide *)

Theorem zip_drop :
  forall (A B : Type) (n : nat) (la : list A) (lb : list B),
    zip (drop n la) (drop n lb) = drop n (zip la lb).
(* begin hide *)
Proof.
  induction n as [| n']; simpl.
    trivial.
    destruct la, lb; simpl; trivial.
      rewrite zip_nil_r. trivial.
Qed.
(* end hide *)

Theorem zip_elem :
  forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    elem (a, b) (zip la lb) -> elem a la /\ elem b lb.
(* begin hide *)
Proof.
  induction la; simpl.
    inversion 1.
    destruct lb; simpl; inversion 1; subst; simpl in *.
      split; constructor.
      destruct (IHla _ H2). split; right; assumption.
Qed.
(* end hide *)

Theorem zip_not_elem :
  exists (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
    elem a la /\ elem b lb /\ ~ elem (a, b) (zip la lb).
(* begin hide *)
Proof.
  exists bool, bool. exists true, false.
  exists [true; false], [true; false].
  simpl. repeat split.
    repeat constructor.
    repeat constructor.
    inversion 1; subst. inversion H2; subst. inversion H3.
Qed.
(* end hide *)

(** *** [intersperse] *)

(** Napisz funkcję [intersperse], który wstawia element [x : A] między
    każde dwa elementy z listy [l : list A]. *)

(* begin hide *)
Fixpoint intersperse {A : Type} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | [h] => [h]
    | h :: t => h :: x :: intersperse x t
end.
(* end hide *)

Theorem intersperse_length :
  forall (A : Type) (x : A) (l : list A),
    length (intersperse x l) = 2 * length l - 1.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl in *; trivial.
  Require Import Omega. rewrite IHl. omega.
Qed.
(* end hide *)

Theorem intersperse_app_last2 :
  forall (A : Type) (x y z : A) (l : list A),
    intersperse x (l ++ [y; z]) =
    intersperse x (l ++ [y]) ++ [x; z].
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl in *; trivial.
  rewrite IHl. trivial.
Qed.
(* end hide *)

Theorem intersperse_rev :
  forall (A : Type) (x : A) (l : list A),
    intersperse x (rev l) = rev (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl; trivial.
  simpl in *. rewrite <- IHl. 
  rewrite <- !app_assoc; simpl. apply intersperse_app_last2.
Qed.
(* end hide *)

(* begin hide *)
Theorem intersperse_app :
  forall (A : Type) (x : A) (l l' : list A),
    intersperse x (l ++ l') = intersperse x l ++ intersperse x l'.
Proof.
  induction l as [| h [| hh t]]; simpl.
    trivial.
    destruct l'; trivial.
    destruct l' as [| h' t']; simpl.
Abort.
(* end hide *)

Theorem intersperse_filter :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = false -> filter p (intersperse x l) = filter p l.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl; intros; trivial.
    rewrite H. simpl in IHl. rewrite (IHl H). trivial.
Qed.
(* end hide *)

Theorem intersperse_map :
  forall (A B : Type) (f : A -> B) (l : list A) (a : A) (b : B),
    f a = b -> intersperse b (map f l) = map f (intersperse a l).
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; simpl; trivial; intros.
  rewrite H. simpl in *. rewrite (IHl _ _ H). trivial.
Qed.
(* end hide *)

(* begin hide *)
(* TODO *)
Theorem intersperse_join :
  forall (A : Type) (x : A) (l : list (list A)),
    intersperse x (join l) = join (intersperse [x] (map (intersperse x) l)).
Proof.
  induction l as [| h [| h' t]]; simpl; trivial.
    rewrite !app_nil_r. trivial.
    simpl in *. rewrite <- IHl.
Abort.
(* end hide *)

(** *** [replicate] *)

(** Napsiz funkcję [replicate], która powiela dany element [n] razy, tworząc
    listę. *)

(* begin hide *)
Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
match n with
    | 0 => []
    | S n' => x :: replicate n' x
end.
(* end hide *)

Theorem replicate_length :
  forall (A : Type) (n : nat) (x : A),
    length (replicate n x) = n.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_plus_app :
  forall (A : Type) (n m : nat) (x : A),
    replicate (n + m) x = replicate n x ++ replicate m x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_rev :
  forall (A : Type) (n : nat) (x : A),
    rev (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; trivial.
  change [x] with (replicate 1 x).
  rewrite IHn', <- replicate_plus_app, plus_comm. simpl. trivial.
Qed.
(* end hide *)

Theorem replicate_elem :
  forall (A : Type) (n : nat) (x y : A),
    elem y (replicate n x) <-> n <> 0 /\ x = y.
(* begin hide *)
Proof.
  split.
    induction n as [| n']; simpl; inversion 1; subst.
      split; auto.
      destruct (IHn' H2). auto.
    intros [H H']. rewrite H'. destruct n as [| n'].
      contradiction H. trivial.
      simpl. left.
Qed.
(* end hide *)

Theorem replicate_map :
  forall (A B : Type) (f : A -> B) (n : nat) (x : A),
    map f (replicate n x) = replicate n (f x).
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intro; try rewrite IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_nth :
  forall (A : Type) (i n : nat) (x : A),
    i < n -> nth i (replicate n x) = Some x.
(* begin hide *)
Proof.
  induction i as [| i']; destruct n as [| n']; simpl; intros.
    omega.
    trivial.
    omega.
    rewrite IHi'.
      trivial.
      apply lt_S_n. assumption.
Qed.
(* end hide *)

Theorem replicate_head :
  forall (A : Type) (n : nat) (x : A),
    head (replicate (S n) x) = Some x.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem replicate_tail :
  forall (A : Type) (n : nat) (x : A),
    tail (replicate (S n) x) = Some (replicate n x).
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem replicate_take :
  forall (A : Type) (m n : nat) (x : A),
    take m (replicate n x) = replicate (min m n) x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct n as [| n']; simpl; intros; trivial.
  rewrite IHm'. trivial.
Qed.
(* end hide *)

Theorem replicate_drop :
  forall (A : Type) (m n : nat) (x : A),
    drop m (replicate n x) = replicate (n - m) x.
(* begin hide *)
Proof.
  induction m as [| m']; destruct n as [| n']; simpl; intros; trivial.
Qed.
(* end hide *)

Theorem replicate_filter_true :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = true -> filter p (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_filter_false :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = false -> filter p (replicate n x) = [].
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_takeWhile_true :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = true -> takeWhile p (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_takeWhile_false :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = false -> takeWhile p (replicate n x) = [].
(* begin hide *)
Proof.
  destruct n as [| n']; simpl; intros; try rewrite H; trivial.
Qed.
(* end hide *)

Theorem replicate_dropWhile_true :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = true -> dropWhile p (replicate n x) = [].
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intros; try rewrite H, IHn'; trivial.
Qed.
(* end hide *)

Theorem replicate_dropWhile_false :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A),
    p x = false -> dropWhile p (replicate n x) = replicate n x.
(* begin hide *)
Proof.
  destruct n as [| n']; simpl; intros; try rewrite H; trivial.
Qed.
(* end hide *)

Theorem replicate_zip :
  forall (A B : Type) (n m : nat) (a : A) (b : B),
    zip (replicate n a) (replicate m b) = replicate (min n m) (a, b).
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'];
  simpl; intros; try rewrite IHn'; trivial.
Qed.
(* end hide *)

(** *** [zipWith] *)

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

Theorem zipWith_spec :
  forall (A B C : Type) (f : A -> B -> C) (la : list A) (lb : list B),
    zipWith f la lb = map (fun x => f (fst x) (snd x)) (zip la lb).
(* begin hide *)
Proof.
  induction la as [| ha ta]; destruct lb as [| hb tb];
  simpl; intros; try rewrite IHta; trivial.
Qed.
(* end hide *)

(** *** [unzip] (odtąd TODO!) *)

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

Theorem zip_unzip :
  forall (A B : Type) (l : list (A * B)),
    zip (fst (unzip l)) (snd (unzip l)) = l.
(* begin hide *)
Proof.
  induction l as [| [ha hb] t]; simpl.
    trivial.
    destruct (unzip t). simpl in *. rewrite IHt. trivial.
Qed.
(* end hide *)

Theorem unzip_zip :
  exists (A B : Type) (la : list A) (lb : list B),
    unzip (zip la lb) <> (la, lb).
(* begin hide *)
Proof.
  exists unit, unit, [], [tt]. simpl. inversion 1.
Qed.
(* end hide *)

(** *** [find] *)

(** Napisz funkcję [find], która znajduje pierwszy element na liście,
    który spełnia podany predykat boolowski. Podaj i udowodnij jej
    specyfikację. *)

(* begin hide *)
Function find {A : Type} (p : A -> bool) (l : list A) : option A :=
match l with
    | [] => None
    | h :: t => if p h then Some h else find p t
end.
(* end hide *)

Theorem find_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    (exists x : A, find p l = Some x) <->
    (exists (h : A) (t : list A), filter p l = h :: t).
(* begin hide *)
Proof.
  split.
    induction l as [| h t]; simpl; destruct 1.
      congruence.
      destruct (p h).
        exists h, (filter p t). trivial.
        edestruct IHt.
          exists x. assumption.
          destruct H0 as [t0 Ht0]. exists x0, t0. assumption.
    induction l as [| h t]; simpl; destruct 1 as [x [l H]].
      inversion H.
      destruct (p h).
        exists h. trivial.
        edestruct IHt.
          exists x, l. assumption.
          exists x0. assumption.
Qed.
(* end hide *)

(** *** [findIndex] *)

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

Theorem findIndex_spec :
  forall (A : Type) (p : A -> bool) (l : list A) (n : nat),
    findIndex p l = Some n -> exists x : A, nth n l = Some x /\ p x = true.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    inversion 1.
    case_eq (p h); intros.
      inversion H0; subst; clear H0; simpl. exists h. auto. 
      case_eq (findIndex p t); intros.
        rewrite H1 in H0. inversion H0; subst; clear H0.
          destruct (IHt _ H1). exists x. simpl. assumption.
        rewrite H1 in H0. inversion H0.
Restart.
  intros A p l. functional induction @findIndex A p l;
  intros; inversion H; subst; clear H; simpl in *.
    exists h. auto.
    destruct (IHo _ e1) as [x H]. exists x. assumption.
Qed.
(* end hide *)

(** *** [findIndices] *)

(** Napisz funkcję [findIndices], która znajduje indeksy wszystkich elemtnów
    listy, które spełniają predykat boolowski [p]. *)

(* begin hide *)
Definition findIndices {A : Type} (p : A -> bool) (l : list A) : list nat :=
  (fix f (l : list A) (n : nat) : list nat :=
  match l with
      | [] => []
      | h :: t => if p h then n :: f t (S n) else f t (S n)
  end) l 0.

(*Theorem findIndices_spec :
  forall (A : Type) (p : A -> bool) (l : list A) (indices : list nat),
    findIndices p l = indices -> forall n : nat, elem n indices ->*)

(* end hide *)

(** *** Zwijanie *)

Fixpoint foldr {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : B :=
match l with
    | [] => b
    | h :: t => f h (foldr f b t)
end.

Fixpoint foldl {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : A :=
match l with
    | [] => a
    | h :: t => foldl f (f a h) t
end.

(** Nie będę na razie tłumaczył, jaka ideologia stoi za [foldr] i [foldl].
    Napiszę o tym później, a na razie porcja zadań.

    Zaimplementuj za pomocą [foldr] lub [foldl] następujące funkcje:
    [length], [app], [rev], [map], [join], [filter], [takeWhile],
    [dropWhile].

    Udowodnij, że zdefiniowane przez ciebie funkcje pokrywają się ze
    swoimi klasycznymi odpowiednikami. *)

(* begin hide *)
(* Reszta polecenia: [repeat], [nth], [take], [drop] *)

Functional Scheme foldr_ind := Induction for foldr Sort Prop.
Functional Scheme foldl_ind := Induction for foldl Sort Prop.

Definition lengthF {A : Type} (l : list A) : nat :=
    foldr (fun _ => S) 0 l.

Definition appF {A : Type} (l1 l2 : list A) : list A :=
    foldr (@cons A) l2 l1.

Definition revF {A : Type} (l : list A) : list A :=
    foldr (fun h t => t ++ [h]) [] l.

Definition revF' {A : Type} (l : list A) : list A :=
    foldl (fun t h => h :: t) [] l.

Definition mapF {A B : Type} (f : A -> B) (l : list A) : list B :=
    foldr (fun h t => f h :: t) [] l.

Definition joinF {A : Type} (l : list (list A)) : list A :=
    foldr app [] l.

Definition filterF {A : Type} (p : A -> bool) (l : list A) : list A :=
    foldr (fun h t => if p h then h :: t else t) [] l.

Definition takeWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
    foldr (fun h t => if p h then h :: t else []) [] l.

(*Definition dropWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
    foldr (fun h t => if p h then t else h :: t) [] l.*)

(*Definition dropWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
    foldl (fun t h => if p h then t else h :: t) [] l.*)

Ltac solve_fold := intros;
match goal with
    | |- context [@foldr ?A ?B ?f ?a ?l] =>
        functional induction @foldr A B f a l; simpl; trivial;
        match goal with
            | H : ?x = _ |- context [?x] => rewrite ?H; auto
        end
    | |- context [@foldl ?A ?B ?f ?a ?l] =>
        functional induction @foldl A B f a l; simpl; trivial;
        match goal with
            | H : ?x = _ |- context [?x] => rewrite ?H; auto
        end
end.

(* end hide *)

Theorem lengthF_spec : forall (A : Type) (l : list A),
    lengthF l = length l.
(* begin hide *)
Proof.
  unfold lengthF; induction l as [| h t]; simpl.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold lengthF. solve_fold.
Qed.
(* end hide *)

Theorem appF_spec : forall (A : Type) (l1 l2 : list A),
    appF l1 l2 = l1 ++ l2.
(* begin hide *)
Proof.
  unfold appF; induction l1 as [| h1 t1]; simpl; intros.
    trivial.
    rewrite IHt1. trivial.
Restart.
  intros. unfold appF. solve_fold.
Qed.
(* end hide *)

Theorem revF_spec : forall (A : Type) (l : list A),
    revF l = rev l.
(* begin hide *)
Proof.
  unfold revF; induction l as [| h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold revF. solve_fold.
Qed.
(* end hide *)

(* begin hide *)
Theorem revF'_spec : forall (A : Type) (l : list A),
    revF' l = rev l.
Proof.
  unfold revF'. intros. replace (rev l) with (rev l ++ []).
    remember [] as acc. clear Heqacc. generalize dependent acc.
    induction l as [| h t]; simpl; intros; subst.
      trivial.
      rewrite IHt. rewrite <- app_cons2. trivial.
    apply app_nil_r.
Qed.
(* end hide *)

Theorem mapF_spec : forall (A B : Type) (f : A -> B) (l : list A),
    mapF f l = map f l.
(* begin hide *)
Proof.
  unfold mapF; induction l as [| h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold mapF. solve_fold.
Qed.
(* end hide *)

Theorem joinF_spec : forall (A : Type) (l : list (list A)),
    joinF l = join l.
(* begin hide *)
Proof.
  unfold joinF; induction l as [| h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold joinF. solve_fold.
Qed.
(* end hide *)

Theorem filterF_spec : forall (A : Type) (p : A -> bool) (l : list A),
    filterF p l = filter p l.
(* begin hide *)
Proof.
  unfold filterF; induction l as [| h t].
    simpl. trivial.
    simpl. rewrite IHt. trivial.
Restart.
  intros. unfold filterF. solve_fold.
Qed.
(* end hide *)

Theorem takeWhileF_spec : forall (A : Type) (p : A -> bool) (l : list A),
    takeWhileF p l = takeWhile p l.
(* begin hide *)
Proof.
  unfold takeWhileF; induction l as [| h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold takeWhileF. solve_fold.
Qed.
(* end hide *)

(* begin hide *)
(* Theorem dropWhileF_spec : forall (A : Type) (p : A -> bool) (l : list A),
    dropWhileF p l = dropWhile p l.
(* begin hide *)
Proof.
  unfold dropWhileF; intros. remember [] as acc.
  generalize dependent acc.
  induction l as [| h t]; simpl; intros.
    trivial.
    destruct (p h).
      rewrite IHt; trivial.
      rewrite IHt.
Qed. *)
(* end hide *)

(** *** Dziwne (TODO) *)

Fixpoint revapp {A : Type} (l1 l2 : list A) : list A :=
match l1 with
    | [] => l2
    | h :: t => revapp t (h :: l2)
end.

Definition app' {A : Type} (l1 l2 : list A) : list A :=
  revapp (revapp l1 []) l2.

Theorem revapp_spec :
  forall (A : Type) (l1 l2 : list A),
    revapp l1 l2 = rev l1 ++ l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros; trivial.
    rewrite IHt, <- app_assoc. cbn. trivial.
Qed.
(* end hide *)

Theorem app'_spec :
  forall (A : Type) (l1 l2 : list A),
    l1 ++ l2 = app' l1 l2.
(* begin hide *)
Proof.
  unfold app'. intros. rewrite !revapp_spec, app_nil_r, rev_inv. trivial.
Qed.
(* end hide *)


(** *** Niestandardowe reguły indukcyjne *)

(** Wyjaśnienia nadejdą już wkrótce. *)

Fixpoint list_ind_2
  (A : Type) (P : list A -> Prop) (H0 : P []) (H1 : forall x : A, P [x])
  (H2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
  (l : list A) : P l.
(* begin hide *)
Proof.
  destruct l as [| x [| y l]]; simpl; auto.
  apply H2. apply list_ind_2; auto.
Qed.
(* end hide *)

Theorem list_ind_rev :
  forall (A : Type) (P : list A -> Prop)
    (Hnil : P []) (Hsnoc : forall (h : A) (t : list A), P t -> P (t ++ [h]))
      (l : list A), P l.
(* begin hide *)
Proof.
  intros. cut (forall l : list A, P (rev l)); intro.
    specialize (H (rev l)). rewrite <- rev_inv. assumption.
    induction l0 as [| h t]; simpl.
      assumption.
      apply Hsnoc. assumption.
Qed.
(* end hide *)

Theorem list_ind_app_l :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l' ++ l))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    assumption.
    apply (IH _ [h]). assumption.
Qed.
(* end hide *)

Theorem list_ind_app_r :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (IH : forall l l' : list A, P l -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t] using list_ind_rev; simpl.
    assumption.
    apply (IH t [h]). assumption.
Qed.
(* end hide *)

Theorem list_ind_app :
  forall (A : Type) (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (IH : forall l l' : list A, P l -> P l' -> P (l ++ l'))
    (l : list A), P l.
(* begin hide *)
Proof.
  induction l as [| h t]; simpl.
    assumption.
    apply (IH [h] t); auto.
Qed.
(* end hide *)