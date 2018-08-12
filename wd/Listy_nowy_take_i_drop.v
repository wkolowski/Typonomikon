Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(** ** [take] *)

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
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite ?(IHt _ (lt_S_n _ _ H)). reflexivity.
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
(* begin hide *)
Proof. Print take.
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
    
Qed.
(* end hide *)
*)

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

Lemma take_insert_lt :
  forall (A : Type) (l : list A) (n m : nat) (x : A),
    m < n ->
      take m (insert l n x) =
      if isEmpty l
      then if beq_nat 0 m then [] else [x]
      else take m l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct m; reflexivity.
    destruct n as [| n']; cbn.
      destruct m as [| m']; cbn.
        reflexivity.
        inversion H.
      destruct m as [| m']; cbn.
        reflexivity.
        rewrite IHt.
          destruct t, m'; cbn.
            1,3-4: reflexivity.
(* TODO *)
Abort.
(* end hide *)

(* TODO: take_remove *)

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
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite <- take_length, <- H. reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      specialize (H 1). cbn in H. inversion H.
      pose (H' := H 1). cbn in H'. inversion H'; subst; clear H'.
        rewrite (IHt1 t2).
          reflexivity.
          intros. specialize (H (S n)). cbn in H.
            inversion H. reflexivity.
Restart.
  intros. specialize (H (max (length l1) (length l2))).
  rewrite ?take_length' in H.
    assumption.
    apply Max.le_max_r.
    apply Max.le_max_l.
Qed.
(* end hide *)

(* TODO: insert_take, insert_drop, zip, unzip, zipWith, intersperse *)

(** ** [drop] *)

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
  induction l1 as [| h t]; cbn; intros.
    inversion H. rewrite drop_0. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      apply le_S_n in H. apply (IHt _ _ H).
Restart.
  intros. rewrite <- Nat.sub_0_le in H.
  rewrite drop_app, H, drop_0. reflexivity.
Qed.
(* end hide *)

Lemma drop_app_r :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    length l1 < n -> drop n (l1 ++ l2) = drop (n - length l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite <- minus_n_O. reflexivity.
    destruct n as [| n']; cbn.
      inversion H.
      apply lt_S_n in H. apply (IHt _ _ H).
Restart.
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

(* TODO: drop_join, drop_bind *)

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
    rewrite nth_nil. reflexivity.
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

(* TODO: init_drop *)

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

(* TODO: insert_drop *)

(* TODO: zip, unzip, zipWith, intersperse *)

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

(** *** Dualność [take] i [drop] *)

(* TODO: napisz coś *)

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
  (*TODO: drop_rev_aux using rewriting *)
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
  forall (A : Type) (l : list A) (n : nat),
    drop n (rev l) = rev (take (length l - n) l).
(* begin hide *)
Proof.
  intros. rewrite drop_rev_aux, !rev_inv. reflexivity.
Qed.
(* end hide *)

Lemma rev_drop :
  forall (A : Type) (l : list A) (n : nat),
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
        inversion H; subst. rewrite drop_0. reflexivity.
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



(*
Lemma removeFirst_take' :
  forall (A : Type) (p : A -> bool) (n : nat) (x : A) (l l' : list A),
    removeFirst p (take' n l) = Some (x, l') ->
      removeFirst p l = Some (x, l' ++ drop n l).
Proof.
  intros A p n x l. revert n x.
  functional induction @removeFirst A p l;
  destruct n as [| n']; cbn; intros; inv H; rewrite e0 in H1; inv H1.
    admit.
    destruct (removeFirst p (take' n' t)) eqn: Heq.
      admit.
      inv H0.
    destruct (removeFirst p (take' n' t)) eqn: Heq.
      destruct p0. inv H0. rewrite (IHo _ _ _ Heq) in e1. inv e1.
        cbn. reflexivity.
      inv H0.
Admitted.
(* end hide *)

*)

(* Oryginalne take i drop: 2101-2804 = 703 linijki *)


(** ** [splitAt] *)

(** Zdefiniuj przez rekursję funkcję [splitAt], która spełnia poniższą
    specyfikację. *)

(* begin hide *)
Fixpoint splitAt
  {A : Type} (n : nat) (l : list A) {struct l} : list A * list A :=
match l, n with
    | [], _ => ([], [])
    | _, 0 => ([], l)
    | h :: t, S n' =>
        let '(l1, l2) := splitAt n' t in (h :: l1, l2)
end.
(* end hide *)

Lemma splitAt_spec :
  forall (A : Type) (l : list A) (n : nat),
    splitAt n l = (take n l, drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHt. reflexivity.
Qed.
(* end hide *)

(** predykatowe rzeczy *)

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

Lemma incl_take :
  forall (A : Type) (l : list A) (n : nat),
    incl (take n l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_take in H. assumption.
Qed.
(* end hide *)

Lemma incl_drop :
  forall (A : Type) (l : list A) (n : nat),
    incl (drop n l) l.
(* begin hide *)
Proof.
  unfold incl; intros. apply elem_drop in H. assumption.
Qed.
(* end hide *)