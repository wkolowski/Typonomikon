Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(*Require Import CoqBookPL.wd.Option.*)

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

Lemma isEmpty_replace_Some :
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

Lemma replace_length :
  forall (A : Type) (l : list A) (x : A),
    replace l (length l) x = None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
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

(*Require Import CoqBookPL.wd.Opcje.*)

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
    Search (S _ <> _).
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
    if S n <=? length l
    then Some (take n l ++ x :: drop (S n) l)
    else None.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
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
  apply leb_correct in H. rewrite H. reflexivity.
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
            rewrite length_rev. unfold lt. omega.
Qed.
(* end hide *)

Definition omap {A B: Type} (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Lemma replace_rev :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
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

(* TODO: join, bind *)

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

Lemma nth_replace :
  forall (A : Type) (l l' : list A) (n m : nat) (x : A),
    replace l n x = Some l' ->
      nth m l' =
      if n =? m then Some x else nth m l.
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
      if n =? length l - 1
      then init l
      else
        match init l with
            | None => None
            | Some i => replace i n x
        end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    rewrite <- minus_n_O. destruct (n =? length t) eqn: Heq.
      apply beq_nat_true in Heq. subst. destruct t; cbn in *.
        inv H.
Abort.
(* end hide *)

(* TODO: uncons, unsnoc *)
(*
Lemma replace_insert :
  forall (A : Type) (l l' : list A) (n : nat) (x y : A),
    match insert l n x with
        | None => True
        | Some l' => replace l' n y = insert l n y
    end.
(* begin hide *)
Proof.
Abort.
(* end hide *)
*)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    
    destruct n as [| n'].
      
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)
*)