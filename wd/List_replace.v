Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Require Import CoqBookPL.wd.Option.

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

Lemma replace_rev_aux :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace l n x = replace (rev l) (length l - S n) x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n'].
      Check replace_length_lt.
      destruct (replace t n' x) eqn: Heq.
Qed.
(* end hide *)

Lemma replace_rev :
  forall (A : Type) (l l' : list A) (n : nat) (x : A),
    replace (rev l) n x = omap rev (replace l (length l - n) x).
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