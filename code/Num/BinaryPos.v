Require Import Recdef Bool.

(** [I'] to 1, [O k] to 2k, zaś [I k] to 2k + 1. *)
Inductive Pos : Set :=
| I' : Pos
| O : Pos -> Pos
| I : Pos -> Pos.

Definition One : Pos := I'.

Fixpoint toNat (n : Pos) : nat :=
match n with
| I' => 1
| O n' => 2 * toNat n'
| I n' => 1 + 2 * toNat n'
end.

Compute toNat (O (O (O I'))).

Function succ (p : Pos) : Pos :=
match p with
| I'   => O I'
| O p' => I p'
| I p' => O (succ p')
end.

Compute succ (I (I (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (succ (I (I (I I')))).

Function pred (p : Pos) : Pos :=
match p with
| I'   => I'
| O I' => I'
| O p' => I (pred p')
| I p' => O p'
end.

Compute pred (I (I (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (pred (I (I (I I')))).

Compute pred (I (O I')).
Compute toNat (I (O I')).
Compute toNat (pred (I (O I'))).

Function pred' (p : Pos) : option Pos :=
match p with
| I'   => None
| O I' => Some I'
| O p' => option_map O (pred' p')
| I p' => Some (O p')
end.

Compute pred' (I (I (I I'))).
Compute toNat (I (I (I I'))).
Compute option_map toNat (pred' (I (I (I I')))).

Function add (p1 p2 : Pos) : Pos :=
match p1, p2 with
| I'   , _     => succ p2
| _    , I'     => succ p1
| O p1', O p2' => O (add p1' p2')
| O p1', I p2' => I (add p1' p2')
| I p1', O p2' => I (add p1' p2')
| I p1', I p2' => O (succ (add p1' p2'))
end.

Compute add (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute toNat (add (I (I (I I'))) (I (O (I I')))).

Function add' (p1 p2 : Pos) : Pos :=
match p1 with
| I'    => succ p2
| O p1' => add' p1' (add' p1' p2)
| I p1' => succ (add' p1' (add' p1' p2))
end.

Compute add' (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute toNat (add' (I (I (I I'))) (I (O (I I')))).

Function sub (p1 p2 : Pos) : option Pos :=
match p1, p2 with
| I'   , _     => None
| O p1', I'    => pred' p1
| O p1', O p2' => option_map O (sub p1' p2')
| O p1', I p2' => option_map (fun p => pred (O p)) (sub p1' p2')
| I p1', I'    => Some (O p1')
| I p1', O p2' => option_map I (sub p1' p2')
| I p1', I p2' => option_map O (sub p1' p2')
end.

Compute sub (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute option_map toNat (sub (I (I (I I'))) (I (O (I I')))).

Function sub' (p1 p2 : Pos) : Pos :=
match p2 with
| I'    => pred p1
| O p2' => sub' (sub' p1 p2') p2'
| I p2' => pred (sub' (sub' p1 p2') p2')
end.

Compute sub' (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute toNat (sub' (I (I (I I'))) (I (O (I I')))).

Function double' (p : Pos) : Pos :=
match p with
| I'   => O I'
| O p' => O (double' p')
| I p' => O (succ (double' p'))
end.

Definition double (p : Pos) := O p.

Compute double (I (I (I I'))).
Compute toNat (I (I (O I'))).
Compute toNat (double (I (I (O I')))).

Function mul_tail (p1 p2 : Pos) : Pos :=
match p1 with
| I'    => p2
| O p1' => mul_tail p1' (O p2)
| I p1' => add p2 (mul_tail p1' (O p2))
end.

Compute mul_tail (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute toNat (mul_tail (I (I (I I'))) (I (O (I I')))).

Function mul (p1 p2 : Pos) : Pos :=
match p1 with
| I'    => p2
| O p1' => O (mul p1' p2)
| I p1' => add p2 (O (mul p1' p2))
end.

Compute mul (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute toNat (mul (I (I (I I'))) (I (O (I I')))).

(* Function pow (p1 p2 : Pos) : Pos :=
match p2 with
end. *)

Function compare (p1 p2 : Pos) : comparison :=
match p1, p2 with
| I'    , I'     => Eq
| I'    , _     => Lt
| _    , I'     => Gt
| O p1', O p2' => compare p1' p2'
| O p1', I p2' =>
  match compare p1' p2' with
  | Lt => Lt
  | Eq => Lt
  | Gt => Gt
  end
| I p1', O p2' =>
  match compare p1' p2' with
  | Lt => Lt
  | Eq => Gt
  | Gt => Gt
  end
| I p1', I p2' => compare p1' p2'
end.

Compute compare (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute Nat.compare (toNat (I (I (I I')))) (toNat (I (O (I I')))).

Definition eqb (p1 p2 : Pos) : bool :=
match compare p1 p2 with
| Eq => true
| _  => false
end.

Definition leb (p1 p2 : Pos) : bool :=
match compare p1 p2 with
| Gt => false
| _  => true
end.

Definition ltb (p1 p2 : Pos) : bool :=
match compare p1 p2 with
| Lt => true
| _  => false
end.

Definition max (p1 p2 : Pos) : Pos :=
match compare p1 p2 with
| Lt => p2
| _  => p1
end.

Definition min (p1 p2 : Pos) : Pos :=
match compare p1 p2 with
| Lt => p1
| _  => p2
end.

(* Function min' (p1 p2 : Pos) : Pos :=
match p1, p2 with
| I'   , _     => p2
| _    , I'    => p1
| O p1', O p2' => O (min' p1' p2')
| O p1', I p2' => 
| I p1', O p2' => 
| I p1', I p2' => I (min' p1' p2')
end. *)

Function odd (p : Pos) : bool :=
match p with
| I'   => true
| O _ => false
| I _ => true
end.

Definition even (p : Pos) : bool := negb (odd p).

Lemma pred_succ :
  forall p : Pos,
    pred (succ p) = p.
Proof.
  induction p; cbn.
  1-2: reflexivity.
  rewrite IHp. destruct p; cbn; reflexivity.
Qed.

Lemma add_I'_l :
  forall p : Pos,
    add I' p = succ p.
Proof.
  reflexivity.
Qed.

Lemma add_I'_r :
  forall p : Pos,
    add p I' = succ p.
Proof.
  destruct p; cbn; reflexivity.
Qed.

Lemma add_succ_l :
  forall p1 p2 : Pos,
    add (succ p1) p2 = succ (add p1 p2).
Proof.
  intros p1.
  functional induction succ p1; cbn; intros.
  - destruct p2; cbn; reflexivity.
  - destruct p2; cbn; reflexivity.
  - destruct p2; cbn; rewrite ?IHp; reflexivity.
Qed.

Lemma add_comm :
  forall p1 p2 : Pos,
    add p1 p2 = add p2 p1.
Proof.
  intros p1 p2.
  functional induction add p1 p2
  ; cbn; rewrite ?IHp; try reflexivity.
  rewrite add_I'_r; reflexivity.
Qed.

Lemma add_succ_r :
  forall p1 p2 : Pos,
    add p1 (succ p2) = succ (add p1 p2).
Proof.
  intros p1 p2.
  rewrite add_comm, add_succ_l, <- add_comm.
  reflexivity.
Qed.

Lemma add_assoc :
  forall p1 p2 p3 : Pos,
    add (add p1 p2) p3 = add p1 (add p2 p3).
Proof.
  intros p1 p2.
  functional induction add p1 p2; cbn; intros p3.
  - rewrite add_succ_l; reflexivity.
  - rewrite add_succ_l, add_succ_r. reflexivity.
  - destruct p3; cbn; rewrite ?IHp; reflexivity.
  - destruct p3; cbn; rewrite ?add_succ_l, ?add_succ_r, ?IHp; reflexivity.
  - destruct p3; cbn; rewrite ?add_succ_l, ?add_succ_r, ?IHp; reflexivity.
  - destruct p3; cbn; rewrite ?add_succ_l, ?add_succ_r, ?IHp; reflexivity.
Qed.

Lemma add_diag :
  forall p : Pos,
    add p p = O p.
Proof.
  induction p as [| p' | p']
  ; cbn; rewrite ?IHp'; reflexivity.
Qed.

Lemma add_O_l :
  forall p1 p2 : Pos,
    add (O p1) p2 = add p1 (add p1 p2).
Proof.
  intros p1 p2.
  rewrite <- add_diag, add_assoc.
  reflexivity.
Qed.

Lemma add_O_r :
  forall p1 p2 : Pos,
    add p1 (O p2) = add p2 (add p2 p1).
Proof.
  intros p1 p2.
  rewrite <- add_diag, add_comm, <- add_assoc.
  reflexivity.
Qed.

Lemma add'_add :
  forall p1 p2 : Pos,
    add' p1 p2 = add p1 p2.
Proof.
  intros p1 p2.
  functional induction add' p1 p2; cbn.
  - reflexivity.
  - rewrite IHp0, IHp. destruct p2.
    + rewrite add_I'_r, add_succ_r, add_diag; cbn; reflexivity.
    + rewrite <- !add_diag, add_assoc. f_equal.
      rewrite <- add_assoc, add_comm. reflexivity.
    + change (I p2) with (succ (O p2)).
      change (I (add p1' p2)) with (succ (O (add p1' p2))).
      rewrite !add_succ_r; f_equal.
      rewrite <- !add_diag, add_assoc; f_equal.
      rewrite (add_comm _ (add p1' _)), add_assoc. reflexivity.
  - rewrite IHp0, IHp. destruct p2.
    + rewrite add_I'_r, add_succ_r, add_diag; cbn; reflexivity.
    + change (I _) with (succ (O (add p1' p2))).
      rewrite <- !add_diag, add_assoc. do 2 f_equal.
      rewrite <- add_assoc, add_comm. reflexivity.
    + change (I p2) with (succ (O p2)).
      rewrite <- !add_diag, !add_succ_r, !add_succ_l. do 2 f_equal.
      rewrite (add_comm _ (add p1' _)), !add_assoc, (add_comm p2 _), !add_assoc.
      reflexivity.
Qed.

Lemma mul_I'_r :
  forall p : Pos,
    mul p I' = p.
Proof.
  induction p; cbn; rewrite ?IHp; reflexivity.
Qed.

Lemma mul_O_r :
  forall p1 p2 : Pos,
    mul p1 (O p2) = O (mul p1 p2).
Proof.
  intros p1 p2.
  functional induction mul p1 p2; cbn; rewrite ?IHp; reflexivity.
Qed.

Lemma mul_I_r :
  forall p1 p2 : Pos,
    mul p1 (I p2) = add p1 (O (mul p1 p2)).
Proof.
  intros p1 p2.
  functional induction mul p1 p2; cbn; rewrite ?IHp.
  1-2: reflexivity.
  rewrite <- add_assoc, (add_comm p2 p1'), add_assoc; reflexivity.
Qed.

Lemma mul_comm :
  forall p1 p2 : Pos,
    mul p1 p2 = mul p2 p1.
Proof.
  intros p1 p2.
  functional induction mul p1 p2; cbn in *.
  - rewrite mul_I'_r; reflexivity.
  - rewrite mul_O_r, IHp; reflexivity.
  - rewrite mul_I_r, IHp; reflexivity.
Qed.

Lemma O_add :
  forall p1 p2 : Pos,
    O (add p1 p2) = add (O p1) (O p2).
Proof.
  reflexivity.
Qed.

Lemma mul_succ_l :
  forall p1 p2 : Pos,
    mul (succ p1) p2 = add p2 (mul p1 p2).
Proof.
  intros p1 p2.
  functional induction (succ p1); cbn.
  - rewrite add_diag; reflexivity.
  - reflexivity.
  - rewrite IHp, O_add, <- add_diag, add_assoc; reflexivity.
Qed.

Lemma mul_succ_r :
  forall p1 p2 : Pos,
    mul p1 (succ p2) = add p1 (mul p1 p2).
Proof.
  intros p1 p2.
  rewrite mul_comm, mul_succ_l, <- mul_comm.
  reflexivity.
Qed.

Lemma mul_add_l :
  forall p1 p2 p3 : Pos,
    mul (add p1 p2) p3 = add (mul p1 p3) (mul p2 p3).
Proof.
  intros p1 p2; functional induction add p1 p2; intros p3.
  - rewrite mul_succ_l; reflexivity.
  - rewrite mul_succ_l, add_comm; cbn; reflexivity.
  - cbn; rewrite IHp; reflexivity.
  - rewrite mul_equation, (mul_equation (O p1')), (mul_equation (I p2')).
    rewrite (add_comm p3 (O (mul p2' p3))), <- add_assoc, <- O_add, add_comm, IHp.
    reflexivity.
  - cbn; rewrite IHp, O_add, add_assoc; reflexivity.
  - cbn.
    rewrite add_assoc, (add_comm (O _)), !add_assoc, <- O_add,
            mul_succ_l, O_add, <- add_diag, add_assoc, IHp, (add_comm (mul _ _))
    ; reflexivity.
Qed.

Lemma mul_add_r :
  forall p1 p2 p3 : Pos,
    mul p1 (add p2 p3) = add (mul p1 p2) (mul p1 p3).
Proof.
  intros p1 p2 p3.
  rewrite mul_comm, mul_add_l, <- (mul_comm p1 _), <- (mul_comm p3 _).
  reflexivity.
Qed.

Lemma mul_assoc :
  forall p1 p2 p3 : Pos,
    mul (mul p1 p2) p3 = mul p1 (mul p2 p3).
Proof.
  intros p1 p2; functional induction mul p1 p2; intros p3; cbn.
  - reflexivity.
  - rewrite IHp; reflexivity.
  - rewrite mul_add_l; cbn; rewrite IHp; reflexivity.
Qed.

Lemma compare_refl :
  forall p : Pos,
    compare p p = Eq.
Proof.
  induction p; cbn; rewrite ?IHp; reflexivity.
Qed.

Lemma compare_refl_conv :
  forall p1 p2 : Pos,
    compare p1 p2 = Eq -> p1 = p2.
Proof.
  intros p1 p2.
  functional induction compare p1 p2
  ; intros [=]; rewrite ?IHc; auto.
Qed.

Lemma compare_spec :
  forall p1 p2 : Pos,
    CompareSpecT (p1 = p2) (compare p2 p1 = Gt) (compare p2 p1 = Lt) (compare p1 p2).
Proof.
  intros p1 p2.
  functional induction compare p1 p2; cbn.
  4-11: destruct IHc as [-> | -> | ->]; constructor; rewrite ?compare_refl; intuition congruence.
  - constructor; reflexivity.
  - constructor. destruct p2; cbn; intuition.
  - constructor. destruct p1; cbn; intuition.
Qed.

Lemma compare_spec' :
  forall p1 p2 : Pos,
    CompareSpecT
      (p1 = p2)
      (compare p1 p2 = Lt /\ compare p2 p1 = Gt)
      (compare p1 p2 = Gt /\ compare p2 p1 = Lt)
      (compare p1 p2).
Proof.
  intros p1 p2.
  functional induction compare p1 p2; cbn.
  4-11: destruct IHc as [-> | [? ->] | [? ->]]; constructor
  ; rewrite ?compare_refl in *; intuition congruence.
  - constructor; reflexivity.
  - constructor. destruct p2; cbn; intuition.
  - constructor. destruct p1; cbn; intuition.
Qed.

Inductive le : Pos -> Pos -> Prop :=
| le_I' : forall p : Pos, le I' p
| le_O  : forall p1 p2 : Pos, le p1 p2 -> le (O p1) (O p2)
| le_I  : forall p1 p2 : Pos, le p1 p2 -> le (I p1) (I p2)
| le_OI : forall p : Pos, le (O p) (I p).

#[global] Hint Constructors le : core.

Lemma le_trans :
  forall p1 p2 p3 : Pos,
    le p1 p2 -> le p2 p3 -> le p1 p3.
Proof.
  intros p1 p2 p3 H12 H23; revert p3 H23.
  induction H12; intros.
  - constructor.
  - inversion H23; subst; clear H23.
    + constructor; apply IHle; assumption.
Restart.
  intros p1 p2; revert p1.
  induction p2 as [| p2' | p2']; intros p1 p2 H13 H23.
  - inversion H13; subst; constructor.
  - inversion H13; inversion H23; subst; clear H13 H23.
    + constructor.
    + constructor.
    + constructor. apply IHp2'; assumption.
    +
Abort.

Lemma compare_le :
  forall p1 p2 : Pos,
    CompareSpecT (p1 = p2) (le p1 p2 /\ p1 <> p2) (le p2 p1 /\ p1 <> p2) (compare p1 p2).
Proof.
  intros p1 p2.
  functional induction compare p1 p2.
  - constructor; reflexivity.
  - constructor. destruct p2; intuition; congruence.
  - constructor. destruct p1; intuition; congruence.
  - destruct IHc as [-> | [IHle IHneq] | [IHle IHneq]]; constructor; intuition; congruence.
  - destruct IHc as [-> | [IHle IHneq] | [IHle IHneq]]; constructor; intuition; try congruence.
    admit.
Abort.

Lemma eqb_spec :
  forall p1 p2 : Pos,
    reflect (p1 = p2) (BinaryPos.eqb p1 p2).
Proof.
  intros p1 p2.
  unfold BinaryPos.eqb.
  destruct (compare_spec p1 p2); constructor.
  - assumption.
  - intros ->. rewrite compare_refl in e. congruence.
  - intros ->. rewrite compare_refl in e. congruence.
Qed.

Lemma compare_succ_l :
  forall p : Pos,
    compare (succ p) p = Gt.
Proof.
  intros p; functional induction succ p; cbn.
  - reflexivity.
  - rewrite compare_refl; reflexivity.
  - rewrite IHp0; reflexivity.
Qed.

Lemma compare_succ :
  forall p1 p2 : Pos,
    compare (succ p1) (succ p2) = compare p1 p2.
Proof.
  intros p1 p2.
  functional induction compare p1 p2.
  - cbn; rewrite ?IHc; try reflexivity.
  - destruct p2; cbn; intuition.
    + destruct p2; cbn; intuition.
    + destruct p2; cbn; reflexivity.
  - destruct p1; cbn; intuition.
    + destruct p1; cbn; intuition.
    + destruct p1; cbn; reflexivity.
  - cbn; reflexivity.
  - destruct p1', p2'; cbn in *; intuition (try congruence).
    + rewrite e1; reflexivity.
    + admit.
  - cbn.
Restart.
  induction p1 as [| p1' IH | p1' IH]; intros [| p2' | p2']. 5: rewrite !succ_equation; cbn.
Admitted.

Lemma CompOpp_compare :
  forall p1 p2 : Pos,
    CompOpp (compare p1 p2) = compare p2 p1.
Proof.
  intros p1 p2.
  functional induction compare p1 p2
  ; cbn; rewrite <- ?IHc, ?e1; cbn; try reflexivity.
  - destruct p2; cbn; intuition.
  - destruct p1; cbn; intuition.
Restart.
  intros p1 p2.
  destruct (compare_spec p1 p2) as [-> | -> | ->]; cbn.
  2-3: reflexivity.
  rewrite compare_refl; reflexivity.
Qed.

Lemma compare_trans :
  forall (p1 p2 p3 : Pos) (c : comparison),
    compare p1 p2 = c -> compare p2 p3 = c -> compare p1 p3 = c.
Proof.
  intros p1 p2; functional induction compare p1 p2
  ; cbn; intros p3 c Heq12 Heq23; subst; auto.
  - destruct p2, p3; cbn in *; intuition congruence.
  - destruct p1, p3; cbn in *; intuition congruence.
Restart.
  intros p1 p2 p3 [] Heq12 Heq23.
  - apply compare_refl_conv in Heq12, Heq23; subst. apply compare_refl.
  - admit.
  - admit.
Restart.
  intros p1 p2 p3 c H12 H23.
  destruct (compare_spec p1 p2); subst.
  + assumption.
  + 
Admitted.

Lemma compare_succ_r :
  forall p : Pos,
    compare p (succ p) = Lt.
Proof.
  intros p.
  rewrite <- CompOpp_compare, compare_succ_l; cbn.
  reflexivity.
Qed.

Lemma min_O :
  forall p1 p2 : Pos,
    min (O p1) (O p2) = O (min p1 p2).
Proof.
  intros p1 p2.
  unfold min; cbn.
  destruct (compare p1 p2); reflexivity.
Qed.

Lemma min_I :
  forall p1 p2 : Pos,
    min (I p1) (I p2) = I (min p1 p2).
Proof.
  intros p1 p2.
  unfold min; cbn.
  destruct (compare p1 p2); reflexivity.
Qed.

Lemma min_comm :
  forall p1 p2 : Pos,
    min p1 p2 = min p2 p1.
Proof.
  intros p1 p2.
  unfold min.
  rewrite <- CompOpp_compare.
  destruct (compare p2 p1) eqn: Hcmp; cbn; [| easy..].
  apply compare_refl_conv; assumption.
Qed.

Lemma min_assoc :
  forall p1 p2 p3 : Pos,
    min (min p1 p2) p3 = min p1 (min p2 p3).
Proof.
  intros p1 p2 p3.
  unfold min.
  destruct (compare_spec' p1 p2) as [-> | [H12 H12'] | [H12 H12']],
           (compare_spec' p2 p3) as [-> | [H23 H23'] | [H23 H23']]
  ; subst; rewrite ?compare_refl, ?H12, ?H12', ?H23, ?H23'.
  1-4: reflexivity.
  all: destruct (compare_spec' p1 p3) as [-> | [H13 H13'] | [H13 H13']]
  ; subst; rewrite ?H13, ?H13'.
  all: try reflexivity.
Admitted.

Lemma max_comm :
  forall p1 p2 : Pos,
    max p1 p2 = max p2 p1.
Proof.
  intros p1 p2.
  unfold max.
  rewrite <- CompOpp_compare.
  destruct (compare p2 p1) eqn: Hcmp; cbn; [| easy..].
  symmetry.
  now apply compare_refl_conv.
Qed.

Lemma max_assoc :
  forall p1 p2 p3 : Pos,
    max (max p1 p2) p3 = max p1 (max p2 p3).
Proof.
  intros p1 p2 p3.
  unfold min.
  destruct (compare p1 p2) eqn: H12,
           (compare p2 p3) eqn: H23.
Admitted.


(* TODO
     Definition tail_add : nat -> nat -> nat.
     Definition tail_addmul : nat -> nat -> nat -> nat.
     Definition tail_mul : nat -> nat -> nat.

     Definition divmod : nat -> nat -> nat -> nat -> nat * nat.
     Definition div : nat -> nat -> nat.
     Definition modulo : nat -> nat -> nat.
     Definition gcd : nat -> nat -> nat.
     Definition square : nat -> nat.
     Definition sqrt_iter : nat -> nat -> nat -> nat -> nat.
     Definition sqrt : nat -> nat.
     Definition log2_iter : nat -> nat -> nat -> nat -> nat.
     Definition log2 : nat -> nat.
     Definition iter : nat -> forall A : Type, (A -> A) -> A -> A.
     Definition div2 : nat -> nat.
     Definition testbit : nat -> nat -> bool.
     Definition shiftl :
       (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n.
     Definition shiftr :
       (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n.
     Definition bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat.
     Definition land : nat -> nat -> nat.
     Definition lor : nat -> nat -> nat.
     Definition ldiff : nat -> nat -> nat.
     Definition lxor : nat -> nat -> nat.

 *)