Theorem plus''''_0_r : forall n : nat, plus''' n 0 = n.
(* begin hide *)
Proof.
  simpl. trivial.
Qed.
(* end hide *)

Theorem plus'''_Sn_m : forall n m : nat, plus''' (S n) m = S (plus''' n m).
(* begin hide *)
Proof.
  intros. generalize dependent n. induction m as [| m']; simpl; intros.
    trivial.
    rewrite IHm'. trivial.
Qed.
(* end hide *)

Theorem plus'''_n_Sm :
  forall n m : nat, plus''' n (S m) = S (plus''' n m).
(* begin hide *)
Proof.
  intros n m. generalize dependent n.
  induction m as [| m']; simpl; intro.
    trivial.
    rewrite ?plus'''_Sn_m. trivial.
Qed.
(* end hide *)

Theorem plus'''_0_l : forall n : nat, plus''' 0 n = n.
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    simpl. rewrite plus'''_Sn_m, IHn'. trivial.
Qed.
(* end hide *)

Theorem plus'''_comm : forall n m : nat, plus''' n m = plus''' m n.
(* begin hide *)
Proof.
  intros. generalize dependent n. induction m as [| m']; simpl; intros.
    rewrite plus'''_0_l. trivial.
    rewrite IHm'. simpl. trivial.
Qed.
(* end hide *)

Theorem plus'''_is_plus : forall n m : nat, plus''' n m = plus n m.
(* begin hide *)
Proof.
  induction n as [| n']; simpl; intro.
    apply plus'''_0_l.
    rewrite <- IHn'. rewrite plus'''_Sn_m. trivial.
Qed.
(* end hide *)

(** Udowodnij powyższe twierdzenie bez używania lematów pomocniczych. *)

