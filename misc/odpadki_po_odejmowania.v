

(* begin hide *)

(** chuj kurła: nie da się zdefiniować odejmowania *)

CoFixpoint sub (n m : conat) : conat :=
{|
    pred :=
      match pred n, pred m with
          | None, _ => None
          | _, None => pred n
          | Some n', Some m' => Some (sub n' m')
      end;
|}.

Lemma sub_0_l :
  forall n : conat, sim (sub zero n) zero.
(* begin hide *)
Proof.
  constructor. cbn. left. destruct (pred n); split; reflexivity.
Qed.
(* end hide *)

Lemma sub_0_r :
  forall n : conat, sim (sub n zero) n.
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. destruct n as [[n' |]]; cbn.
    right. do 2 eexists. intuition.
    left. auto.
Qed.
(* end hide *)

Lemma sub_succ :
  forall n m : conat, sim (sub (succ n) (succ m)) (sub n m).
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. destruct n as [[n' |]], m as [[m' |]]; cbn.
    right. do 2 eexists. intuition. apply CH.
    right. do 2 eexists. intuition.
      change {| pred := None; |} with zero.
Abort.
(* end hide *)

Lemma sub_omega_l :
  forall n : conat, sim (sub omega n) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. destruct n as [[n' |]]; cbn.
    right. exists (sub omega n'), omega. intuition.
    right. exists omega, omega. intuition.
Qed.
(* end hide *)

Lemma sub_omega_omega :
  sim (sub omega omega) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. right.
  exists (sub omega omega), omega. intuition.
Qed.
(* end hide *)

Inductive Finite : conat -> Prop :=
    | Finite_zero : Finite zero
    | Finite_succ : forall n : conat, Finite n -> Finite (succ n).

Lemma omega_not_Finite :
  ~ Finite omega.
(* begin hide *)
Proof.
  intro. remember omega as n. revert Heqn.
  induction H; intro.
    apply (f_equal pred) in Heqn. cbn in Heqn. inv Heqn.
    apply (f_equal pred) in Heqn. cbn in Heqn. inv Heqn.
Qed.
(* end hide *)

Lemma sub_Finite_omega :
  forall n : conat, Finite n -> sim (sub n omega) zero.
(* begin hide *)
Proof.
Abort.
(* end hide *)