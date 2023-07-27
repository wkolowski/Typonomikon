(** * D4c: Arytmetyka Peano, część 3 *)

From Typonomikon Require Import D1c.

Module MyNat.

Import D1c.MyNat.

(** * Dzielenie przez 2 *)

(** Pokaż, że indukcję na liczbach naturalnych można robić "co 2".
    Wskazówka: taktyk można używać nie tylko do dowodzenia. Przypomnij
    sobie, że taktyki to programy, które generują dowody, zaś dowody
    są programami. Dzięki temu nic nie stoi na przeszkodzie, aby
    taktyki interpretować jako programy, które piszą inne programy.
    I rzeczywiście — w Coqu możemy używać taktyk do definiowania
    dowolnych termów. W niektórych przypadkach jest to bardzo częsta
    praktyka. *)

Fixpoint nat_ind_2
  (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
  (HSS : forall n : nat, P n -> P (S (S n))) (n : nat) : P n.
(* begin hide *)
Proof.
  destruct n.
    apply H0.
    destruct n.
      apply H1.
      apply HSS. apply nat_ind_2; auto.
Qed.
(* end hide *)

(** Zdefiniuj dzielenie całkowitoliczbowe przez [2] oraz funkcję obliczającą
    resztę z dzielenia przez [2]. *)

(* begin hide *)
Fixpoint div2 (n : nat) : nat :=
match n with
| 0 => 0
| 1 => 0
| S (S n') => S (div2 n')
end.

Fixpoint mod2 (n : nat) : nat :=
match n with
| 0 => 0
| 1 => 1
| S (S n') => mod2 n'
end.
(* end hide *)

Lemma div2_even :
  forall n : nat, div2 (mul 2 n) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r in *. rewrite ?add_S_r. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma div2_odd :
  forall n : nat, div2 (S (mul 2 n)) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r in *. rewrite ?add_S_r. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma mod2_even :
  forall n : nat, mod2 (mul 2 n) = 0.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r, ?add_S_r in *. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma mod2_odd :
  forall n : nat, mod2 (S (mul 2 n)) = 1.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r, ?add_S_r in *. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma div2_mod2_spec :
  forall n : nat, add (mul 2 (div2 n)) (mod2 n) = n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial.
  rewrite add_0_r in *. rewrite add_S_r. cbn. rewrite H. trivial.
Qed.
(* end hide *)

Lemma div2_le :
  forall n : nat, div2 n <= n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial; try (repeat constructor; fail).
  apply le_n_S. constructor. assumption.
Qed.
(* end hide *)

Lemma div2_pres_le :
  forall n m : nat, n <= m -> div2 n <= div2 m.
(* begin hide *)
Proof.
  induction n using nat_ind_2; cbn; intros; try apply le_0_l.
  destruct m as [| [| m']]; cbn.
    inversion H. 
    inversion H. inversion H1.
    apply le_n_S, IHn. do 2 apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma mod2_le :
  forall n : nat, mod2 n <= n.
(* begin hide *)
Proof.
  apply nat_ind_2; cbn; intros; trivial; repeat constructor; assumption.
Qed.
(* end hide *)

Lemma mod2_not_pres_e :
  exists n m : nat, n <= m /\ mod2 m <= mod2 n.
(* begin hide *)
Proof.
  exists (S (S (S 0))), (S (S (S (S 0)))). cbn.
  split; repeat constructor.
Qed.
(* end hide *)

Lemma div2_lt :
  forall n : nat,
    0 <> n -> div2 n < n.
(* begin hide *)
Proof.
  induction n using nat_ind_2; cbn; intros.
    contradiction H. reflexivity.
    apply le_n.
    unfold lt in *. destruct n as [| n'].
      cbn. apply le_n.
      specialize (IHn ltac:(inversion 1)). apply le_n_S.
        apply le_trans with (S n').
          assumption.
          apply le_S, le_n.
Qed.
(* end hide *)

End MyNat.

(** * Szybkie potęgowanie (TODO) *)

(* begin hide *)
Module MyDiv2.

Import ZArith.

Fixpoint evenb (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S n') => evenb n'
end.

(*
Fixpoint quickMul (fuel n m : nat) : nat :=
match fuel with
| 0 => 0
| S fuel' =>
  match n with
  | 0 => 0
  | _ =>
    let res := quickMul fuel' (div2 n) m in
      if evenb n then add res res else add (add m res) res
  end
end.

Time Eval compute in 430 * 110.
Time Eval compute in quickMul 1000 430 110.

Function qm (n m : nat) {measure id n} : nat :=
match n with
| 0 => 0
| _ =>
  let r := qm (div2 n) m in
    if evenb n then 2 * r else m + 2 * r
end.
Proof.
Abort.

*)
End MyDiv2.
(* end hide *)