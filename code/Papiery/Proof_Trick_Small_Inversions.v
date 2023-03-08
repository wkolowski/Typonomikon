(** * Proof Trick: Small Inversions *)

(** ** 1 Introduction *)

Inductive mul3 : nat -> Prop :=
| T0 : mul3 0
| T3 : forall n : nat, mul3 n -> mul3 (3 + n).

Fixpoint mod3 (n : nat) : nat :=
match n with
| S (S (S n')) => mod3 n'
| n' => n'
end.

(** ** 2 Two Facets of Inversion *)

(** ** 3 Inversion by Diagonalization of Absurd Hypotheses *)

(* 11 lines *)
Definition absurd2_prog :
  forall P : Prop, mul3 2 -> P :=
    fun (P : Prop) (H : mul3 2) =>
    let
      diag (x : nat) :=
      match x with
      | 2 => P
      | _ => mul3 2
      end
    in
      match H in (mul3 n) return (diag n) with
      | T0     => H
      | T3 _ _ => H
      end.

Inductive nd (f g : nat -> nat) (c : nat) : nat -> Prop :=
| Nc : nd f g c c
| Nf : forall n : nat, nd f g c n -> nd f g c (f n)
| Ng : forall n : nat, nd f g c n -> nd f g c (g n).

Definition pl3 := plus 3.
Definition pl5 := plus 5.

Lemma absurd_nd4_interac :
  forall C : Prop, nd pl3 pl5 7 4 -> C.
Proof.
  intros C H.
  pose (diag x := match x with | 4 => C | _ => nd pl3 pl5 7 4 end).
  change (diag 4).
  case H; intros.
    apply H.
    case H0; intros; apply H.
    apply H.
  Show Proof. (* 21 lines *)
Restart.
  intros C H.
  pose (diag x := match x with | 4 => C | _ => nd pl3 pl5 7 4 end).
  change (diag 4).
  case H; (intros; exact H) || (intros n N; case N; intros; exact H).
  Show Proof. (* 21 lines *)
Qed.

(* 12 lines, effectively 10 *)
Definition absurd_nd4_prog :
  forall C : Prop, nd pl3 pl5 7 4 -> C :=
    fun (C : Prop) (H : nd pl3 pl5 7 4) =>
    let
      diag x := match x with | 4 => C | _ => nd pl3 pl5 7 4 end
    in
      match H in (nd _ _ _ n) return (diag n) with
      | Nf _ _ _ _ N =>
        match N in (nd _ _ _ n0) return (diag (pl3 n0)) with
        | Nc _ _ _     => H
        | Nf _ _ _ _ _ => H
        | Ng _ _ _ _ _ => H
        end
      | _ => H
      end.

(** ** 4 Eliminating Strong Elimination *)

(** ** 5 Recursively Absurd Hypotheses *)

Require Import Arith.

Lemma invmul10 : mul3 10 -> 0 = 1.
Proof.
  intro H.
  pose (diag x := if Nat.eqb x 10 then 1 else 0).
  change (0 = diag 10).
  do 4 (case H; clear H; reflexivity || intros).
  Show Proof. (* 20 lines *)
Restart.
  intro. do 4 (inversion H; clear - H1; rename H1 into H).
  Show Proof. (* 148 lines *)
Qed.

(** ** 6 Size of Proof Terms *)

Section wut.

Variable p : nat.

Definition tr15 : nat -> Prop :=
  nd (plus 6) (plus 9) 15.

(** Proofscript from the paper doesn't work. *)
Lemma tr15_beq :
  tr15 40 -> tr15 p.
Proof.
  intros t40.
  pose (diag n := if Nat.eqb n 40 then p else n).
  change (tr15 (diag 40)).
  assert (gen : forall n : nat, tr15 n -> tr15 (diag n)).
(*    repeat (exact t40 || intros n t; exact t40 || (case t; clear t n)).*)
    intros n t; case t; clear n t.
      constructor.
      intros n t. case t; clear n t.
Abort.

Lemma tr15_inv :
  tr15 40 -> tr15 p.
Proof.
  unfold tr15. intros t40.
  repeat match goal with
  | H : nd _ _ _ _ |- _ => inversion_clear H
  end.
  Show Proof. (* 8985 lines *)
Qed.

End wut.

(** ** 7 Other experiments *)

Section wut2.

Variable A : nat -> Prop.

Inductive l10 : nat -> Prop :=
| l10ini : l10 10
| l10rec : forall n : nat, A n -> l10 (pred n).

Lemma inv_lA0 :
  l10 0 -> A 0 \/ A 1.
Proof.
  intro l.
  match goal with
  | l : ?P |- ?Q =>
    pose (diag n := match n with 0 => Q | _ => P end)
  end.
  change (diag 0).
  case l; cbn; auto.
  do 2 (destruct n; cbn; auto).
  Show Proof. (* 17 lines *)
Restart.
  intros. inversion H. destruct n; cbn; auto.
  Show Proof. (* 39 lines *)
Qed.

End wut2.

(** ** 8 Application to Operational Semantics *)

(** ** 9 Conclusion and Further Work *)