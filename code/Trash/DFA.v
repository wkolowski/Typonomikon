Require Import List.
Import ListNotations.

Class DFA (Σ : Type) : Type :=
{
    State : Type;
    states : list State;
(*    finite : forall q : State, In q states;*)
    start : State;
    accepting : State -> bool;
    transition : Σ -> State -> State;
}.

Arguments State {Σ} _.
Arguments states {Σ} _.
(*Arguments finite {Σ} _ _.*)
Arguments start {Σ} _.
Arguments accepting {Σ} _ _.
Arguments transition {Σ} _ _ _.

Fixpoint accepts' {Σ : Type} (A : DFA Σ) (q : State A) (w : list Σ) : bool :=
match w with
    | [] => accepting A q
    | x :: w' => accepts' A (transition A x q) w'
end.

Definition accepts {Σ : Type} (A : DFA Σ) (w : list Σ) : bool :=
  accepts' A (start A) w.

Require Import Bool.

Instance product {Σ : Type} (A B : DFA Σ) : DFA Σ :=
{|
    State := State A * State B;
    states :=
      concat (
          map (fun qa : State A =>
            map (fun qb : State B => (qa, qb))
              (states B)) (states A));
    start := (start A, start B);
    accepting '(qa, qb) := accepting A qa && accepting B qb;
    transition x '(qa, qb) := (transition A x qa, transition B x qb);
|}.
(*
Proof.
  destruct A, B; cbn in *.
  clear -states0 states1 finite0 finite1.
  revert states1 finite1.
  induction states0; cbn; intros; destruct q as [qa qb].
    specialize (finite0 qa). inversion finite0.
    apply in_or_app. destruct (finite0 qa).
      subst. left. admit.
      right. apply IHstates0; auto. intro.
*)

Lemma product_spec :
  forall (Σ : Type) (A B : DFA Σ) (qa : State A) (qb : State B) (w : list Σ),
    accepts' (product A B) (qa, qb) w = accepts' A qa w && accepts' B qb w.
Proof.
  intros. revert A B qa qb.
  induction w as [| x w']; cbn.
    reflexivity.
    intros. rewrite IHw'. reflexivity.
Qed.
