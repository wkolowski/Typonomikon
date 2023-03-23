Inductive BT (A : Type) : Type :=
| E
| N (v : A) (l r : BT A).

Arguments E {A}.
Arguments N {A} _ _ _.

Inductive ForallSub {A : Type} (P : BT A -> Prop) : BT A -> Prop :=
| ForallSub_E : P E -> ForallSub P E
| ForallSub_N :
    forall {v : A} {l r : BT A},
      P (N v l r) -> ForallSub P l -> ForallSub P r -> ForallSub P (N v l r).

Inductive ExistsSub {A : Type} (P : BT A -> Prop) : BT A -> Prop :=
| ExistsSub_here :
    forall {t : BT A}, P t -> ExistsSub P t
| ExistsSub_left :
    forall {v : A} {l r : BT A}, ExistsSub P l -> ExistsSub P (N v l r)
| ExistsSub_right :
    forall {v : A} {l r : BT A}, ExistsSub P r -> ExistsSub P (N v l r).

Inductive Forall {A : Type} (P : A -> Prop) : BT A -> Prop :=
| Forall_E : Forall P E
| Forall_N :
    forall {v : A} {l r : BT A},
      P v -> Forall P l -> Forall P r -> Forall P (N v l r).

Fixpoint subs {A : Type} (t : BT A) : BT (BT A) :=
match t with
| E => N E E E
| N v l r => N (N v l r) (subs l) (subs r)
end.

Definition ForallSub' {A : Type} (P : BT A -> Prop) (t : BT A) : Prop :=
  Forall P (subs t).

Lemma ForallSub_ForallSub' :
  forall {A : Type} (P : BT A -> Prop) (t : BT A),
    ForallSub P t <-> ForallSub' P t.
Proof.
  unfold ForallSub'.
  split.
  - induction 1; cbn.
    + now constructor; [| constructor..].
    + now constructor.
  - induction t as [| v l IHl r IHr]; cbn.
    + inversion_clear 1; subst.
      now constructor.
    + inversion_clear 1; subst.
      now constructor; [| apply IHl | apply IHr].
Qed.

Definition Forall' {A : Type} (P : A -> Prop) (t : BT A) : Prop :=
  ForallSub (fun t' =>
    match t' with
    | E => True
    | N v _ _ => P v
    end) t.

Lemma Forall_Forall' :
  forall {A : Type} (P : A -> Prop) (t : BT A),
    Forall P t <-> Forall' P t.
Proof.
  now split; induction 1; constructor.
Qed.