Require Import List.
Import ListNotations.

Function div2 {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [x] => []
    | x :: y :: t => x :: div2 t
end.

Check R_div2.
Check R_div2_rect.
Check div2_equation.
Check div2_rect.
Check R_div2_correct.
Check R_div2_complete.

Print R_div2.
Print R_div2_rect.
Print div2_equation.
Print div2_rect.
Print R_div2_correct.
Print R_div2_complete.

Inductive R_div2' {A : Type} : list A -> list A -> Prop :=
    | c0 : R_div2' [] []
    | c1 : forall x : A, R_div2' [x] []
    | c2 : forall (x y : A) (l l' : list A),
        R_div2' l l' -> R_div2' (x :: y :: l) (x :: l').

Fixpoint R_div2'_correct
  (A : Type) (l l' : list A) : div2 l = l' -> R_div2' l l'.
Proof.
  destruct l as [| x [| y t]]; cbn; intros; subst; constructor.
    apply R_div2'_correct. trivial.
Qed.

Theorem R_div2'_complete :
  forall (A : Type) (l l' : list A),
    R_div2' l l' -> div2 l = l'.
Proof.
  induction 1. Focus 3. cbn; subst; trivial.
Qed.

Fixpoint div2_ind'
  (P : forall A : Type, list A -> list A -> Prop)
  (H0 : forall A : Type, P A [] [])
  (H1 : forall (A : Type) (x : A), P A [x] [])
  (H2 : forall (A : Type) (x y : A) (t : list A),
      P A t (div2 t) -> P A (x :: y :: t) (x :: div2 t))
  (A : Type) (l : list A) : P A l (div2 l).
Proof.
  destruct l as [| x [| y t]]; cbn.
    apply H0.
    apply H1.
    apply H2. apply div2_ind'; auto.
Qed.

Theorem div2_eq' :
  forall (A : Type) (l : list A),
    div2 l = match l with
                | [] => []
                | [x] => []
                | x :: y :: t => x :: div2 t
             end.
Proof.
  destruct l as [| x [| y t]]; cbn; trivial.
Qed.

Goal
  forall (A : Type) (l : list A),
    l <> [] -> length (div2 l) < length l.
Proof.
  apply (@div2_ind (fun A l l' => l <> [] -> length l' < length l)); intros.
    contradiction.
    cbn. auto.
    destruct t as [| h1 [| h2 t']]; cbn in *; auto.
      apply lt_n_S.
Abort.