Require Import D5.

Fixpoint rot2 {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [x] => [x]
    | x :: y :: t => y :: x :: rot2 t
end.

Fixpoint list_ind_2
  {A : Type} (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (Hcons2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
  (l : list A) : P l :=
match l with
    | [] => Hnil
    | [x] => Hsingl x
    | x :: y :: l' => Hcons2 x y l' (list_ind_2 P Hnil Hsingl Hcons2 l')
end.

Lemma rot2_involution :
  forall (A : Type) (l : list A),
    rot2 (rot2 l) = l.
Proof.
  intro. apply list_ind_2; cbn; intros.
    1-2: reflexivity.
    rewrite H. reflexivity.
Qed.

Inductive Rot2 {A : Type} : list A -> list A -> Prop :=
    | Rot2_nil : Rot2 [] []
    | Rot2_singl : forall x : A, Rot2 [x] [x]
    | Rot2_cons2 :
        forall (x y : A) (l l' : list A),
          Rot2 l l' -> Rot2 (x :: y :: l) (y :: x :: l').

Lemma Rot2_correct :
  forall (A : Type) (l : list A),
    Rot2 l (rot2 l).
Proof.
  intro. apply list_ind_2; cbn; constructor. assumption.
Qed.

Lemma Rot2_complete :
  forall (A : Type) (l l' : list A),
    Rot2 l l' -> rot2 l = l'.
Proof.
  induction 1; cbn.
    1-2: reflexivity.
    rewrite IHRot2. reflexivity.
Qed.