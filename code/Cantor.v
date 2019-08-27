Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.

Theorem Cantor_opt :
  forall {A B : Type} (f : A -> A -> option B),
    B -> ~ surjective f.
Proof.
  unfold surjective. intros A B f b H.
  destruct (H (fun _ => None)) as [a1 eq1].
  destruct (H (fun _ => Some b)) as [a2 eq2].
  destruct (H (
    fun x : A =>
    match f x x with
      | None => Some b
      | Some _ => None
    end))
  as [a eq].
  apply (f_equal (fun f => f a)) in eq.
  destruct (f a a); congruence.
Qed.

(** Jeden konstruktor negatywny - ok. *)
Module attempt1.

Fail Inductive wut : Type :=
    | C : (wut -> bool) -> wut.

Axioms
  (wut : Type)
  (C : (wut -> bool) -> wut)
  (ind : forall
    (P : wut -> Type)
    (H : forall f : wut -> bool, P (C f)),
      {f : forall w : wut, P w |
       forall g : wut -> bool, f (C g) = H g}).

Fail Definition bad : bool :=
  let f (w : wut) : bool :=
    match w with
        | C f' => f' w
    end
  in f (C f).

(* ===> f (C f) = f (C f) = f (C f) *)

Definition bad : wut -> (wut -> bool).
Proof.
  apply (ind (fun _ => wut -> bool)).
  intro f. exact f.
Defined.

(*
Lemma have_mercy_plx : False.
Proof.
  apply (Cantor' bad negb).
    destruct b; inversion 1.
    unfold surjective. intro. unfold bad. destruct (ind _).
      exists (C b). apply e.
Qed.
*)

End attempt1.

(* Jeden konstruktor pozytywny - nie ok. *)
Module positive.

Fail Inductive harder : Type :=
    | C : ((harder -> nat) -> nat) -> harder.

Axioms
  (harder : Type)
  (C : ((harder -> nat) -> nat) -> harder)
  (ind : forall
    (P : harder -> Type)
    (PC : forall f : (harder -> nat) -> nat, P (C f)),
      {f : forall h : harder, P h |
        forall g : (harder -> nat) -> nat,
          f (C g) = PC g}).

Definition bad : harder -> ((harder -> nat) -> nat).
Proof.
  apply (ind (fun _ => (harder -> nat) -> nat)).
  exact (fun x => x).
Defined.

Definition bad' : ((harder -> nat) -> nat) -> (harder -> nat).
Proof.
  intros f h.
  apply (ind (fun _ => harder -> nat)).
Abort.

Lemma bad_sur :
  surjective bad.
Proof.
  unfold surjective. intro f.
  exists (C f). unfold bad.
  destruct (ind _). apply e.
Qed.

(*
Fail Definition loop : nat :=
  let f : harder -> nat :=
    fun h : harder =>
    match h with
        | C g => g f
    end
*)

Goal ~ surjective bad.
Proof.
  unfold surjective. intro H.
  specialize (H (
    fun f : (harder -> nat) =>
      bad (C (fun _ => 42)) f)).
  destruct H as [h eq].
Abort.

End positive.