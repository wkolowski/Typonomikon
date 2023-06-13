(** * G8e: Kontenery [TODO] *)

From Typonomikon Require Import G8d.

(** [S] to skrót od "shape", czyli po naszemu "kształt", zaś [P] ma przywodzić
    na myśl "position", czyli "pozycja". *)

Inductive Container (S : Type) (P : S -> Type) (X : Type) : Type :=
| ctain : forall s : S, (P s -> X) -> Container S P X.

Arguments ctain {S P X} _ _.

(* Definition Container (S : Type) (P : S -> Type) : Type -> Type :=
  fun X : Type => {s : S & P s -> X}. *)

Require Import List.
Import ListNotations.

Require Import Fin.
Require Import Equality.

Require Import Recdef.

Module CList.

Definition CList (A : Type) :=
  Container nat Fin.t A.

Definition prev {n : nat} (f : Fin.t (2 + n)) : Fin.t (1 + n).
Proof.
  inversion f as [| n' f'].
    exact F1.
    exact f'.
Defined.

Fixpoint f {A : Type} (l : list A) : CList A.
refine (
match l with
| [] => ctain 0 (fun s : Fin.t 0 => match s with end)
| x :: xs =>
  match f _ xs with
  | ctain n p => ctain (Datatypes.S n) _
  end
end).
  destruct n as [| n']; intro s.
    exact x.
    exact (p (prev s)).
Defined.
Definition g {A : Type} (c : CList A) : list A.
Proof.
  destruct c as [n p].
  revert n p.
  fix IH 1; intros [| n'] p.
    exact [].
    exact (p F1 :: IH _ (fun s => p (FS s))).
Defined.

Lemma fg :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    revert h IHt.
    induction t as [| h' t']; cbn; intros.
      reflexivity.
      destruct (f t'). cbn in *. destruct s.
Abort.

Lemma gf :
  forall {A : Type} (c : CList A),
    f (g c) = c.
Proof.
  intros A [n p].
  induction n as [| n'].
    cbn. f_equal. admit.
    cbn. destruct (f _) eqn: Heq. destruct s.
      admit.
      destruct n' as [| n''].
        cbn in *. congruence.
        cbn in Heq.
Abort.

End CList.