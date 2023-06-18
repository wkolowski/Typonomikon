(** * G8e: Kontenery [TODO] *)

From Typonomikon Require Export G8d.

(** Odkrycie stulecia: [Container] jest funktorem bazowym [W]! *)

(** * Kontenery (TODO) *)

(** [S] to skrót od "shape", czyli po naszemu "kształt", zaś [P] ma przywodzić
    na myśl "position", czyli "pozycja". *)

Inductive Container (S : Type) (P : S -> Type) (X : Type) : Type :=
| ctain : forall s : S, (P s -> X) -> Container S P X.

Arguments ctain {S P X} _ _.

Definition shape {S P X} (c : Container S P X) : S :=
match c with
| ctain s _ => s
end.

Definition position {S P X} (c : Container S P X) : P (shape c) -> X :=
match c with
| ctain s p => p
end.

Require Import List.
Import ListNotations.

Require Import FunctionalExtensionality.

Require Import Fin.
Require Import Equality.

Module CList.

Definition CList (A : Type) :=
  Container nat Fin.t A.

Definition cnil {A : Type} : CList A :=
  ctain 0 (fun e : Fin.t 0 => match e with end).

Definition ccons {A : Type} (h : A) (t : CList A) : CList A.
Proof.
  destruct t as [s p].
  apply (ctain (1 + s)).
  intros f.
  dependent destruction f.
  - exact h.
  - exact (p f).
Defined.

Definition prev {n : nat} (f : Fin.t (2 + n)) : Fin.t (1 + n).
Proof.
  dependent destruction f.
  - exact F1.
  - exact f.
Defined.

Fixpoint f {A : Type} (l : list A) : CList A :=
match l with
| [] => cnil
| h :: t => ccons h (f t)
end.

Definition g {A : Type} (c : CList A) : list A.
Proof.
  destruct c as [s p].
  revert s p.
  fix IH 1; intros [| s'] p.
  - exact [].
  - exact (p F1 :: IH _ (fun s => p (FS s))).
Defined.

Lemma f_cons :
  forall {A : Type} (h : A) (t : list A),
    f (h :: t) = ccons h (f t).
Proof.
  easy.
Qed.

Lemma g_ccons :
  forall {A : Type} (h : A) (t : CList A),
    g (ccons h t) = h :: g t.
Proof.
  now destruct t; cbn.
Qed.

Lemma g_ctain :
  forall {A : Type} (s : nat) (p : Fin.t (1 + s) -> A),
    g (ctain (1 + s) p) = p F1 :: g (ctain s (fun s => p (FS s))).
Proof.
  easy.
Qed.

Lemma fg :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  induction l as [| h t]; cbn; [easy |].
  now rewrite g_ccons, IHt.
Qed.

Lemma gf :
  forall {A : Type} (c : CList A),
    f (g c) = c.
Proof.
  intros A [s p]; revert p.
  induction s as [| s']; intros.
  - cbn; unfold cnil; f_equal.
    extensionality x.
    now dependent destruction x; cbn.
  - rewrite g_ctain, f_cons, IHs'.
    unfold ccons; f_equal.
    extensionality x.
    now dependent destruction x; cbn.
Qed.

End CList.