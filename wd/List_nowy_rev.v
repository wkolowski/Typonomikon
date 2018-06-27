Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(* begin hide *)
Fixpoint rev {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => snoc h (rev t)
end.
(* end hide *)

Lemma isEmpty_rev :
  forall (A : Type) (l : list A),
    isEmpty (rev l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    apply isEmpty_snoc.
Qed.
(* end hide *)

Lemma length_rev :
  forall (A : Type) (l : list A),
    length (rev l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_snoc, IHt. reflexivity.
Qed.
(* end hide *)

Lemma snoc_rev :
  forall (A : Type) (l : list A) (x : A),
    snoc x (rev l) = rev (x :: l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma rev_snoc :
  forall (A : Type) (x : A) (l : list A),
    rev (snoc x l) = x :: rev l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite ?IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma rev_rev :
  forall (A : Type) (l : list A),
    rev (rev l) = l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite rev_snoc, IHt. reflexivity.
Qed.
(* end hide *)

(* GRUBA KRESKA ================================================= *)

Lemma rev_app :
  forall (A : Type) (l1 l2 : list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intro.
    rewrite app_nil_r. reflexivity.
    rewrite IHt1, snoc_app, snoc_rev. reflexivity.
Qed.
(* end hide *)