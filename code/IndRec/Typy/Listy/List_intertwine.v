Require Import D5.

Fixpoint intertwine {A : Type} (l1 l2 : list A) : list A :=
match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: intertwine t1 t2
end.

Lemma len_intertwine :
  forall {A : Type} (l1 l2 : list A),
    length (intertwine l1 l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite plus_0_r. reflexivity.
      rewrite IHt1, plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma map_intertwine :
  forall {A B : Type} (f : A -> B) (l1 l2 : list A),
    map f (intertwine l1 l2) = intertwine (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      reflexivity.
      rewrite IHt1. reflexivity.
Qed.
(* end hide *)

(* TODO *) Lemma intertwine_replicate :
  forall {A : Type} (x : A) (n : nat) (l : list A),
    intertwine l (replicate n x) =
      intersperse x (take (min (length l) (S n)) l) ++
      replicate (n - length l) x.
(* begin hide *)
Proof.
  intros until l. revert n.
  induction l as [| h t]; cbn; intro.
    rewrite <- minus_n_O. reflexivity.
    destruct n as [| n']; cbn.
      rewrite Nat.min_0_r, take_0. cbn. specialize (IHt 0). cbn in IHt.
Abort.
(* end hide *)