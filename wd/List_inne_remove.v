Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(** ** [remove] *)

(** Czemu [remove] ma taki dziwny typ? *)

Fixpoint remove
  {A : Type} (n : nat) (l : list A) {struct l}
  : option (A * list A * list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some (h, [], t)
    | h :: t, S n' =>
        match remove n' t with
            | None => None
            | Some (x, l1, l2) => Some (x, h :: l1, l2)
        end
end.

Lemma remove_spec :
  forall (A : Type) (l : list A) (n : nat),
    match remove n l with
        | None => length l <= n
        | Some (x, l1, l2) => l = l1 ++ x :: l2
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    apply le_0_n.
    destruct n as [| n']; cbn.
      reflexivity.
      specialize (IHt n'). destruct (remove n' t).
        destruct p, p. cbn. rewrite <- IHt. reflexivity.
        apply le_n_S. assumption.
Qed.
(* end hide *)