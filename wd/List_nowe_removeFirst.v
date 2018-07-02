Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(** * [rmFirst] *)

(* Połączenie [takeWhile], [find], [dropWhile] i [removeFirst].
   Ciekawe, dlaczego wcześniej tego nie zauważyłem. *)

Print takeWhile.
Print find.
Print dropWhile.
Print removeFirst.

(* begin hide *)
Fixpoint rmFirst
  {A : Type} (p : A -> bool) (l : list A) : option (list A * A * list A) :=
match l with
    | [] => None
    | h :: t =>
        if p h
        then Some ([], h, t)
        else
          match rmFirst p t with
              | None => None
              | Some (b, x, e) => Some (h :: b, x, e)
          end
end.
(* end hide *)

Lemma rmFirst_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    match rmFirst p l with
        | None => forall x : A, elem x l -> p x = false
        | Some (b, x, e) =>
            b = takeWhile (fun x : A => negb (p x)) l /\
            Some x = find p l /\
            x :: e = dropWhile (fun x : A => negb (p x)) l /\
            Some (x, b ++ e) = removeFirst p l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (p h) eqn: Hph; cbn.
      repeat split; reflexivity.
      destruct (rmFirst p t) eqn: Heq.
        destruct p0, p0. decompose [and] IHt; clear IHt.
          rewrite <- H3, ?H, H0. cbn. repeat split. assumption.
        intros. inv H.
          assumption.
          apply IHt. assumption.
Qed.
(* end hide *)

(* begin hide *)
Fixpoint rmLast
  {A : Type} (p : A -> bool) (l : list A) : option (list A * A * list A) :=
match l with
    | [] => None
    | h :: t =>
        match rmLast p t with
            | None => if p h then Some ([], h, t) else None
            | Some (b, x, e) => Some (h :: b, x, e)
        end
end.
(* end hide *)

Lemma rmLast_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    match rmLast p l with
        | None => forall x : A, elem x l -> p x = false
        | Some (b, x, e) =>
            b = takeWhile p l /\
            Some x = findLast p l /\
            x :: e = dropWhile p l /\
            Some (x, b ++ e) = removeLast p l
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    destruct (rmLast p t) eqn: Heq.
      destruct p0, p0. decompose [and] IHt; clear IHt.
        rewrite <- H3, ?H, H0, <- H1. destruct (p h) eqn: Hph; cbn.
          repeat split.
          subst.
Abort.
(* end hide *)
