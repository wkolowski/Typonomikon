Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Function groupBy
  {A : Type} (p : A -> A -> bool) (l : list A) : list (list A) :=
match l with
    | [] => []
    | [x] => [[x]]
    | x :: (y :: l'') as l' =>
        match groupBy p l' with
            | [] => [[x]]
            | l :: ls => if p x y then (x :: l) :: ls else [x] :: l :: ls
        end
end.

Compute groupBy orb [true; true; false; false; true].

Lemma isEmpty_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    isEmpty (groupBy p l) = isEmpty l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma join_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    join (groupBy p l) = l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    1-2: reflexivity.
    apply (f_equal isEmpty) in e0. rewrite isEmpty_groupBy in e0.
      inversion e0.
    rewrite e0 in IHl0. cbn in IHl0. rewrite IHl0. reflexivity.
    rewrite e0 in IHl0. cbn in IHl0. rewrite IHl0. reflexivity.
Qed.
(* end hide *)

Lemma map_groupBy_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    map (groupBy p) (groupBy p l) =
    map (fun x => [x]) (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    1-3: reflexivity.
    Focus 2. rewrite e0 in *. cbn in *. rewrite IHl0. reflexivity.
    rewrite ?e0 in IHl0. cbn in IHl0. inversion IHl0; subst; clear IHl0.
      rewrite H0. f_equal. destruct l0.
        reflexivity.
        cbn in *. destruct l''.
          inversion e0; subst. rewrite e1. reflexivity.
          cbn in *. destruct l''.
            destruct (p y a0); inversion e0; subst; rewrite e1; reflexivity.
Abort.

Function splitBy
  {A : Type} (p : A -> bool) (l : list A) : list (list A) :=
match l with
    | [] => []
    | [h] => if p h then [] else [[h]]
    | x :: (y :: t) as t' =>
        if p y
        then [x] :: splitBy p t
        else 
          match splitBy p t' with
             | [] => if p x then [] else [[x]]
             | l :: ls => if p x then l :: ls else (x :: l) :: ls
         end
end.

Definition isZero n :=
match n with
    | 0 => true
    | _ => false
end.

Compute splitBy isZero [1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].

Lemma splitBy_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = true -> splitBy p (intersperse x l) = map (fun x => [x]) l.
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn.
    reflexivity.
Abort.
(* end hide *)

(* TODO: unsplitBy *)