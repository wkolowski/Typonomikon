Require Import D5.

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

Function splitBy'
  {A : Type} (p : A -> bool) (l : list A) : list (list A) :=
match l with
    | [] => []
    | h :: t =>
        if p h
        then splitBy p t
        else
          match splitBy p t with
              | [] => [[h]]
              | g :: gs => (h :: g) :: gs
          end
end.

Definition splitBy2
  {A : Type} (p : A -> bool) (l : list A) : list (list A) :=
    map (fun x : A => if p x then [] else [x]) l.

Compute splitBy isZero [0; 1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].
Compute splitBy' isZero [0; 1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].
Compute splitBy2 isZero [0; 1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].

Lemma splitBy_splitBy' :
  forall (A : Type) (p : A -> bool) (l : list A),
    splitBy p l = splitBy' p l.
Proof.
  intros. functional induction @splitBy A p l; cbn.
    reflexivity.
    rewrite e0. reflexivity.
    rewrite e0. reflexivity.
    destruct (p x), t; rewrite e0.
Abort.

Lemma splitBy_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = true -> (forall x : A, elem x l -> p x = false) ->
      splitBy p (intersperse x l) = map (fun x => [x]) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (intersperse x t); cbn in *.
      rewrite (H0 _ ltac:(left)), <- (IHt H).
        reflexivity.
        intros. apply H0. right. assumption.
      rewrite H, (IHt H).
        reflexivity.
        intros. apply H0. right. assumption.
Qed.
(* end hide *)

(* TODO: a whole library for splitting lists! *)