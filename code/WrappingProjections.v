Set Primitive Projections.
Variant delayF (X : Type) (rec : Type) : Type :=
| NowF (x : X)
| LaterF (d : rec).
CoInductive delay X : Type := go { _observe : delayF X (delay X) }.
Arguments NowF {_ _}.
Arguments LaterF {_ _}.
Arguments _observe {_}.
Arguments go {_}.
Notation Now x := (go (NowF x)).
Notation Later t := (go (LaterF t)).

Definition subst {X Y} (k : X -> delay Y) : delay X -> delay Y :=
  cofix F (c : delay X) : delay Y :=
    match _observe c with
    | NowF x => k x
    | LaterF d => Later (F d)
    end.

Definition bind {X Y} (c : delay X) (k : X -> delay Y) := subst k c.

Definition iter {Acc Res : Type} (body : Acc -> delay (Acc + Res)) : Acc -> delay Res :=
  cofix F acc :=
    bind
      (body acc)
      (fun x =>
         match x with
         | inl acc' => Later (F acc')
         | inr res  => Now res
         end
      ).

Variable (body : nat -> delay (nat + nat)).
Variable (k : nat -> delay bool).

Definition observe {X : Type} (d : delay X) : delayF X (delay X) :=
  _observe d.

(* Undesired reduction behavior, the wrapping blocks it *)
Eval cbn in _observe (bind (iter body 0) k).

Eval simpl in _observe (bind (iter body 0) k).