(* TODO: rozszerzyć metodę Bove-Capretta na korekursję *)

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A} _.
Arguments tl {A} _.

Definition cons {A : Type} (h : A) (t : Stream A) : Stream A :=
{|
    hd := h;
    tl := t;
|}.

CoFixpoint zipWith
  {A B C : Type} (f : A -> B -> C) (sa : Stream A) (sb : Stream B) : Stream C :=
{|
    hd := f (hd sa) (hd sb);
    tl := zipWith f (tl sa) (tl sb);
|}.

Fail CoFixpoint fibs : Stream nat :=
{|
    hd := 0;
    tl := zipWith plus fibs (cons 1 fibs);
|}.

(*
Inductive Call (C : Type) (F : Type -> Type) : Type :=
    | call : C -> forall {A B : Type}, (A -> B -> C) -> F A -> F B -> Call C F.

Arguments call {C F} _ {A B} _.

CoInductive wut (C : Type) : Type :=
{
    wuut : Call C wut;
}.
*)

Set Implicit Arguments.

(*
CoInductive cod {C : Type} (f : C -> C -> C) (s : Stream C) : Type :=
{
    cod' :
      {h : C & {t : Stream C & (s = cons h t)%type * cod f t}}%type +
}.
*)

CoInductive Call (C : Type) : Type :=
{
    hdc : C;
    fn : C -> C -> C;
    arg1 : Call C;
    hd_arg2 : C;
    tl_arg2 : Call C;
}.

CoFixpoint Fibs : Call nat :=
{|
    hdc := 0;
    fn := plus;
    arg1 := Fibs;
    hd_arg2 := 1;
    tl_arg2 := Fibs;
|}.

CoFixpoint Call2Stream {C : Type} (c : Call C) : Stream C.
Proof.
  constructor.
    exact (hdc c).
    apply (zipWith (fn c)).
      exact (Call2Stream _ (arg1 c)).
      exact (cons (hd_arg2 c) (Call2Stream _ (tl_arg2 c))).
Abort.

(*
{|
    hd := hdc c;
    tl := zipWith (fn c)
                  (Call2Stream (arg1 c))
                  (cons (hd_arg2 c) (Call2Stream (tl_arg2 c)));
|}.
*)

(*
CoFixpoint w2s {C : Type} (w : wut C) : Stream C :=
{|
    hd := match wuut _ w with call h _ _ _ => h end
|}.

Inductive Call (C : Type) (F : Type -> Type) : Type :=
    | ht : C -> F C -> Call C F
    | zw : forall {A B : Type}, (A -> B -> C) -> F A -> F B -> Call C F.

Arguments ht {C F} _ _.
Arguments zw {C F A B} _ _ _.

CoInductive ZipWith' (C : Type) : Type :=
{
    call : Call C ZipWith';
}.

Definition Cons {C : Type} (h : C) (t : ZipWith' C) : ZipWith' C :=
{|
    call := ht h t
|}.

Definition ZipWith
  {A B C : Type} (f : A -> B -> C)
  (zwa : ZipWith' A) (zwb : ZipWith' B) : ZipWith' C :=
{|
    call := zw f zwa zwb
|}.

CoFixpoint Fibs : ZipWith' nat :=
  Cons 0 (ZipWith plus Fibs (Cons 1 Fibs)).

(*
CoFixpoint do {C : Type} (zw : ZipWith' C) : Stream C :=
{|
    
|}.
*)

Inductive whnf : forall {C : Type}, ZipWith' C -> Prop :=
    | whnf_cons :
        forall (C : Type) (h : C) (t : ZipWith' C),
          whnf t -> whnf (Cons h t)
    | whnf_zip :
        forall
          {A B C : Type} (f : A -> B -> C)
          (zwa : ZipWith' A) (zwb : ZipWith' B),
            whnf zwa -> whnf zwb -> whnf (ZipWith f zwa zwb).

Lemma whnf_Fibs : whnf Fibs.
Proof.
  unfold Fibs. unfold Cons.
  constructor.

Record Result (C : Type) : Type :=
{
    res : C;
    rest : ZipWith' C;
    w : whnf rest;
}.

Fixpoint step {C : Type} {zw : ZipWith' C} (w : whnf zw) : Result C :=
match w with
    | whnf_cons _ h t => {| res := h; rest := 

CoFixpoint do {C : Type} (zw : ZipWith C) : Stream C :=
{|
    hd := 
(*Inductive FiniteZW {C : Type} *)

CoInductive fibs : 
*)

Unset Guard Checking.

CoFixpoint fibs : Stream nat :=
{|
    hd := 0;
    tl := zipWith plus fibs (cons 1 fibs)
|}.

Require Import D5.

Fixpoint take {A : Type} (n : nat) (s : Stream A) : list A :=
match n with
    | 0 => []
    | S n' => hd s :: take n' (tl s)
end.

Compute take 20 fibs.