Require Import CoqMTL.Control.

(** * Datat types à la carte *)

(** Based on paper of the same name by Wouter Swierstra. *)

(** ** 1 Introduction *)

(** ** 2 Fixing the expression problem *)

Fail Inductive Expr (F : Type -> Type) : Type :=
    | In : F (Expr F) -> Expr F.

Definition Expr (F : Type -> Type) : Type :=
  forall (X : Type), (F X -> X) -> X.

Inductive Val (E : Type) : Type :=
    | Val' : nat -> Val E.

Arguments Val' {E} _.

Inductive Add (E : Type) : Type :=
    | Add' : E -> E -> Add E.

Arguments Add' {E} _ _.

Inductive Coproduct (F G : Type -> Type) (E : Type) :=
    | Inl : F E -> Coproduct F G E
    | Inr : G E -> Coproduct F G E.

Arguments Inl {F G E} _.
Arguments Inr {F G E} _.

Notation "F :+: G" := (Coproduct F G) (right associativity, at level 42).

Definition addExample : Expr (Val :+: Add) :=
  fun X In =>
    In (Inr (Add' (In (Inl (Val' 118))) (In (Inl (Val' 1219))))).

(** ** 3 Evaluation *)

#[refine]
Instance Functor_Val : Functor Val :=
{
    fmap := fun (A B : Type) (f : A -> B) (va : Val A) =>
      match va with Val' a => Val' a end
}.
Proof.
  all: intros; ext x; destruct x; compute; reflexivity.
Defined.

#[refine]
Instance Functor_Add : Functor Add :=
{
    fmap := fun (A B : Type) (f : A -> B) (ax : Add A) =>
      match ax with Add' e1 e2 => Add' (f e1) (f e2) end
}.
Proof.
  all: intros; ext x; destruct x; compute; reflexivity.
Defined.

#[refine]
Instance Functor_Coproduct
  (F G : Type -> Type) (instF : Functor F) (instG : Functor G)
  : Functor (F :+: G) :=
{
    fmap := fun (A B : Type) (f : A -> B) (x : Coproduct F G A) =>
    match x with
        | Inl e => Inl (fmap f e)
        | Inr e => Inr (fmap f e)
    end
}.
Proof.
  all: intros; ext x; destruct x; hs.
Defined.

Definition foldExpr
  {F : Type -> Type} {inst : Functor F} {A : Type}
  (f : F A -> A) (x : Expr F) : A :=
    x _ f.

Class Eval (F : Type -> Type) (inst : Functor F) : Type :=
{
    evalAlgebra : F nat -> nat
}.

Instance Eval_Val : Eval Val Functor_Val :=
{
    evalAlgebra := fun x : Val nat => match x with Val' n => n end
}.

Instance Eval_Add : Eval Add Functor_Add :=
{
    evalAlgebra := fun x : Add nat => match x with Add' n m => n + m end
}.

Instance Eval_Coproduct
  (F G : Type -> Type) (instF : Functor F) (instG : Functor G)
  (instEF : Eval F instF) (instEG : Eval G instG)
  : Eval (F :+: G) (Functor_Coproduct F G instF instG) :=
{
    evalAlgebra := fun x : (F :+: G) nat =>
    match x with
        | Inl e => evalAlgebra e
        | Inr e => evalAlgebra e
    end
}.

Definition eval
  {F : Type -> Type} {instF : Functor F} {instE : Eval F instF}
  (x : Expr F) : nat := foldExpr evalAlgebra x.

Compute eval addExample.

(** ** 4 Automating injections *)

Class Sub (F G : Type -> Type) : Type :=
{
    inj : forall {A : Type}, F A -> G A
}.

Notation "F :<: G" := (Sub F G) (at level 42).

Instance Sub_refl (F : Type -> Type) : Sub F F :=
{
    inj := fun A : Type => @id (F A)
}.

Instance Sub_Coproduct (F G : Type -> Type) : Sub F (F :+: G) :=
{
    inj := @Inl F G
}.

Instance Sub_Rec
  (F G H : Type -> Type) (inst : Sub F H) : Sub F (G :+: H) :=
{
    inj := fun A : Type => @inj F H inst A .> Inr
}.

Definition inject
  (F G : Type -> Type) (inst : Sub F G) (x : F (Expr G)) : Expr G.
Proof.
  destruct inst as [inj]. unfold Expr in *.
  intros X In.
  apply inj in x. apply In. firstorder.
Abort.

Definition val
  {F : Type -> Type} {inst : Val :<: F} (x : nat) : Expr F :=
    fun X In => In (inj (Val' x)).

Definition add
  {F : Type -> Type} {inst : Add :<: F} (e1 e2 : Expr F) : Expr F :=
    fun X In => In (inj (Add' (e1 _ In) (e2 _ In))).

Eval cbn in
  let x : Expr (Add :+: Val) := add (val 1000) (add (val 330) (val 7))
  in eval x.

(** ** 5 Examples *)

Inductive Mul (E : Type) : Type :=
    | Mul' : E -> E -> Mul E.

Arguments Mul' {E} _ _.

#[refine]
Instance Functor_Mul : Functor Mul :=
{
    fmap := fun A B f x => match x with Mul' e1 e2 => Mul' (f e1) (f e2) end
}.
Proof.
  all: intros; ext x; destruct x; hs.
Defined.

Instance Eval_Mul : Eval Mul Functor_Mul :=
{
    evalAlgebra := fun '(Mul' x y) => x * y
}.

Definition mul
  {F : Type -> Type} {inst : Mul :<: F} (e1 e2 : Expr F) : Expr F :=
    fun X In => In (inj (Mul' (e1 _ In) (e2 _ In))).

Eval cbn in
  let
    x : Expr (Mul :+: Add :+: Val) :=
      add (val 1000) (mul (val 33) (val 7))
  in eval x.

Require Import String.
Open Scope string.

(* Problem! *)
Fail Inductive Render (F : Type -> Type) : Type :=
{
    render : forall {G : Type -> Type} {inst : Render G}, F (Expr G) -> string
}.

Fail Inductive Render (F : Type -> Type) : Type :=
    | C : forall (G : Type -> Type),
            (Render G -> F (Expr G) -> string) -> Render F.

Definition Render : (Type -> Type) -> Type :=
  fun F : Type -> Type =>
    forall Render : (Type -> Type) -> Type,
      ((forall G : Type -> Type, Render G -> F (Expr G) -> string) -> Render F)
      -> Render F.

Class RenderClass (F : Type -> Type) : Type :=
{
    render : Render F;
}.

Definition render_Val : Render Val :=
  fun _ f => f (fun _ _ _ => "42").

Instance Render_Val : RenderClass Val :=
{
    render := render_Val
}.

Definition render_Add : Render Add.
Proof.
  red. intros R f.
  apply f. intros G wut x. destruct x as [e1 e2].
Abort.