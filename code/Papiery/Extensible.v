Require Import String.

Set Implicit Arguments.

(** Zainspirowane przez
    #<a class='link'
        href='https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf'>
    Trees that Grow</a>#.

    TODO: dokończyć *)

Inductive Typ : Type :=
| Int : Typ
| Fun : Typ -> Typ -> Typ.

Inductive Con : Type := CLit | CVar | CAnn | CAbs | CApp | CExt.

Inductive Exp (f : Con -> Type) : Type :=
| Lit : f CLit -> nat -> Exp f
| Var : f CVar -> string -> Exp f
| Ann : f CAnn -> Exp f -> Typ -> Exp f
| Abs : f CAbs -> string -> Exp f -> Exp f
| App : f CApp -> Exp f -> Exp f -> Exp f
| Ext : f CExt -> Exp f.

Arguments Lit {f} _ _.
Arguments Var {f} _ _.
Arguments Ann {f} _ _.
Arguments Abs {f} _ _.
Arguments App {f} _ _.
Arguments Ext {f} _.

Module Undecorated.

Module Undecorated.

Inductive Exp : Type :=
| Lit : nat -> Exp
| Var : string -> Exp
| Ann : Exp -> Typ -> Exp
| Abs : string -> Exp -> Exp
| App : Exp -> Exp -> Exp.

End Undecorated.

Definition undecorated (c : Con) : Type :=
match c with
| CExt => False
| _    => unit
end.

Fixpoint f (e : Undecorated.Exp) : Exp undecorated :=
match e with
| Undecorated.Lit n     => Lit tt n
| Undecorated.Var v     => Var tt v
| Undecorated.Ann e' t  => Ann tt (f e') t
| Undecorated.Abs x e'  => Abs tt x (f e')
| Undecorated.App e1 e2 => App tt (f e1) (f e2)
end.

Fixpoint g (e : Exp undecorated) : Undecorated.Exp :=
match e with
| Lit _ n     => Undecorated.Lit n
| Var _ v     => Undecorated.Var v
| Ann _ e' t  => Undecorated.Ann (g e') t
| Abs _ x e'  => Undecorated.Abs x (g e')
| App _ e1 e2 => Undecorated.App (g e1) (g e2)
| Ext x       => match x with end
end.

Lemma fg :
  forall e : Undecorated.Exp,
    g (f e) = e.
Proof.
  induction e; cbn; congruence.
Qed.

Lemma gf :
  forall e : Exp undecorated,
    f (g e) = e.
Proof.
  induction e; cbn; try destruct f0; congruence.
Qed.

End Undecorated.

Module NewField.

Module NewField.

Inductive Exp : Type :=
| Lit : nat -> Exp
| Var : string -> Exp
| Ann : Exp -> Typ -> Exp
| Abs : string -> Exp -> Exp
| App : Typ -> Exp -> Exp -> Exp.

End NewField.

Definition newfield (c : Con) : Type :=
match c with
| CExt => False
| CApp => Typ
| _    => unit
end.

Fixpoint f (e : NewField.Exp) : Exp newfield :=
match e with
| NewField.Lit n       => Lit tt n
| NewField.Var v       => Var tt v
| NewField.Ann e' t    => Ann tt (f e') t
| NewField.Abs x e'    => Abs tt x (f e')
| NewField.App t e1 e2 => App t (f e1) (f e2)
end.

Fixpoint g (e : Exp newfield) : NewField.Exp :=
match e with
| Lit _ n     => NewField.Lit n
| Var _ v     => NewField.Var v
| Ann _ e' t  => NewField.Ann (g e') t
| Abs _ x e'  => NewField.Abs x (g e')
| App t e1 e2 => NewField.App t (g e1) (g e2)
| Ext x       => match x with end
end.

Lemma fg :
  forall e : NewField.Exp,
    g (f e) = e.
Proof.
  induction e; cbn; congruence.
Qed.

Lemma gf :
  forall e : Exp newfield,
    f (g e) = e.
Proof.
  induction e; cbn; try destruct f0; congruence.
Qed.

End NewField.

Module NewConstructor.

Module NewConstructor.

Axiom V : Type.

Inductive Exp : Type :=
| Lit : nat -> Exp
| Var : string -> Exp
| Ann : Exp -> Typ -> Exp
| Abs : string -> Exp -> Exp
| App : Exp -> Exp -> Exp
| Val : V -> Exp.

End NewConstructor.

Definition newcons (c : Con) : Type :=
match c with
| CExt => NewConstructor.V
| _    => unit
end.

Fixpoint f (e : NewConstructor.Exp) : Exp newcons :=
match e with
| NewConstructor.Lit n     => Lit tt n
| NewConstructor.Var v     => Var tt v
| NewConstructor.Ann e' t  => Ann tt (f e') t
| NewConstructor.Abs x e'  => Abs tt x (f e')
| NewConstructor.App e1 e2 => App tt (f e1) (f e2)
| NewConstructor.Val v     => Ext v
end.

Fixpoint g (e : Exp newcons) : NewConstructor.Exp :=
match e with
| Lit _ n     => NewConstructor.Lit n
| Var _ v     => NewConstructor.Var v
| Ann _ e' t  => NewConstructor.Ann (g e') t
| Abs _ x e'  => NewConstructor.Abs x (g e')
| App t e1 e2 => NewConstructor.App (g e1) (g e2)
| Ext v       => NewConstructor.Val v
end.

Lemma fg :
  forall e : NewConstructor.Exp,
    g (f e) = e.
Proof.
  induction e; cbn; congruence.
Qed.

Lemma gf :
  forall e : Exp newcons,
    f (g e) = e.
Proof.
  induction e; cbn; try destruct f0; congruence.
Qed.

End NewConstructor.

(* Generic functions *)
Fixpoint printTyp (t : Typ) : string :=
match t with
| Int => "Int"
| Fun t1 t2 => "(" ++ printTyp t1 ++ ") -> " ++ printTyp t2
end.

Fixpoint printExp
  {f : Con -> Type} (p : f CExt -> string) (e : Exp f) : string :=
match e with
| Lit _ n     => "literal"
| Var _ v     => v
| Ann _ e' t  => printExp p e' ++ " : " ++ printTyp t
| Abs _ v e'  => "lambda " ++ v ++ ". " ++ printExp p e'
| App _ e1 e2 => "(" ++ printExp p e1 ++ ") " ++ printExp p e2
| Ext x       => p x
end.

Definition printUndecorated (e : Exp Undecorated.undecorated) : string :=
  printExp (fun _ => ""%string) e.

Definition printNewField (e : Exp NewField.newfield) : string :=
  printExp (fun _ => ""%string) e.

Definition printNewConstructor (e : Exp NewConstructor.newcons) : string :=
  printExp (fun v => "{{some value lol}}"%string) e.

Module ReplacingConstructor.

Module ReplacingConstructor.

Inductive Exp : Type :=
| Lit : nat -> Exp
| Var : string -> Exp
| Ann : Exp -> Typ -> Exp
| Abs : string -> Exp -> Exp
| App : Exp -> list Exp -> Exp.

End ReplacingConstructor.

(** No i wuj, w Coqu nie da się tego odpowiednio "zawiązać" (tie the knot) bez nadmiernego kombinowania. *)

(* Definition replcons (c : Con) : Type :=
match c with
| CExt => 
| _    => unit
end.
 *)

End ReplacingConstructor.