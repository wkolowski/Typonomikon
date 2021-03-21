Require Import Bool List.
Import ListNotations.

(** Przykład cbn wzięty z pracy "Another Look at Nested Recursion" *)

Variable Var : Type.
Hypothesis veq : Var -> Var -> bool.
Hypothesis veq_spec : forall x y : Var, reflect (x = y) (veq x y).

Inductive Term (A : Type) : Type :=
    | C : nat -> Term A
    | V : A -> Term A
    | Add : Term A -> Term A -> Term A
    | App : Term A -> A (*Term A*) -> Term A -> Term A.

Arguments C   {A} _.
Arguments V   {A} _.
Arguments Add {A} _ _.
Arguments App {A} _ _ _.

Definition Env : Type := list (Var * nat).

Fixpoint lookup (v : Var) (env : Env) : nat :=
match env with
    | [] => 0
    | (x, n) :: env' => if veq v x then n else lookup v env'
end.

Fixpoint cbv (t : Term Var) (env : Env) : nat :=
match t with
    | C n => n
    | V v => lookup v env
    | Add t1 t2 => plus (cbv t1 env) (cbv t2 env)
    | App t1 x t2 => cbv t1 ((x, cbv t2 env) :: env)
end.

Inductive cbnG : Term Var -> Var -> Term Var -> Term Var -> Type :=
    | cbnG_C :
        forall (n : nat) (y : Var) (z : Term Var), cbnG (C n) y z (C n)
    | cbnG_V_eq :
        forall (y : Var) (z r : Term Var),
          cbnhG z r -> cbnG (V y) y z r
    | cbnG_V_neq :
        forall (v y : Var) (z : Term Var),
          v <> y -> cbnG (V v) y z (V v)
    | cbnG_Add :
        forall (t1 t2 : Term Var) (y : Var) (z r1 r2 : Term Var),
          cbnG t1 y z r1 -> cbnG t2 y z r2 ->
            cbnG (Add t1 t2) y z (Add r1 r2)
    | cbnG_App :
        forall (t1 t2 : Term Var) (x y : Var) (z r1 r2 : Term Var),
          cbnG t1 x t2 r1 -> cbnG r1 y z r2 ->
            cbnG (App t1 x t2) y z r2

with cbnhG : Term Var -> Term Var -> Type :=
    | cbnhG_C :
        forall n : nat, cbnhG (C n) (C n)
    | cbnhG_V :
        forall x : Var, cbnhG (V x) (V x)
    | cbnhG_Add :
        forall t1 t2 r1 r2 : Term Var,
          cbnhG t1 r1 -> cbnhG t2 r2 -> cbnhG (Add t1 t2) (Add r1 r2)
    | cbnhG_App :
        forall (t1 t2 : Term Var) (x : Var) (r : Term Var),
          cbnG t1 x t2 r -> cbnhG (App t1 x t2) r.

Inductive cbnD : Term Var -> Var -> Term Var -> Type :=
    | cbnD_C :
        forall (n : nat) (y : Var) (z : Term Var), cbnD (C n) y z
    | cbnD_V_eq :
        forall (y : Var) (z : Term Var),
          cbnhD z -> cbnD (V y) y z
    | cbnD_V_neq :
        forall (v y : Var) (z : Term Var),
          v <> y -> cbnD (V v) y z
    | cbnD_Add :
        forall (t1 t2 : Term Var) (y : Var) (z : Term Var),
          cbnD t1 y z -> cbnD t2 y z ->
            cbnD (Add t1 t2) y z
    | cbnD_App :
        forall (t1 t2 : Term Var) (x y : Var) (z r : Term Var),
          cbnG t1 x t2 r -> cbnD r y z ->
            cbnD (App t1 x t2) y z

with cbnhD : Term Var -> Type :=
    | cbnhD_C :
        forall n : nat, cbnhD (C n)
    | cbnhD_V :
        forall x : Var, cbnhD (V x)
    | cbnhD_Add :
        forall t1 t2 : Term Var,
          cbnhD t1 -> cbnhD t2 -> cbnhD (Add t1 t2)
    | cbnhD_App :
        forall (t1 t2 : Term Var) (x : Var),
          cbnD t1 x t2 -> cbnhD (App t1 x t2).

Fixpoint cbn
  {t : Term Var} {y : Var} {z : Term Var} (d : cbnD t y z) : Term Var :=
match d with
    | cbnD_C n _ _ => C n
    | cbnD_V_eq _ _ dz => cbnh dz
    | cbnD_V_neq v _ _ _ => V v
    | cbnD_Add _ _ _ _ d1 d2 => Add (cbn d1) (cbn d2)
    | cbnD_App _ _ _ _ _ _ _ d' => cbn d'
end

with cbnh {t : Term Var} (d : cbnhD t) : Term Var :=
match d with
    | cbnhD_C n => C n
    | cbnhD_V x => V x
    | cbnhD_Add _ _ d1 d2 => Add (cbnh d1) (cbnh d2)
    | cbnhD_App _ _ _ d' => cbn d'
end.

Lemma cbnG_cbn :
  forall (t : Term Var) (y : Var) (z : Term Var) (d : cbnD t y z),
    cbnG t y z (cbn d)

with cbnhG_cbnh :
  forall (t : Term Var) (d : cbnhD t),
    cbnhG t (cbnh d).
Proof.
  destruct d; cbn.
    constructor.
    constructor. apply cbnhG_cbnh.
    constructor. assumption.
    constructor; apply cbnG_cbn.
    econstructor.
      exact c.
      apply cbnG_cbn.
  destruct d; cbn.
    constructor.
    constructor.
    constructor; apply cbnhG_cbnh.
    constructor. apply cbnG_cbn.
Restart.
  all: destruct d; cbn; econstructor; eauto.
Qed.