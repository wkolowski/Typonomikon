Require Import Program.Equality Arith.

From Typonomikon Require Import F2.

Inductive Vec (A : Type) : nat -> Type :=
| vnil : Vec A 0
| vcons : forall n : nat, A -> Vec A n -> Vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} {n}.

Definition vhd {A : Type} {n : nat} (v : Vec A (S n)) : A :=
match v with
| vcons h _ => h
end.

Definition vtl {A : Type} {n : nat} (v : Vec A (S n)) : Vec A n :=
match v with
| vcons _ t => t
end.

Lemma vhd_vtl :
  forall (A : Type) (n : nat) (v : Vec A (S n)),
    v = vcons (vhd v) (vtl v).
Proof.
  dependent destruction v. cbn. reflexivity.
Qed.

Fixpoint vtake {A : Type} (s : Stream A) (n : nat) : Vec A n :=
match n with
| 0 => vnil
| S n' => vcons (hd s) (vtake (tl s) n')
end.

Fixpoint vtake' {A : Type} (s : Stream A) (n : nat) : Vec A (S n) :=
match n with
| 0 => vcons (hd s) vnil
| S n' => vcons (hd s) (vtake' (tl s) n')
end.

CoFixpoint unvtake {A : Type} (f : forall n : nat, Vec A (S n)) : Stream A :=
{|
  hd := vhd (f 0);
  tl := unvtake (fun n : nat => vtl (f (S n)))
|}.

Fixpoint vnth {A : Type} {n : nat} (v : Vec A n) (k : nat) : option A :=
match v, k with
| vnil, _ => None
| vcons h t, 0 => Some h
| vcons h t, S k' => vnth t k'
end.

Ltac depdestr x :=
  let x' := fresh "x" in remember x as x'; dependent destruction x'.

Lemma unvtake_vtake' :
  forall (A : Type) (n : nat) (f : forall n : nat, Vec A (S n)),
    (forall m1 m2 k : nat, k <= m1 -> k <= m2 ->
      vnth (f m1) k = vnth (f m2) k) ->
       vtake' (unvtake f) n = f n.
Proof.
  induction n as [| n']; cbn; intros.
    remember (f 0) as v. dependent destruction v. cbn. f_equal.
      dependent destruction v. reflexivity.
    rewrite IHn'.
      rewrite vhd_vtl. f_equal.
        specialize (H 0 (S n') 0 ltac:(auto) ltac:(apply Nat.le_0_l)).
        depdestr (f 0). depdestr (f (S n')). cbn in *.
        inversion H. reflexivity.
      intros. specialize (H (S m1) (S m2) (S k)).
        depdestr (f (S m1)). depdestr (f (S m2)). cbn in *.
        apply H; apply le_n_S; assumption.
Qed.

Lemma vtake_unvtake :
  forall (A : Type) (s : Stream A),
    sim (unvtake (vtake' s)) s.
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply CH.
Qed.