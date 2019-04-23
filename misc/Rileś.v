(** Rileś: Koindukcja *)

Require Import List.
Import ListNotations.

Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Setoid.
Require Import FinFun.

Require Import NArith.
Require Import Div2.
Require Import ZArith.

(** TODO: napisać coś *)

(** * Koindukcja *)

(** ** Strumienie *)

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A}.
Arguments tl {A}.

CoInductive bisim {A : Type} (s1 s2 : Stream A) : Prop :=
{
    hds : hd s1 = hd s2;
    tls : bisim (tl s1) (tl s2);
}.

Lemma bisim_refl :
  forall (A : Type) (s : Stream A), bisim s s.
Proof.
  cofix CH. constructor; auto.
Qed.

Lemma bisim_sym :
  forall (A : Type) (s1 s2 : Stream A),
    bisim s1 s2 -> bisim s2 s1.
Proof.
  cofix CH.
  destruct 1. constructor; auto.
Qed.

Lemma bisim_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    bisim s1 s2 -> bisim s2 s3 -> bisim s1 s3.
Proof.
  cofix CH.
  destruct 1, 1. constructor; eauto. rewrite hds0. assumption.
Qed.

(** *** Jakieś pierdoły *)

CoFixpoint from' (n : nat) : Stream nat :=
{|
    hd := n;
    tl := from' (S n);
|}.

CoFixpoint facts' (r n : nat) : Stream nat :=
{|
    hd := r;
    tl := facts' (r * S n) (S n);
|}.

Definition facts : Stream nat := facts' 1 0.

Compute stake 9 facts.

(** *** Z manuala Agdy *)

CoFixpoint evens {A : Type} (s : Stream A) : Stream A :=
{|
    hd := hd s;
    tl := evens (tl (tl s));
|}.

CoFixpoint odds {A : Type} (s : Stream A) : Stream A :=
{|
    hd := hd (tl s);
    tl := odds (tl (tl s));
|}.

Definition split {A : Type} (s : Stream A) : Stream A * Stream A :=
  (evens s, odds s).

CoFixpoint merge {A : Type} (ss : Stream A * Stream A) : Stream A :=
{|
    hd := hd (fst ss);
    tl := merge (snd ss, tl (fst ss));
|}.

Lemma merge_split :
  forall (A : Type) (s : Stream A),
    bisim (merge (split s)) s.
Proof.
  cofix CH.
  intros. constructor.
    cbn. reflexivity.
    cbn. constructor.
      cbn. reflexivity.
      cbn. apply CH.
Qed.

(** *** Bijekcja między strumieniami i funkcjami *)

Instance Equiv_bisim (A : Type) : Equivalence (@bisim A).
Proof.
  split; red.
    apply bisim_refl.
    apply bisim_sym.
    apply bisim_trans.
Defined.

CoFixpoint theChosenOne : Stream unit :=
{|
    hd := tt;
    tl := theChosenOne;
|}.

Lemma all_chosen_unit_aux :
  forall s : Stream unit, bisim s theChosenOne.
Proof.
  cofix CH.
  constructor.
    destruct (hd s). cbn. reflexivity.
    cbn. apply CH.
Qed.

Theorem all_chosen_unit :
  forall x y : Stream unit, bisim x y.
Proof.
  intros.
  rewrite (all_chosen_unit_aux x), (all_chosen_unit_aux y).
  reflexivity.
Qed.

Axiom bisim_eq :
  forall (A : Type) (x y : Stream A), bisim x y -> x = y.

Theorem all_eq :
  forall x y : Stream unit, x = y.
Proof.
  intros. apply bisim_eq. apply all_chosen_unit.
Qed.

Definition unit_to_stream (u : unit) : Stream unit := theChosenOne.
Definition stream_to_unit (s : Stream unit) : unit := tt.

Theorem unit_is_Stream_unit :
  Bijective unit_to_stream.
Proof.
  red. exists stream_to_unit.
  split; intros.
    destruct x; trivial.
    apply all_eq.
Qed.

CoFixpoint memo_aux {A : Type} (f : nat -> A) (n : nat) : Stream A :=
{|
    hd := f n;
    tl := memo_aux f (S n);
|}.

Definition memo {A : Type} (f : nat -> A) : Stream A :=
  memo_aux f 0.

Fixpoint index {A : Type} (s : Stream A) (n : nat) : A :=
match n with
    | 0 => hd s
    | S n' => index (tl s) n'
end.

Fixpoint drop {A : Type} (n : nat) (s : Stream A) : Stream A :=
match n with
    | 0 => s
    | S n' => drop n' (tl s)
end.

Lemma tl_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    tl (drop n s) = drop (S n) s.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.

Lemma unfold :
  forall (A : Type) (s : Stream A),
    s = {| hd := hd s; tl := tl s; |}.
Proof.
  destruct s; cbn. reflexivity.
Qed.

Lemma memo_index_aux' :
  forall (f : nat -> nat) (n m : nat),
    bisim (memo_aux f (n + m)) (memo_aux (fun k : nat => f (n + k)) m).
Proof.
  cofix CH.
  constructor.
    cbn. reflexivity.
    cbn. rewrite plus_n_Sm. apply CH.
Qed.

Lemma memo_index_aux :
  forall (A : Type) (s : Stream A) (n : nat),
    bisim (memo_aux (index s) n) (drop n s).
Proof.
  cofix CH.
  constructor.
    revert s. induction n as [| n']; cbn in *; intros.
      reflexivity.
      apply IHn'.
    cbn. rewrite tl_drop. apply CH.
Qed.

Lemma memo_index :
  forall (A : Type) (s : Stream A),
    bisim (memo (index s)) s.
Proof.
  intros. unfold memo. rewrite memo_index_aux. cbn. reflexivity.
Qed.

Lemma index_memo_aux :
  forall (A : Type) (f : nat -> A) (n : nat),
    index (memo_aux f n) = fun k : nat => f (k + n).
Proof.
  intros. extensionality k. revert n.
  induction k as [| k']; cbn; intros.
    reflexivity.
    rewrite IHk'. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma index_memo :
  forall (A : Type) (f : nat -> A),
    index (memo f) = fun k : nat => f k.
Proof.
  intros.
  replace (fun k : nat => f k) with (fun k : nat => f (k + 0)).
    apply index_memo_aux.
    extensionality k. rewrite <- plus_n_O. reflexivity.
Qed.

Lemma natfun_is_stream_nat :
  Bijective (@memo nat).
Proof.
  red. exists index. split; intros.
    apply index_memo.
    apply bisim_eq. apply memo_index.
Defined.

(** *** Trochę losowości *)

CoFixpoint rand (seed n1 n2 : Z) : Stream Z :=
{|
    hd := Zmod seed n2;
    tl := rand (Zmod seed n2 * n1) n1 n2;
|}.

CoFixpoint rand' (seed n1 n2 : Z) : Stream Z :=
{|
    hd := Zmod seed n2;
    tl := rand (Zmod (seed * n1) n2) n1 n2;
|}.

Fixpoint stake {A : Type} (n : nat) (s : Stream A) : list A :=
match n with
    | 0 => []
    | S n' => hd s :: stake n' (tl s)
end.

Compute stake 10 (rand 1 123456789 987654321).
Compute stake 10 (rand' 1235 234567890 6652).

(** ** Kolisty *)

CoInductive Conat : Type :=
{
    pred : option Conat;
}.

CoInductive LList (A : Type) : Type :=
{
    uncons : option (A * LList A);
}.

Arguments uncons {A}.

Fixpoint toLList {A : Type} (l : list A) : LList A :=
{|
    uncons :=
    match l with
        | [] => None
        | h :: t => Some (h, toLList t)
    end
|}.

Lemma toLList_inj :
  forall {A : Set} (l1 l2 : list A),
    toLList l1 = toLList l2 -> l1 = l2.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; inversion 1.
    reflexivity.
    f_equal. apply IHt1. assumption.
Defined.

CoFixpoint from (n : nat) : LList nat :=
{|
    uncons := Some (n, from (S n));
|}.

Definition lhead {A : Type} (l : LList A) : option A :=
match uncons l with
    | Some (a, _) => Some a
    | _ => None
end.

Definition ltail {A : Type} (l : LList A) : option (LList A) :=
match uncons l with
    | Some (_, t) => Some t
    | _ => None
end.

Fixpoint lnth {A : Type} (n : nat) (l : LList A) : option A :=
match n, uncons l with
    | _, None => None
    | 0, Some (x, _) => Some x
    | S n', Some (_, l') => lnth n' l'
end.

Eval compute in lnth 511 (from 0).

Definition nats := from 0.

CoFixpoint repeat {A : Type} (x : A) : LList A :=
{|
    uncons := Some (x, repeat x);
|}.

Eval simpl in lnth 123 (repeat 5).

CoFixpoint lapp {A : Type} (l1 l2 : LList A) : LList A :=
match uncons l1 with
    | None => l2
    | Some (h, t) => {| uncons := Some (h, lapp t l2) |}
end.

(*
CoFixpoint general_omega {A : Set} (l1 l2 : LList A) : LList A :=
match l1, l2 with
    | _, LNil => l1
    | LNil, LCons h' t' => LCons h' (general_omega t' l2)
    | LCons h t, _ => LCons h (general_omega t l2)
end.
*)

CoFixpoint lmap {A B : Type} (f : A -> B) (l : LList A) : LList B :=
{|
    uncons :=
    match uncons l with
        | None => None
        | Some (h, t) => Some (f h, lmap f t)
    end
|}.

Inductive Finite {A : Type} : LList A -> Prop :=
    | Finite_nil : Finite {| uncons := None |}
    | Finite_cons :
        forall (h : A) (t : LList A),
          Finite t -> Finite {| uncons := Some (h, t) |}.

CoInductive Infinite {A : Type} (l : LList A) : Prop :=
{
    h : A;
    t : LList A;
    p : uncons l = Some (h, t);
    inf' : Infinite t;
}.

Lemma empty_not_Infinite :
  forall A : Type, ~ Infinite {| uncons := @None (A * LList A) |}.
Proof.
  intros A []. cbn in p. inversion p.
Qed.

Lemma lmap_Infinite :
  forall (A B : Type) (f : A -> B) (l : LList A),
    Infinite l -> Infinite (lmap f l).
Proof.
  cofix CH.
  destruct 1. econstructor.
    cbn. rewrite p. reflexivity.
    apply CH. assumption.
Qed.

Lemma lapp_Infinite_l :
  forall (A : Type) (l1 l2 : LList A),
    Infinite l1 -> Infinite (lapp l1 l2).
Proof.
  cofix CH.
  destruct 1. econstructor.
    destruct l1; cbn in *; inversion p; cbn. reflexivity.
    apply CH. assumption.
Qed.

Lemma lapp_Infinite_r :
  forall (A : Type) (l1 l2 : LList A),
    Infinite l2 -> Infinite (lapp l1 l2).
Proof.
  cofix CH.
  destruct l1 as [[[h t] |]]; intros.
    econstructor.
      cbn. reflexivity.
      apply CH. assumption.
    destruct H. econstructor.
      lazy. destruct l2; cbn in *. rewrite p. reflexivity.
      assumption.
Qed.

Lemma Finite_not_Infinite :
  forall (A : Type) (l : LList A),
    Finite l -> ~ Infinite l.
Proof.
  induction 1; intro.
    inversion H. cbn in p. inversion p.
    apply IHFinite. inversion H0; inversion p; subst. assumption.
Qed.

(*
Lemma Infinite_not_Finite :
  forall (A : Type) (l : LList A),
    Infinite l -> ~ Finite l.
Proof.
  induction 2.
    inversion H. inversion p.
    apply IHFinite. inversion H; inversion p; subst. assumption.
Qed.
*)

CoInductive bisim2 {A : Type} (l1 l2 : LList A) : Prop :=
{
    bisim2' :
      uncons l1 = None /\ uncons l2 = None \/
      exists (h1 : A) (t1 : LList A) (h2 : A) (t2 : LList A),
        uncons l1 = Some (h1, t1) /\
        uncons l2 = Some (h2, t2) /\
          h1 = h2 /\ bisim2 t1 t2
}.

Hint Constructors bisim2.

Lemma bisim2_refl :
  forall (A : Type) (l : LList A), bisim2 l l.
Proof.
  cofix CH.
  destruct l as [[[h t]|]].
    constructor. right. exists h, t, h, t; auto.
    constructor. left. cbn. split; reflexivity.
Qed.

Lemma bisim2_symm :
  forall (A : Type) (l1 l2 : LList A),
    bisim2 l1 l2 -> bisim2 l2 l1.
Proof.
  cofix CH.
  destruct 1 as [[[] | (h1 & t1 & h2 & t2 & p1 & p2 & p3 & H)]].
    constructor. left. split; assumption.
    constructor. right. exists h2, t2, h1, t1. auto.
Qed.

Lemma bisim2_trans :
  forall (A : Type) (l1 l2 l3 : LList A),
    bisim2 l1 l2 -> bisim2 l2 l3 -> bisim2 l1 l3.
Proof.
  cofix CH.
  destruct 1 as [[[] | (h11 & t11 & h12 & t12 & p11 & p12 & p13 & H1)]],
           1 as [[[] | (h21 & t21 & h22 & t22 & p21 & p22 & p23 & H2)]];
  subst.
    auto.
    rewrite H0 in p21. inversion p21.
    rewrite H in p12. inversion p12.
    rewrite p12 in p21; inversion p21; subst.
      econstructor. right. exists h22, t11, h22, t22.
        do 3 try split; auto. eapply CH; eauto.
Qed.

Lemma lmap_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : LList A),
    bisim2 (lmap g (lmap f l)) (lmap (fun x => g (f x)) l).
Proof.
  cofix CH.
  constructor. destruct l as [[[h t]|]]; [right | left]; cbn.
    exists (g (f h)), (lmap g (lmap f t)),
           (g (f h)), (lmap (fun x => g (f x)) t).
      repeat (split; [reflexivity | idtac]). apply CH.
    do 2 split.
Qed.

Lemma bisim2_Infinite :
  forall (A : Type) (l1 l2 : LList A),
    bisim2 l1 l2 -> Infinite l1 -> Infinite l2.
Proof.
  cofix CH.
  destruct 1 as [[[] | (h1 & t1 & h2 & t2 & p1 & p2 & p3 & H)]], 1.
    rewrite H in p. inversion p.
    econstructor.
      exact p2.
      rewrite p1 in p. inversion p; subst. eapply CH; eauto.
Qed.

(** ** Drzewka *)

CoInductive coBTree (A : Type) : Type :=
{
    root : option (coBTree A * A * coBTree A)
}.

Arguments root {A} _.

CoFixpoint fmap {A B : Type} (f : A -> B) (t : coBTree A) : coBTree B :=
{|
    root :=
    match root t with
        | None => None
        | Some (l, v, r) => Some (fmap f l, f v, fmap f r)
    end
|}.

CoFixpoint ns (n : nat) : coBTree nat :=
{|
    root := Some (ns (1 + 2 * n), n, ns (2 + 2 * n))
|}.

Inductive BTree (A : Type) : Type :=
    | Empty : BTree A
    | Node : A -> BTree A -> BTree A -> BTree A.

Arguments Empty {A}.
Arguments Node {A} _ _ _.

Fixpoint ttake (n : nat) {A : Type} (t : coBTree A) : BTree A :=
match n with
    | 0 => Empty
    | S n' =>
        match root t with
            | None => Empty
            | Some (l, v, r) => Node v (ttake n' l) (ttake n' r)
        end
end.

Compute ttake 5 (ns 0).

CoInductive tsim {A : Type} (t1 t2 : coBTree A) : Prop :=
{
    tsim' :
      root t1 = None /\ root t2 = None \/
      exists (v1 v2 : A) (l1 l2 r1 r2 : coBTree A),
        root t1 = Some (l1, v1, r1) /\
        root t2 = Some (l2, v2, r2) /\
          tsim l1 l2 /\ tsim r1 r2
}.

CoFixpoint mirror {A : Type} (t : coBTree A) : coBTree A :=
{|
    root :=
      match root t with
          | None => None
          | Some (l, v, r) => Some (mirror r, v, mirror l)
      end
|}.

Lemma tsim_mirror_inv :
  forall (A : Type) (t : coBTree A),
    tsim (mirror (mirror t)) t.
Proof.
  cofix CH.
  destruct t as [[[[l v] r]|]]; constructor; [right | left]. cbn.
    exists v, v, (mirror (mirror l)), l, (mirror (mirror r)), r. auto.
    auto.
Qed.

(** ** Rekursja ogólna *)

CoInductive Div (A : Type) : Type :=
{
    call : A + Div A
}.

Fixpoint even (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
end.

(* The name is very unfortunate. *)
CoFixpoint collatz (n : nat) : Div unit :=
{|
    call :=
    match n with
        | 0 | 1 => inl tt
        | n' =>
            if even n'
            then inr (collatz (div2 n'))
            else inr (collatz (1 + 3 * n'))
    end
|}.

Print Div.

Fixpoint fuel (n : nat) {A : Type} (d : Div A) : option A :=
match n, d with
    | 0, _ => None
    | _, Build_Div _ (inl a) => Some a
    | S n', Build_Div _ (inr d') => fuel n' d'
end.

Compute fuel 5 (collatz 4).

Arguments uncons {A} _.

CoFixpoint collatz' (n : nat) : LList nat :=
match n with
    | 0 => {| uncons := None |}
    | 1 => {| uncons := Some (1, {| uncons := None |}) |}
    | n' =>
        if even n'
        then {| uncons := Some (n', collatz' (div2 n')) |}
        else {| uncons := Some (n', collatz' (1 + 3 * n')) |}
end.

Fixpoint take (n : nat) {A : Type} (l : LList A) : list A :=
match n, uncons l with
    | 0, _ => []
    | _, None => []
    | S n', Some (h, t) => h :: take n' t
end.

Compute map (fun n : nat => take 200 (collatz' n)) [30; 31; 32; 33].
Compute take 150 (collatz' 12344).

(** insertion sort na kolistach *)

CoFixpoint ins (n : nat) (s : LList nat) : LList nat :=
{|
    uncons :=
      match uncons s with
          | None => None
          | Some (h, t) =>
              if n <=? h
              then
                Some (n, {| uncons := Some (h, t) |})
              else
                Some (h, ins n t)
      end
|}.

(*
CoFixpoint ss (s : LList nat) : LList nat :=
{|
    uncons :=
      match uncons s with
          | None => None
          | Some (h, t) =>
              match uncons (ss t) with
                  | None => None
                  | Some (h', t') => Some (h', ins h t')
              end
      end
|}.
*)