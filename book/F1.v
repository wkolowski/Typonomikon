(** * F1: Koindukcja i korekursja [TODO] *)

(* begin hide *)

(** Pamiętać o tym, że przy negatywnej koindukcji kryterium ścisłej
    pozytywnośći też obowiązuje. Powody są mniej więcej takie jak dla
    typów induktywnych. *)

Fail CoInductive wut : Type :=
{
    haha : wut -> Prop;
}.

(** Ciężko mi jednak stwierdzić w tej chwili, czy jest jakiś odpowiednik
    problemów z nieterminacją. NIEPRODUKTYWNOŚĆ! *)

(* end hide *)

Require Import List.
Import ListNotations.

Require Import FunctionalExtensionality.
Require Import Setoid.
Require Import FinFun.

Require Import NArith.
Require Import Div2.
Require Import ZArith.

(** * Koindukcja (TODO) *)

(** ** Strumienie (TODO) *)

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
  destruct 1 as [hds tls]. constructor; auto.
Qed.

Lemma bisim_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    bisim s1 s2 -> bisim s2 s3 -> bisim s1 s3.
Proof.
  cofix CH.
  destruct 1 as [hds1 tls1], 1 as [hds2 tls2].
  constructor; eauto. rewrite hds1. assumption.
Qed.

(** *** Jakieś pierdoły (TODO) *)

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

(*Compute stake 9 facts.*)

(** *** Przykład z manuala Agdy (TODO) *)

(**
    hd (evens s) := hd s;
    tl (evens s) := evens (tl (tl s));
*)

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

(** *** Bijekcja między [Stream unit] i [unit] (TODO) *)

Instance Equiv_bisim (A : Type) : Equivalence (@bisim A).
(* begin hide *)
Proof.
  split; red.
    apply bisim_refl.
    apply bisim_sym.
    apply bisim_trans.
Defined.
(* end hide *)

CoFixpoint theChosenOne : Stream unit :=
{|
    hd := tt;
    tl := theChosenOne;
|}.

Lemma all_chosen_unit_aux :
  forall s : Stream unit, bisim s theChosenOne.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
    destruct (hd s). cbn. reflexivity.
    cbn. apply CH.
Qed.
(* end hide *)

Lemma all_chosen_unit :
  forall x y : Stream unit, bisim x y.
(* begin hide *)
Proof.
  intros.
  rewrite (all_chosen_unit_aux x), (all_chosen_unit_aux y).
  reflexivity.
Qed.
(* end hide *)

Axiom bisim_eq :
  forall (A : Type) (x y : Stream A), bisim x y -> x = y.

Theorem all_eq :
  forall x y : Stream unit, x = y.
(* begin hide *)
Proof.
  intros. apply bisim_eq. apply all_chosen_unit.
Qed.
(* end hide *)

Definition unit_to_stream (u : unit) : Stream unit := theChosenOne.
Definition stream_to_unit (s : Stream unit) : unit := tt.

Lemma unit_is_Stream_unit :
  Bijective unit_to_stream.
(* begin hide *)
Proof.
  red. exists stream_to_unit.
  split; intros.
    destruct x; trivial.
    apply all_eq.
Qed.
(* end hide *)

(** *** Trochę losowości (TODO) *)

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

(** ** Kolisty (TODO) *)

CoInductive Conat : Type :=
{
    pred : option Conat;
}.

CoInductive coList (A : Type) : Type :=
{
    uncons : option (A * coList A);
}.

Arguments uncons {A}.

Fixpoint tocoList {A : Type} (l : list A) : coList A :=
{|
    uncons :=
    match l with
        | [] => None
        | h :: t => Some (h, tocoList t)
    end
|}.

Lemma tocoList_inj :
  forall {A : Set} (l1 l2 : list A),
    tocoList l1 = tocoList l2 -> l1 = l2.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; inversion 1.
    reflexivity.
    f_equal. apply IHt1. assumption.
Defined.

CoFixpoint from (n : nat) : coList nat :=
{|
    uncons := Some (n, from (S n));
|}.

Definition lhead {A : Type} (l : coList A) : option A :=
match uncons l with
    | Some (a, _) => Some a
    | _ => None
end.

Definition ltail {A : Type} (l : coList A) : option (coList A) :=
match uncons l with
    | Some (_, t) => Some t
    | _ => None
end.

Fixpoint lnth {A : Type} (n : nat) (l : coList A) : option A :=
match n, uncons l with
    | _, None => None
    | 0, Some (x, _) => Some x
    | S n', Some (_, l') => lnth n' l'
end.

Eval compute in lnth 511 (from 0).

Definition nats := from 0.

CoFixpoint repeat {A : Type} (x : A) : coList A :=
{|
    uncons := Some (x, repeat x);
|}.

Eval cbn in lnth 123 (repeat 5).

CoFixpoint lapp {A : Type} (l1 l2 : coList A) : coList A :=
match uncons l1 with
    | None => l2
    | Some (h, t) => {| uncons := Some (h, lapp t l2) |}
end.

CoFixpoint lmap {A B : Type} (f : A -> B) (l : coList A) : coList B :=
{|
    uncons :=
    match uncons l with
        | None => None
        | Some (h, t) => Some (f h, lmap f t)
    end
|}.

Inductive Finite {A : Type} : coList A -> Prop :=
    | Finite_nil : Finite {| uncons := None |}
    | Finite_cons :
        forall (h : A) (t : coList A),
          Finite t -> Finite {| uncons := Some (h, t) |}.

CoInductive Infinite {A : Type} (l : coList A) : Prop :=
{
    h : A;
    t : coList A;
    p : uncons l = Some (h, t);
    inf' : Infinite t;
}.

Lemma empty_not_Infinite :
  forall A : Type, ~ Infinite {| uncons := @None (A * coList A) |}.
Proof.
  intros A []. cbn in p. inversion p.
Qed.

Lemma lmap_Infinite :
  forall (A B : Type) (f : A -> B) (l : coList A),
    Infinite l -> Infinite (lmap f l).
Proof.
  cofix CH.
  destruct 1. econstructor.
    cbn. rewrite p. reflexivity.
    apply CH. assumption.
Qed.

Lemma lapp_Infinite_l :
  forall (A : Type) (l1 l2 : coList A),
    Infinite l1 -> Infinite (lapp l1 l2).
Proof.
  cofix CH.
  destruct 1. econstructor.
    destruct l1; cbn in *; inversion p; cbn. reflexivity.
    apply CH. assumption.
Qed.

Lemma lapp_Infinite_r :
  forall (A : Type) (l1 l2 : coList A),
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
  forall (A : Type) (l : coList A),
    Finite l -> ~ Infinite l.
Proof.
  induction 1; intro.
    inversion H. cbn in p. inversion p.
    apply IHFinite. inversion H0; inversion p; subst. assumption.
Qed.

CoInductive bisim2 {A : Type} (l1 l2 : coList A) : Prop :=
{
    bisim2' :
      uncons l1 = None /\ uncons l2 = None \/
      exists (h1 : A) (t1 : coList A) (h2 : A) (t2 : coList A),
        uncons l1 = Some (h1, t1) /\
        uncons l2 = Some (h2, t2) /\
          h1 = h2 /\ bisim2 t1 t2
}.

Hint Constructors bisim2.

Lemma bisim2_refl :
  forall (A : Type) (l : coList A), bisim2 l l.
Proof.
  cofix CH.
  destruct l as [[[h t]|]].
    constructor. right. exists h, t, h, t; auto.
    constructor. left. cbn. split; reflexivity.
Qed.

Lemma bisim2_symm :
  forall (A : Type) (l1 l2 : coList A),
    bisim2 l1 l2 -> bisim2 l2 l1.
Proof.
  cofix CH.
  destruct 1 as [[[] | (h1 & t1 & h2 & t2 & p1 & p2 & p3 & H)]].
    constructor. left. split; assumption.
    constructor. right. exists h2, t2, h1, t1. auto.
Qed.

Lemma bisim2_trans :
  forall (A : Type) (l1 l2 l3 : coList A),
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
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : coList A),
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
  forall (A : Type) (l1 l2 : coList A),
    bisim2 l1 l2 -> Infinite l1 -> Infinite l2.
Proof.
  cofix CH.
  destruct 1 as [[[] | (h1 & t1 & h2 & t2 & p1 & p2 & p3 & H)]], 1.
    rewrite H in p. inversion p.
    econstructor.
      exact p2.
      rewrite p1 in p. inversion p; subst. eapply CH; eauto.
Qed.

(** ** Drzewka (TODO) *)

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

(** ** Rekursja ogólna (TODO) *)

(* begin hide *)
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

CoFixpoint collatz' (n : nat) : coList nat :=
match n with
    | 0 => {| uncons := None |}
    | 1 => {| uncons := Some (1, {| uncons := None |}) |}
    | n' =>
        if even n'
        then {| uncons := Some (n', collatz' (div2 n')) |}
        else {| uncons := Some (n', collatz' (1 + 3 * n')) |}
end.

Fixpoint take (n : nat) {A : Type} (l : coList A) : list A :=
match n, uncons l with
    | 0, _ => []
    | _, None => []
    | S n', Some (h, t) => h :: take n' t
end.

Compute map (fun n : nat => take 200 (collatz' n)) [30; 31; 32; 33].
Compute take 150 (collatz' 12344).

(** TODO: insertion sort na kolistach *)

CoFixpoint ins (n : nat) (s : coList nat) : coList nat :=
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

CoFixpoint ss (s : coList nat) : coList nat :=
{|
    uncons :=
      match uncons s with
          | None => None
          | Some (h, t) =>
              match uncons (ins h t) with
                  | None => None
                  | Some (h', t') => Some (h', ss t')
              end
      end
|}.
(* end hide *)

(* begin hide *)
(** TODO: końcówka kolistowego burdla *)

Ltac inv H := inversion H; subst; clear H.

(*
CoInductive Rev {A : Type} (l r : coList A) : Prop :=
{
    Rev' :
      (uncons l = None /\ uncons r = None)
      \/
      exists (h : A) (tl tr : coList A),
        uncons l = Some (h, tl) /\ r = snoc tr h /\ Rev tl tr
}.

Lemma Rev_wut :
  forall (A : Type) (l r : coList A),
    Infinite l -> Infinite r -> Rev l r.
(* begin hide *)
Proof.
  cofix CH.
  constructor. right. destruct H, H0.
  exists h, t, r. split.
    assumption.
    split.
      Focus 2. apply CH; auto; econstructor; eauto.
      apply eq_lsim. apply lsim_symm. apply Infinite_snoc. econstructor; eauto.
Qed.
(* end hide *)

Lemma Rev_Finite :
  forall (A : Type) (l r : coList A),
    Rev l r -> Finite r -> Finite l.
(* begin hide *)
Proof.
  intros A l r HRev H. revert l HRev.
  induction H as [r H | h t r' H IH]; intros.
    destruct HRev as [[[H1 H2] | (h & tl & tr & H1 & H2 & H3)]].
      left. assumption.
      subst. cbn in H. destruct (uncons tr) as [[]|]; inv H.
    destruct HRev as [[[H1 H2] | (h' & tl & tr & H1 & H2 & H3)]].
      congruence.
      subst.
Abort.
(* end hide *)

Lemma Rev_Finite :
  forall (A : Type) (l r : coList A),
    Rev l r -> Finite l -> Finite r.
(* begin hide *)
Proof.
  intros A l r HRev H. revert r HRev.
  induction H; intros.
    destruct HRev as [[[H1 H2] | (h & tl & tr & H1 & H2 & H3)]].
      left. assumption.
      subst. congruence.
    destruct HRev as [[[H1 H2] | (h' & tl & tr & H1 & H2 & H3)]].
      congruence.
      subst. rewrite H1 in H. inv H. apply Finite_snoc, IHFinite.
        assumption.
Qed.
(* end hide *)

Lemma Infinite_Rev :
  forall (A : Type) (l r : coList A),
    Rev l r -> Infinite l -> Infinite r.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1. (* decompose [ex or and] Revc0; clear Revc0.
    destruct 1. congruence.
    intro. subst. destruct x1 as [[[h t] |]]; cbn.
      econstructor.
        cbn. reflexivity.
        apply (CH _ (cocons x t)).
          constructor. cbn. right. exists x, t, t. auto.
      congruence.
      subst. cbn in *. inversion p; subst. *)
Abort.
(* end hide *)

Lemma Finite_cocons :
  forall (A : Type) (x : A) (l : coList A),
    Finite l -> Finite (cocons x l).
(* begin hide *)
Proof.
  intros. apply (Finite_Some x l); auto.
Qed.
(* end hide *)

Fixpoint fromList {A : Type} (l : list A) : coList A :=
{|
    uncons :=
    match l with
        | [] => None
        | h :: t => Some (h, fromList t)
    end
|}.

Lemma fromList_inj  :
  forall {A : Set} (l1 l2 : list A),
    fromList l1 = fromList l2 -> l1 = l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; inversion 1.
    reflexivity.
    f_equal. apply IHt1. assumption.
Defined.
*)
(* end hide *)

(** * Ćwiczenia (TODO) *)

(** **** Ćwiczenie *)

(** Zdefiniuj typ potencjalnie nieskończonych drzew binarnych trzymających
    wartości typu [A] w węzłach, jego relację bipodobieństwa, predykaty
    "skończony" i "nieskończony" oraz funkcję [mirror], która zwraca
    lustrzane odbicie drzewa. Udowodnij, że bipodobieństwo jest relacją
    równoważności i że funkcja [mirror] jest inwolucją (tzn.
    [mirror (mirror t)] jest bipodobne do [t]), która zachowuje właściwości
    bycia drzewem skończonym/nieskończonym. Pokaż, że drzewo nie może być
    jednocześnie skończone i nieskończone. *)

(* begin hide *)
Module Zad1.

CoInductive coBTree (A : Type) : Type :=
{
    tree : option (coBTree A * A * coBTree A)
}.

Arguments tree {A} _.

CoInductive sim {A : Type} (t1 t2 : coBTree A) : Prop :=
{
    sim' :
      tree t1 = None /\ tree t2 = None \/
      exists (v1 v2 : A) (l1 l2 r1 r2 : coBTree A),
        tree t1 = Some (l1, v1, r1) /\
        tree t2 = Some (l2, v2, r2) /\
          sim l1 l2 /\ sim r1 r2
}.

Lemma sim_refl :
  forall (A : Type) (t : coBTree A), sim t t.
Proof.
  cofix CH.
  constructor.
  destruct t as [[[[l v] r] |]]; cbn.
    right. eauto 10.
    left. auto.
Qed.

Lemma sim_sym :
  forall (A : Type) (t1 t2 : coBTree A),
    sim t1 t2 -> sim t2 t1.
Proof.
  cofix CH.
  constructor.
  destruct H as [H]; decompose [ex or and] H; clear H; eauto 20.
Qed.

Lemma sim_trans :
  forall (A : Type) (t1 t2 t3 : coBTree A),
    sim t1 t2 -> sim t2 t3 -> sim t1 t3.
Proof.
  cofix CH.
  constructor.
  destruct H as [H], H0 as [H0].
  decompose [ex or and] H; decompose [ex or and] H0; clear H H0.
    auto.
    1-2: congruence.
    rewrite H1 in H6. inversion H6; subst; clear H6. eauto 15.
Qed.

CoFixpoint mirror {A : Type} (t : coBTree A) : coBTree A :=
{|
    tree :=
      match tree t with
          | None => None
          | Some (l, v, r) => Some (mirror r, v, mirror l)
      end
|}.

Lemma mirror_involution :
  forall (A : Type) (t : coBTree A),
    sim (mirror (mirror t)) t.
Proof.
  cofix CH.
  destruct t as [[[[l v] r] |]];
  constructor; [right | left].
    exists v, v, (mirror (mirror l)), l, (mirror (mirror r)), r. auto.
    auto.
Qed.

Inductive Finite {A : Type} : coBTree A -> Prop :=
    | Finite_None : forall t : coBTree A, tree t = None -> Finite t
    | Finite_Some :
        forall (v : A) (l r t : coBTree A),
          Finite l -> Finite r ->
          tree t = Some (l, v, r) -> Finite t.

CoInductive Infinite {A : Type} (t : coBTree A) : Prop :=
{
    root : A;
    left : coBTree A;
    right : coBTree A;
    p : tree t = Some (left, root, right);
    Infinite_left : Infinite left;
    Infinite_right : Infinite right;
}.

Lemma Finite_mirror :
  forall (A : Type) (t : coBTree A),
    Finite t -> Finite (mirror t).
Proof.
  induction 1.
    constructor. cbn. rewrite H. reflexivity.
    eapply Finite_Some.
      exact IHFinite2.
      exact IHFinite1.
      cbn. rewrite H1. reflexivity.
Qed.

Lemma Infinite_mirror :
  forall (A : Type) (t : coBTree A),
    Infinite t -> Infinite (mirror t).
Proof.
  cofix CH.
  inversion 1. econstructor.
    cbn. rewrite p. reflexivity.
    apply CH; assumption.
    apply CH; assumption.
Qed.

Lemma Finite_Infinite_contradiction :
  forall (A : Type) (t : coBTree A),
    Finite t -> Infinite t -> False.
Proof.
  induction 1; inversion 1; subst; congruence.
Qed.

Lemma Finite_or_Infinite : (* TODO: dla coBTree *)
  forall {A : Type} (t : coBTree A),
    ~ ~ (Finite t \/ Infinite t).
Proof.
  intros A t H.
  apply H. right.
  revert t H. cofix CH.
  intros t H.
  destruct t as [[[[l x] r] |]].
    econstructor.
      cbn. reflexivity.
      apply CH. destruct 1.
        apply H. left.
Abort.
End Zad1.
(* end hide *)

(** **** Ćwiczenie *)

(** Znajdź taką rodzinę typów koinduktywnych [C], że dla dowolnego
    typu [A], [C A] jest w bijekcji z typem funkcji [nat -> A]. Przez
    bijekcję będziemy tu rozumieć funkcję, która ma odwrotność, z którą
    w obie strony składa się do identyczności.

    Uwaga: nie da się tego udowodnić bez użycia dodatkowych aksjomatów,
    które na szczęście są bardzo oczywiste i same się narzucają. *)

(* begin hide *)
Module Zad2.

Require Import FunctionalExtensionality.
Require Import FinFun.

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A}.
Arguments tl {A}.

CoInductive sim {A : Type} (s1 s2 : Stream A) : Prop :=
{
    hds : hd s1 = hd s2;
    tls : sim (tl s1) (tl s2);
}.

Axiom sim_eq :
  forall (A : Type) (s1 s2 : Stream A), sim s1 s2 -> s1 = s2.

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

Lemma memo_index_aux' :
  forall (f : nat -> nat) (n m : nat),
    sim (memo_aux f (n + m)) (memo_aux (fun k : nat => f (n + k)) m).
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    rewrite plus_n_Sm. apply CH.
Qed.

Lemma memo_index_aux :
  forall (A : Type) (s : Stream A) (n : nat),
    sim (memo_aux (index s) n) (drop n s).
Proof.
  cofix CH.
  constructor; cbn.
    revert s. induction n as [| n']; cbn in *; intros.
      reflexivity.
      apply IHn'.
    rewrite tl_drop. apply CH.
Qed.

Lemma memo_index :
  forall (A : Type) (s : Stream A),
    sim (memo (index s)) s.
Proof.
  intros. unfold memo. apply memo_index_aux.
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
    apply sim_eq. apply memo_index.
Qed.

End Zad2.
(* end hide *)

(** **** Ćwiczenie *)

(** Zdefiniuj pojęcie "nieskończonego łańcucha malejącego" (oczywiście
    za pomocą koindukcji) i udowodnij, że jeżeli relacja jest dobrze
    ufundowana, to nie ma nieskończonych łańcuchów malejących. *)

(* begin hide *)
Module Zad5.

CoInductive DecChain {A : Type} (R : A -> A -> Prop) (x : A) : Type :=
{
    hd : A;
    R_hd_x : R hd x;
    tl : DecChain R hd;
}.

Lemma wf_no_DecChain :
  forall (A : Type) (R : A -> A -> Prop) (x : A),
    well_founded R -> DecChain R x -> False.
Proof.
  unfold well_founded.
  intros A R x H C.
  specialize (H x).
  induction H.
  inversion C.
  apply H0 with hd0; assumption.
Qed.

End Zad5.
(* end hide *)