(** * H2z: Izomorfizmy typów [TODO] *)

Require Import Equality.

From Typonomikon Require Import H2.

(** * Definicja izomorfizmu typów (TODO) *)

Class iso (A B : Type) : Type :=
{
  coel : A -> B;
  coer : B -> A;
  coel_coer : forall a : A, coer (coel a) = a;
  coer_coel : forall b : B, coel (coer b) = b;
}.

Arguments coel {A B} _.
Arguments coer {A B} _.

#[export]
Instance iso_refl (A : Type) : iso A A :=
{
  coel := id;
  coer := id;
  coel_coer _ := eq_refl;
  coer_coel _ := eq_refl;
}.

#[export]
Instance iso_sym {A B : Type} (i : iso A B) : iso B A :=
{
  coel := coer i;
  coer := coel i;
  coel_coer := coer_coel;
  coer_coel := coel_coer;
}.

#[refine]
#[export]
Instance iso_trans
  {A B C : Type} (i : iso A B) (j : iso B C) : iso A C :=
{
  coel a := coel j (coel i a);
  coer c := coer i (coer j c);
}.
Proof.
  - now intros; rewrite 2!coel_coer.
  - now intros; rewrite 2!coer_coel.
Defined.

(** * Podstawowe typy *)

(** ** Produkty *)

#[refine]
#[export]
Instance prod_unit_l (A : Type) : iso (unit * A) A :=
{
  coel '(_, a) := a;
  coer a := (tt, a);
}.
Proof.
  - now intros [[]].
  - easy.
Defined.

#[refine]
#[export]
Instance prod_unit_r (A : Type) : iso (A * unit) A :=
{
  coel '(a, _) := a;
  coer a := (a, tt);
}.
Proof.
  - now intros [a []].
  - easy.
Defined.

#[refine, export]
Instance prod_empty_l (A : Type) : iso (Empty_set * A) Empty_set :=
{
  coel '(e, _) := match e with end;
  coer e := match e with end;
}.
Proof.
  - now intros [[] _].
  - now intros [].
Defined.

#[refine, export]
Instance prod_empty_r (A : Type) : iso (A * Empty_set) Empty_set :=
{
  coel '(_, e) := match e with end;
  coer e := match e with end;
}.
Proof.
  - now intros [_ []].
  - now intros [].
Defined.

#[refine]
#[export]
Instance prod_assoc (A B C : Type) : iso (A * (B * C)) ((A * B) * C) :=
{
  coel '(a, (b, c)) := ((a, b), c);
  coer '((a, b), c) := (a, (b, c));
}.
Proof.
  - now intros [a [b c]].
  - now intros [[a b] c].
Defined.

#[refine]
#[export]
Instance prod_comm {A B : Type} : iso (A * B) (B * A) :=
{
  coel '(a, b) := (b, a);
  coer '(b, a) := (a, b);
}.
Proof.
  - now intros [a b].
  - now intros [b a].
Defined.

(** ** Sumy *)

#[refine]
#[export]
Instance sum_empty_l (A : Type) : iso (Empty_set + A) A :=
{
  coel x := match x with | inl e => match e with end | inr a => a end;
  coer := inr;
}.
Proof.
  - now intros [[] | a].
  - easy.
Defined.

#[refine]
#[export]
Instance sum_empty_r (A : Type) : iso (A + Empty_set) A :=
{
  coel x := match x with | inl a => a | inr e => match e with end end;
  coer := inl;
}.
Proof.
  - now intros [a | []].
  - easy.
Defined.

#[refine]
#[export]
Instance sum_assoc (A B C : Type) : iso (A + (B + C)) ((A + B) + C) :=
{
  coel x :=
    match x with
    | inl a => inl (inl a)
    | inr (inl b) => inl (inr b)
    | inr (inr c) => inr c
    end;
  coer x :=
    match x with
    | inl (inl a) => inl a
    | inl (inr b) => inr (inl b)
    | inr c => inr (inr c)
    end;
}.
Proof.
  - now intros [a | [b | c]]; cbn.
  - now intros [[a | b] | c]; cbn.
Defined.

Definition sum_swap {A B : Type} (x : A + B) : B + A :=
match x with
| inl a => inr a
| inr b => inl b
end.

#[refine]
#[export]
Instance sum_comm (A B : Type) : iso (A + B) (B + A) :=
{
  coel := sum_swap;
  coer := sum_swap;
}.
Proof.
  - now intros [a | b]; cbn.
  - now intros [b | a]; cbn.
Defined.

(** ** Funkcje *)

Require Import FunctionalExtensionality.

#[refine, export]
Instance fun_empty_l (A : Type) : iso (Empty_set -> A) unit :=
{
  coel f := tt;
  coer _ e := match e with end;
}.
Proof.
  - intros f.
    extensionality e.
    now destruct e.
  - now intros [].
Defined.

#[refine, export]
Instance fun_unit_l (A : Type) : iso (unit -> A) A :=
{
  coel f := f tt;
  coer a := fun _ => a;
}.
Proof.
  - intros f.
    now extensionality u; destruct u.
  - easy.
Defined.

#[refine, export]
Instance fun_unit_r (A : Type) : iso (A -> unit) unit :=
{
  coel _ := tt;
  coer _ := fun _ => tt;
}.
Proof.
  - intros f.
    extensionality a.
    now destruct (f a).
  - now intros [].
Defined.

(** ** Rozdzielność *)

#[refine, export]
Instance prod_sum_l (A B C : Type) : iso ((A + B) * C) (A * C + B * C) :=
{
  coel '(ab, c) :=
    match ab with
    | inl a => inl (a, c)
    | inr b => inr (b, c)
    end;
  coer x :=
    match x with
    | inl (a, c) => (inl a, c)
    | inr (b, c) => (inr b, c)
    end;
}.
Proof.
  - now intros [[a | b] c].
  - now intros [[a c] | [b c]].
Defined.

#[refine, export]
Instance prod_sum_r (A B C : Type) : iso (A * (B + C)) (A * B + A * C) :=
{
  coel '(a, bc) :=
    match bc with
    | inl b => inl (a, b)
    | inr c => inr (a, c)
    end;
  coer x :=
    match x with
    | inl (a, b) => (a, inl b)
    | inr (a, c) => (a, inr c)
    end;
}.
Proof.
  - now intros [a [b | c]].
  - now intros [[a b] | [a c]].
Defined.

(** ** [bool] *)

#[refine, export]
Instance prod_bool_l (A : Type) : iso (bool * A) (A + A) :=
{
  coel '(b, a) := if b then inl a else inr a;
  coer x :=
    match x with
    | inl a => (true, a)
    | inr a => (false, a)
    end;
}.
Proof.
  - now intros [[] ?].
  - now intros [a | a].
Defined.

#[refine, export]
Instance prod_bool_r (A : Type) : iso (A * bool) (A + A) :=
{
  coel '(a, b) := if b then inl a else inr a;
  coer x :=
    match x with
    | inl a => (a, true)
    | inr a => (a, false)
    end;
}.
Proof.
  - now intros [? []].
  - now intros [a | a].
Defined.

#[refine, export]
Instance fun_bool_l (A : Type) : iso (bool -> A) (A * A) :=
{
  coel f := (f true, f false);
  coer '(a1, a2) := fun b => if b then a1 else a2;
}.
Proof.
  - intros f.
    extensionality b.
    now destruct b.
  - now intros [a1 a2].
Defined.

(** ** Adiunkcje *)

#[refine, export]
Instance fun_prod_r (A B C : Type) : iso (A -> B * C) ((A -> B) * (A -> C)) :=
{
  coel f := (fun a => fst (f a), fun a => snd (f a));
  coer '(f1, f2) := fun a => (f1 a, f2 a);
}.
Proof.
  - intros f.
    extensionality a.
    now destruct (f a).
  - now intros [f1 f2]; cbn.
Defined.

#[refine, export]
Instance fun_sum_l (A B C : Type) : iso (A + B -> C) ((A -> C) * (B -> C)) :=
{
  coel f := (fun a => f (inl a), fun b => f (inr b));
  coer '(f1, f2) := fun x =>
    match x with
    | inl a => f1 a
    | inr b => f2 b
    end;
}.
Proof.
  - intros f.
    extensionality x.
    now destruct x.
  - now intros [f1 f2].
Defined.

#[refine, export]
Instance fun_fun_r (A B C : Type) : iso (A -> (B -> C)) (A * B -> C) :=
{
  coel f := fun '(a, b) => f a b;
  coer f := fun a b => f (a, b);
}.
Proof.
  - easy.
  - intros f.
    extensionality x.
    now destruct x.
Defined.

(** ** Zachowywania izomorfizmów *)

#[refine]
#[export]
Instance iso_pres_prod
  {A1 A2 B1 B2 : Type} (i : iso A1 A2) (j : iso B1 B2) : iso (A1 * B1) (A2 * B2) :=
{
  coel '(a, b) := (coel i a, coel j b);
  coer '(a, b) := (coer i a, coer j b);
}.
Proof.
  - intros [a1 b1].
    now rewrite !coel_coer.
  - intros [a2 b2].
    now rewrite !coer_coel.
Defined.

#[refine, export]
Instance iso_pres_sum
  {A1 A2 B1 B2 : Type} (i : iso A1 A2) (j : iso B1 B2) : iso (A1 + B1) (A2 + B2) :=
{
  coel x :=
    match x with
    | inl a1 => inl (coel i a1)
    | inr b1 => inr (coel j b1)
    end;
  coer x :=
    match x with
    | inl a2 => inl (coer i a2)
    | inr b2 => inr (coer j b2)
    end;
}.
Proof.
  - now intros [a1 | b1]; rewrite !coel_coer.
  - now intros [a2 | b2]; rewrite !coer_coel.
Defined.

#[refine, export]
Instance iso_pres_fun
  {A1 A2 B1 B2 : Type} (i : iso A1 A2) (j : iso B1 B2) : iso (A1 -> B1) (A2 -> B2) :=
{
  coel f := fun a2 => coel j (f (coer i a2));
  coer f := fun a1 => coer j (f (coel i a1));
}.
Proof.
  - intros f.
    extensionality a1.
    now rewrite !coel_coer.
  - intros f.
    extensionality a1.
    now rewrite !coer_coel.
Defined.

Definition fmap_option {A B : Type} (f : A -> B) (x : option A) : option B :=
match x with
| None   => None
| Some a => Some (f a)
end.

#[refine, export]
Instance iso_pres_option
  (A1 A2 : Type) (i : iso A1 A2) : iso (option A1) (option A2) :=
{
  coel := fmap_option (coel i);
  coer := fmap_option (coer i);
}.
Proof.
  - intros [a |]; cbn; [| easy].
    now rewrite coel_coer.
  - intros [b |]; cbn; [| easy].
    now rewrite coer_coel.
Defined.

(** * Typy zależne *)

#[refine, export]
Instance iso_pi_fun
  {A B2 : Type} {B1 : A -> Type}
  (i : forall x : A, iso (B1 x) B2)
  : iso (forall x : A, B1 x) (A -> B2) :=
{
  coel f := fun a => coel (i a) (f a);
  coer f := fun a => coer (i a) (f a);
}.
Proof.
  - intros f.
    extensionality a.
    now rewrite coel_coer.
  - intros f.
    extensionality a.
    now rewrite coer_coel.
Defined.

#[refine, export]
Instance iso_sigT_prod
  {A B2 : Type} {B1 : A -> Type}
  (i : forall x : A, iso (B1 x) B2)
  : iso {x : A & B1 x} (A * B2) :=
{
  coel '(existT _ a b1) := (a, coel (i a) b1);
  coer '(a, b2) := existT _ a (coer (i a) b2);
}.
Proof.
  - intros [a b1].
    now rewrite coel_coer.
  - intros [a b2].
    now rewrite coer_coel.
Defined.

(** * Izomorfizmy charakterystyczne typów induktywnych (TODO) *)

(** ** [bool] *)

#[refine, export]
Instance bool_char : iso bool (unit + unit) :=
{
  coel b := if b then inl tt else inr tt;
  coer x := if x then true else false;
}.
Proof.
  - now intros [].
  - now intros [[] | []].
Defined.

(** ** Opcje *)

#[refine, export]
Instance option_char (A : Type) : iso (option A) (unit + A) :=
{
  coel oa :=
    match oa with
    | None => inl tt
    | Some a => inr a
    end;
  coer x :=
    match x with
    | inl _ => None
    | inr a => Some a
    end;
}.
Proof.
  - now intros [a |].
  - now intros [[] | a].
Defined.

(** ** Liczby naturalne *)

Definition pred (n : nat) : option nat :=
match n with
| 0 => None
| S n' => Some n'
end.

Definition unpred (on : option nat) : nat :=
match on with
| None => 0
| Some n => S n
end.

#[refine]
#[export]
Instance iso_nat_option_nat : iso nat (option nat) :=
{
  coel n := match n with | 0 => None | S n' => Some n' end;
  coer o := match o with | None => 0 | Some n => S n end;
}.
Proof.
  - now intros [].
  - now intros [].
Defined.

(** ** Listy *)

Definition uncons {A : Type} (l : list A) : option (A * list A) :=
match l with
| [] => None
| h :: t => Some (h, t)
end.

Definition ununcons {A : Type} (x : option (A * list A)) : list A :=
match x with
| None => []
| Some (h, t) => h :: t
end.

#[refine]
#[export]
Instance list_char (A : Type) : iso (list A) (option (A * list A)) :=
{
  coel l :=
    match l with
    | []     => None
    | h :: t => Some (h, t)
    end;
  coer o :=
    match o with
    | None        => []
    | Some (h, t) => h :: t
    end;
}.
Proof.
  - now intros [].
  - now intros [[] |].
Defined.

(** ** Strumienie *)

From Typonomikon Require Import F2.

(** Jak można się domyślić po przykładach, charakterystyczne izomorfizmy
    dla prostych typów induktywnych są łatwe. A co z innowacyjniejszymi
    rodzajami definicji induktywnych oraz z definicjami koinduktywnymi?
    Sprawdźmy to! *)

Axiom sim_eq :
  forall (A : Type) (x y : Stream A), sim x y -> x = y.

#[refine]
#[export]
Instance Stream_char (A : Type) : iso (Stream A) (A * Stream A) :=
{
  coel s := (hd s, tl s);
  coer '(a, s) := {| hd := a; tl := s |}
}.
Proof.
  - intro s.
    apply sim_eq.
    now constructor; cbn.
  - now intros [a s]; cbn.
Defined.

(** * Charakteryzacje "kontenerowe" (TODO) *)

(** ** [Stream unit ~ unit] *)

Require Import FinFun ZArith.

CoFixpoint theChosenOne : Stream unit :=
{|
  hd := tt;
  tl := theChosenOne;
|}.

Lemma all_chosen_unit_aux :
  forall s : Stream unit,
    sim s theChosenOne.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
  - now destruct (hd s).
  - now apply CH.
Qed.
(* end hide *)

Lemma all_chosen_unit :
  forall x y : Stream unit,
    sim x y.
(* begin hide *)
Proof.
  now intros; rewrite (all_chosen_unit_aux x), (all_chosen_unit_aux y).
Qed.
(* end hide *)

Lemma all_eq :
  forall x y : Stream unit,
    x = y.
(* begin hide *)
Proof.
  now intros; apply sim_eq, all_chosen_unit.
Qed.
(* end hide *)

Definition unit_to_stream (u : unit) : Stream unit := theChosenOne.
Definition stream_to_unit (s : Stream unit) : unit := tt.

Lemma unit_is_Stream_unit :
  Bijective unit_to_stream.
(* begin hide *)
Proof.
  exists stream_to_unit.
  split; intros.
  - now destruct x.
  - now apply all_eq.
Qed.
(* end hide *)

(** ** [Stream A ~ nat -> A] *)

Definition index {A : Type} (s : Stream A) : nat -> A :=
  fun n => F2.nth n s.

CoFixpoint memoize {A : Type} (f : nat -> A) : Stream A :=
{|
  hd := f 0;
  tl := memoize (fun n => f (S n));
|}.

Lemma index_memoize :
  forall {A : Type} (f : nat -> A) (n : nat),
    index (memoize f) n = f n.
Proof.
  intros A f n; revert f.
  induction n as [| n']; cbn; intros; [easy |].
  change (F2.nth n' _) with (index (memoize (fun n => f (S n))) n').
  now rewrite IHn'.
Qed.

Lemma memoize_index :
  forall {A : Type} (s : Stream A),
    sim (memoize (index s)) s.
Proof.
  cofix CH.
  constructor; cbn; [easy |].
  now apply CH.
Qed.

(** * Charakteryzacje "wektorowe" (TODO) *)

(** ** [list A ~ {n : nat & vec A n}] *)

Set Warnings "-notation-overridden".
From Typonomikon Require Import E1.
Set Warnings "notation-overridden".

Definition vlist (A : Type) : Type :=
  {n : nat & vec A n}.

Fixpoint vectorize' {A : Type} (l : list A) : vec A (length l) :=
match l with
| nil => vnil
| cons h t => vcons h (vectorize' t)
end.

Definition vectorize {A : Type} (l : list A) : vlist A :=
  existT _ (length l) (vectorize' l).

Fixpoint toList {A : Type} {n : nat} (v : vec A n) : list A :=
match v with
| vnil => nil
| vcons h t => cons h (toList t)
end.

Definition listize {A : Type} (v : vlist A) : list A :=
  toList (projT2 v).

Lemma eq_head_tail :
  forall {A : Type} {n : nat} (v1 v2 : vec A (S n)),
    head v1 = head v2 -> tail v1 = tail v2 -> v1 = v2.
Proof.
  intros A n v1 v2.
  dependent destruction v1; dependent destruction v2; cbn.
  now intros -> ->.
Qed.

From Typonomikon Require Import F0a.

Lemma transport_cons :
  forall {A : Type} {n m : nat} (h : A) (t : vec A n) (p : n = m),
    transport (fun n : nat => vec A (S n)) p
     (h :: t) = h :: transport (fun n : nat => vec A n) p t.
Proof.
  now destruct p; cbn.
Qed.

#[refine]
#[export]
Instance iso_list_vlist (A : Type) : iso (list A) (vlist A) :=
{
  coel := vectorize;
  coer := listize;
}.
Proof.
  - induction a as [| h t]; cbn in *; [easy |].
    now rewrite IHt.
  - intros [n v].
    unfold vectorize; cbn.
    induction v as [| h t]; cbn; [easy |].
    apply sigT_eq' in IHv; cbn in IHv.
    destruct IHv as [p e].
    unshelve eapply sigT_eq.
    + exact (ap S p).
    + now rewrite transport_ap, transport_cons, e.
Defined.

(** * Ciekawsze izomorfizmy *)

(** ** [nat ~ nat + nat] *)

(** Jak trudno jest zrobić ciekawsze izomorfizmy? *)

Function div2 (n : nat) : nat + nat :=
match n with
| 0 => inl 0
| 1 => inr 0
| S (S n') =>
  match div2 n' with
  | inl m => inl (S m)
  | inr m => inr (S m)
  end
end.

Definition undiv2 (x : nat + nat) : nat :=
match x with
| inl n => 2 * n
| inr n => S (2 * n)
end.

#[refine]
#[export]
Instance iso_nat_sum_nat_nat : iso nat (nat + nat) :=
{
  coel := div2;
  coer := undiv2;
}.
Proof.
  - intros a.
    functional induction (div2 a); cbn; [easy.. | |].
    + rewrite e0 in IHs; cbn in IHs.
      now rewrite <- plus_n_Sm, IHs.
    + rewrite e0 in IHs; cbn in IHs.
      now rewrite <- plus_n_Sm, IHs.
  - destruct b as [n | n].
    + cbn.
      functional induction (div2 n); cbn; [easy.. | |].
      * now rewrite <- 2!plus_n_Sm; cbn; rewrite IHs.
      * now rewrite <- 2!plus_n_Sm; cbn; rewrite IHs.
    + induction n as [| n']; cbn in *; [easy |].
      destruct n' as [| n'']; cbn in *; [easy |].
      now rewrite <- plus_n_Sm, IHn'.
Defined.

(** Niezbyt trudno, ale łatwo też nie. *)

(** ** [nat ~ nat * nat] *)

(** *** [goto] *)

Function goto' (x y n : nat) : nat * nat :=
match n, x with
| 0   , _    => (x, y)
| S n', 0    => goto' (S y) 0 n'
| S n', S x' => goto' x' (S y) n'
end.

Definition goto (n : nat) : nat * nat :=
  goto' 0 0 n.

Lemma goto'_add :
  forall x y n m x' y': nat,
    goto' x y n = (x', y') ->
      goto' x y (n + m) = goto' x' y' m.
Proof.
  intros x y n.
  functional induction goto' x y n; cbn; intros.
  - now inv H.
  - now apply IHp.
  - now apply IHp.
Qed.

Lemma goto'_small :
  forall x y n : nat,
    n <= x ->
      goto' x y n = (x - n, y + n).
Proof.
  intros x y n Hle.
  functional induction goto' x y n; cbn; [now f_equal; lia | now lia |].
  now rewrite IHp; [f_equal |]; lia.
Qed.

Lemma goto'_right :
  forall x y : nat,
    goto' x y (1 + x + y) = (S x, y).
Proof.
  intros.
  replace (1 + x + y) with (x + (1 + y)) by lia.
  erewrite goto'_add; cycle 1.
  - now apply goto'_small.
  - rewrite Nat.sub_diag; cbn.
    now rewrite goto'_small; [f_equal |]; lia.
Qed.

Lemma goto_add :
  forall n m : nat,
    goto (n + m) = goto' (fst (goto n)) (snd (goto n)) m.
Proof.
  unfold goto.
  intros n m.
  erewrite goto'_add; [easy |].
  now destruct (goto' 0 0 n).
Qed.

(** *** [comefrom] *)

(** Chcielibyśmy zdefiniować funkcję odwrotną do [goto'] w ten sposób:

    [comefrom (0, 0) = 0]

    [comefrom (S x, 0) = 1 + comefrom (0, x)]

    [comefrom (x, S y) = 1 + comefrom (S x, y)]

    Niestety takie równania nie są strukturalnie rekurencyjne, więc definicja
    nie jest akceptowana przez Coqa. Próba ratowania sytuacji za pomocą rekursji
    dobrze ufundowanej też by się nie powiodła (wiem bo próbowałem).

    Zamiast tego, użyjemy nieco przerobionej definicji, a potem spróbujemy pokazać,
    że spełnia ona powyższe równania. *)

Fixpoint comefrom' (x y : nat) {struct x} : nat :=
match x with
| 0 =>
  (fix aux (y : nat) : nat :=
    match y with
    | 0    => 0
    | S y' => 1 + y + aux y'
    end) y
| S x' => x + y + comefrom' x' y
end.

Definition comefrom (xy : nat * nat) : nat :=
  comefrom' (fst xy) (snd xy).

Lemma comefrom'_eq_1 :
  comefrom' 0 0 = 0.
Proof.
  easy.
Qed.

Lemma comefrom'_eq_2 :
  forall x : nat,
    comefrom' (S x) 0 = 1 + comefrom' 0 x.
Proof.
  now induction x as [| x']; cbn in *; lia.
Qed.

Lemma comefrom'_eq_3 :
  forall x y : nat,
    comefrom' x (S y) = 1 + comefrom' (S x) y.
Proof.
  induction x as [| x'].
  - intros []; cbn; lia.
  - intros y.
    specialize (IHx' y); cbn in *.
    now lia.
Qed.

Lemma comefrom'_right :
  forall x y : nat,
    comefrom' (S x) y = 1 + x + y + comefrom' x y.
Proof.
  induction x as [| x']; cbn; intros; [now lia |].
  specialize (IHx' y).
  now lia.
Qed.

Lemma comefrom'_up :
  forall x y : nat,
    comefrom' x (S y) = 2 + x + y + comefrom' x y.
Proof.
  induction x as [| x']; cbn; intros; [now lia |].
  specialize (IHx' y).
  now lia.
Qed.

Lemma comefrom'_goto' :
  forall x y n x' y' : nat,
    goto' x y n = (x', y') ->
      comefrom' x' y' = comefrom' x y + n.
Proof.
  intros x y n.
  functional induction goto' x y n; intros.
  - now inv H; lia.
  - now rewrite (IHp _ _ H), comefrom'_eq_2; lia.
  - now rewrite (IHp _ _ H), comefrom'_eq_3; lia.
Qed.

Lemma comefrom_goto :
  forall n : nat,
    comefrom (goto n) = n.
Proof.
  intros.
  destruct (goto n) as [x y] eqn: Heq.
  unfold comefrom; cbn.
  rewrite (comefrom'_goto' 0 0 n x y); cbn; [easy |].
  exact Heq.
Qed.

Lemma goto_comefrom :
  forall xy : nat * nat,
    goto (comefrom xy) = xy.
Proof.
  intros [x y].
  unfold comefrom, fst, snd.
  revert y.
  induction x as [| x'].
  - induction y as [| y']; [easy |].
    rewrite comefrom'_up, Nat.add_comm, goto_add, IHy'; cbn.
    rewrite goto'_small; [| easy].
    now f_equal; lia.
  - intros y.
    rewrite comefrom'_right, Nat.add_comm, goto_add, IHx'.
    unfold fst, snd.
    now apply goto'_right.
Qed.

#[refine]
#[export]
Instance iso_nat_prod_nat_nat : iso nat (nat * nat) :=
{
  coel := goto;
  coer := comefrom;
}.
Proof.
  - now apply comefrom_goto.
  - now apply goto_comefrom.
Defined.

(** ** [nat ~ nat * nat], alternatywnie (TODO) *)

Definition komenvan (x : nat) (y : nat) : nat :=
  let n := x + y in Nat.div2 (S n * n) + y.

(* ŹLE!
Function comefrom_v2 (xy : nat * nat) {measure (fun '(x, y) => x + y) xy} : nat :=
match xy with
| (0, 0) => 0
| (x, y) => x + y + comefrom_v2 (x - 1, y - 1)
end.
Proof.
  - now intros [] x y -> y' -> [= -> ->]; cbn; lia.
  - now intros [x' y'] x y n -> [= -> ->]; cbn; lia.
Defined.

Compute comefrom (0, 1).
Compute comefrom_v2 (0, 1).
Compute komenvan 3 5.
*)

(** ** [nat ~ list nat] *)

(** Jak trudno jest z podstawowych izomorfizmów dla produktów i sum
    uskładać coś w stylu [nat ~ list nat]? A może nie da się i trzeba
    robić ręcznie? *)

Fixpoint nat_vec {n : nat} (arg : nat) : vec nat (S n) :=
match n with
| 0 => arg :: vnil
| S n' =>
  let
    (arg1, arg2) := goto arg
  in
    arg1 :: nat_vec arg2
end.

Fixpoint vec_nat {n : nat} (v : vec nat n) {struct v} : option nat :=
match v with
| vnil => None
| vcons h t =>
  match vec_nat t with
  | None => Some h
  | Some r => Some (comefrom (h, r))
  end
end.

#[refine]
#[export]
Instance vec_S (A : Type) (n : nat) : iso (vec A (S n)) (A * vec A n) :=
{
  coel v := (head v, tail v);
  coer '(h, t) := vcons h t;
}.
Proof.
  - intros.
    now refine (match a with vcons _ _ => _ end); cbn.
  - now intros [a v]; cbn.
Defined.

#[export]
Instance iso_nat_vlist_S :
  forall n : nat,
    iso nat (vec nat (S n)).
Proof.
  induction n as [| n'].
  - split with (coel := fun n => vcons n vnil) (coer := head); [easy |].
    intros b.
    refine (match b with vcons _ _ => _ end).
    destruct n; cbn; f_equal; [| easy].
    now refine (match v with vnil => _ end).
  - eapply iso_trans.
    + now apply iso_nat_prod_nat_nat.
    + eapply iso_trans; cycle 1.
      * now apply iso_sym, vec_S.
      * apply iso_pres_prod; [| easy].
        now apply iso_refl.
Defined.

#[export]
Instance iso_vlist_option :
  forall A : Type,
    iso (vlist A) (option {n : nat & vec A (S n)}).
Proof.
  unshelve esplit.
  - intros [[| n] v].
    + exact None.
    + exact (Some (existT _ n v)).
  - intros [[n v] |].
    + exact (existT _ (S n) v).
    + exact (existT _ 0 vnil).
  - now intros [? []].
  - now intros [[] |].
Defined.

#[export]
Instance iso_nat_list_nat :
  iso nat (list nat).
Proof.
  eapply iso_trans; [| now apply iso_sym, iso_list_vlist].
  unfold vlist.
  eapply iso_trans; [now apply iso_nat_option_nat |].
  eapply iso_trans; [| now apply iso_sym, iso_vlist_option].
  apply iso_pres_option.
  eapply iso_trans; [now apply iso_nat_prod_nat_nat |].
  apply iso_sym, iso_sigT_prod.
  intros.
  now apply iso_sym, iso_nat_vlist_S.
Defined.

(* Compute D5a.map (coel iso_nat_list_nat) (D5a.iterate S 100 0). *)

(** ... ale [nat ~ list nat] jest dość trudne. *)