(** * H2z: Izomorfizmy typów [TODO] *)

Require Import Equality.

From Typonomikon Require Import H2.

(* begin hide *)

(** TODO: Izomorfizmy dla typów induktywnych (patrz notatka poniżej).

    Każde drzewo jest drzewem o jakiejś wysokości (no chyba że ma
    nieskończone rozgałęzienie, to wtedy nie). Uogólniając: każdy
    element typu induktywnego jest elementem odpowiadającego mu
    typu indeksowanego o pewnym indeksie. UWAGA: rozróżnienie na
    drzewa o skończonej wysokości vs drzewa o ograniczonej wysokości. *)

(* end hide *)

Class iso (A B : Type) : Type :=
{
  coel : A -> B;
  coer : B -> A;
  coel_coer :
    forall a : A, coer (coel a) = a;
  coer_coel :
    forall b : B, coel (coer b) = b;
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
  intros. rewrite 2!coel_coer. reflexivity.
  intros. rewrite 2!coer_coel. reflexivity.
Defined.

#[refine]
#[export]
Instance iso_pres_prod
  {A A' B B' : Type} (i : iso A A') (j : iso B B') : iso (A * B) (A' * B') :=
{
  coel '(a, b) := (coel i a, coel j b);
  coer '(a, b) := (coer i a, coer j b);
}.
Proof.
  destruct a. rewrite !coel_coer. reflexivity.
  destruct b. rewrite !coer_coel. reflexivity.
Defined.

(** * Produkty i sumy *)

#[refine]
#[export]
Instance prod_assoc (A B C : Type) : iso (A * (B * C)) ((A * B) * C) :=
{
  coel '(a, (b, c)) := ((a, b), c);
  coer '((a, b), c) := (a, (b, c));
}.
Proof.
  intros [a [b c]]. reflexivity.
  intros [[a b] c]. reflexivity.
Defined.

#[refine]
#[export]
Instance prod_unit_l (A : Type) : iso (unit * A) A :=
{
  coel '(_, a) := a;
  coer a := (tt, a);
}.
Proof.
  intros [[]]. reflexivity.
  reflexivity.
Defined.

#[refine]
#[export]
Instance prod_unit_r (A : Type) : iso (A * unit) A :=
{
  coel '(a, _) := a;
  coer a := (a, tt);
}.
Proof.
  intros [a []]. reflexivity.
  reflexivity.
Defined.

#[refine]
#[export]
Instance prod_comm {A B : Type} : iso (A * B) (B * A) :=
{
  coel '(a, b) := (b, a);
  coer '(b, a) := (a, b);
}.
Proof.
  destruct a. cbn. reflexivity.
  destruct b. cbn. reflexivity.
Defined.

(** Trzeba przerobić rozdział o typach i funkcjach tak, żeby nie mieszać
    pojęć kategorycznych (wprowadzonych na początku) z teoriozbiorowymi
    (injekcja, surjekcja, bijekcja). Przedstawić te 3 ostatnie jako
    explicite charakteryzacje pojęć kategorycznych. *)

#[refine]
#[export]
Instance sum_empty_l (A : Type) : iso (Empty_set + A) A :=
{
  coel x := match x with | inl e => match e with end | inr a => a end;
  coer := inr;
}.
Proof.
  destruct a as [[] | a]. reflexivity.
  reflexivity.
Defined.

#[refine]
#[export]
Instance sum_empty_r (A : Type) : iso (A + Empty_set) A :=
{
  coel x := match x with | inl a => a | inr e => match e with end end;
  coer := inl;
}.
Proof.
  destruct a as [a | []]. reflexivity.
  reflexivity.
Defined.

#[refine]
#[export]
Instance sum_assoc (A B C : Type) : iso (A + (B + C)) ((A + B) + C) :=
{

}.
Proof.
  1-2: firstorder.
    intros [a | [b | c]]; cbn; reflexivity.
    intros [[a | b] | c]; cbn; reflexivity.
Defined.

#[refine]
#[export]
Instance sum_comm (A B : Type) : iso (A + B) (B + A) :=
{

}.
Proof.
  1-2: firstorder.
    destruct a as [a | b]; cbn; reflexivity.
    destruct b as [b | a]; cbn; reflexivity.
Defined.

(** * Liczby naturalne *)

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
  destruct a; reflexivity.
  destruct b; reflexivity.
Defined.

(** * Listy *)

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
  destruct a; reflexivity.
  destruct b as [[h t] |]; reflexivity.
Defined.

(** * Strumienie *)

From Typonomikon Require Import F2.

(** Jak można się domyślić po przykładach, charakterystyczne izomorfizmy
    dla prostych typów induktywnych są łatwe. A co z innowacyjniejszymi
    rodzajami definicji induktywnych oraz z definicjami koinduktywnymi?
    Sprawdźmy to! *)

#[refine]
#[export]
Instance Stream_char (A : Type) : iso (Stream A) (A * Stream A) :=
{
  coel s := (hd s, tl s);
  coer '(a, s) := {| hd := a; tl := s |}
}.
Proof.
Admitted.
(*
  destruct a. cbn. reflexivity.
  destruct b. cbn. reflexivity.
Defined.
*)

(** * Ciekawsze izomorfizmy *)

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
  intro. functional induction (div2 a); cbn.
    1-2: reflexivity.
    rewrite e0 in IHs. cbn in IHs. rewrite <- plus_n_Sm, IHs. reflexivity.
    rewrite e0 in IHs. cbn in IHs. rewrite <- plus_n_Sm, IHs. reflexivity.
  destruct b.
    cbn. functional induction (div2 n); cbn.
      1-2: reflexivity.
      rewrite <- 2!plus_n_Sm. cbn. rewrite IHs. reflexivity.
      rewrite <- 2!plus_n_Sm. cbn. rewrite IHs. reflexivity.
    induction n as [| n'].
      cbn. reflexivity.
      cbn in *. destruct n' as [| n'']; cbn in *.
        reflexivity.
        rewrite <- plus_n_Sm. rewrite IHn'. reflexivity.
Defined.

(** Niezbyt trudno, ale łatwo też nie. *)

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
  functional induction goto' x y n;
  cbn; intros.
    inv H. reflexivity.
    apply IHp. assumption.
    apply IHp. assumption.
Qed.

Lemma goto'_small :
  forall x y n : nat,
    n <= x ->
      goto' x y n = (x - n, y + n).
Proof.
  intros.
  functional induction goto' x y n.
    f_equal; lia.
    lia.
    cbn. replace (y + S n') with (S y + n').
      apply IHp. lia.
      lia.
Qed.

Lemma goto'_right :
  forall x y : nat,
    goto' x y (1 + x + y) = (S x, y).
Proof.
  intros.
  replace (1 + x + y) with (x + (1 + y)) by lia.
  erewrite goto'_add.
    2: { apply goto'_small. lia. }
    rewrite Nat.sub_diag. cbn. rewrite goto'_small.
      f_equal; lia.
      lia.
Qed.

Lemma goto_add :
  forall n m : nat,
    goto (n + m) = goto' (fst (goto n)) (snd (goto n)) m.
Proof.
  intros. unfold goto.
  erewrite goto'_add.
    reflexivity.
    destruct (goto' 0 0 n); reflexivity.
Qed.

(** Chcielibyśmy zdefiniować funkcję odwrotną do [goto'] w ten sposób:
    comefrom (0  , 0) = 0
    comefrom (S x, 0) = 1 + comefrom (0  , x)
    comefrom (x, S y) = 1 + comefrom (S x, y)

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
  reflexivity.
Qed.

Lemma comefrom'_eq_2 :
  forall x : nat,
    comefrom' (S x) 0 = 1 + comefrom' 0 x.
Proof.
  induction x as [| x']; cbn in *; lia.
Qed.

Lemma comefrom'_eq_3 :
  forall x y : nat,
    comefrom' x (S y) = 1 + comefrom' (S x) y.
Proof.
  induction x as [| x'].
    destruct y; cbn; lia.
    intros y. specialize (IHx' y). cbn in *. lia.
Qed.

Lemma comefrom'_right :
  forall x y : nat,
    comefrom' (S x) y = 1 + x + y + comefrom' x y.
Proof.
  induction x as [| x']; intros.
    cbn. lia.
    specialize (IHx' y). cbn. lia.
Qed.

Lemma comefrom'_up :
  forall x y : nat,
    comefrom' x (S y) = 2 + x + y + comefrom' x y.
Proof.
  induction x as [| x']; intros.
    cbn. lia.
    specialize (IHx' y). cbn. lia.
Qed.

Lemma comefrom'_goto' :
  forall x y n x' y' : nat,
    goto' x y n = (x', y') ->
      comefrom' x' y' = comefrom' x y + n.
Proof.
  intros x y n.
  functional induction goto' x y n;
  intros.
    inv H. lia.
    rewrite (IHp _ _ H). rewrite comefrom'_eq_2. lia.
    rewrite (IHp _ _ H). rewrite comefrom'_eq_3. lia.
Qed.

Lemma comefrom_goto :
  forall n : nat,
    comefrom (goto n) = n.
Proof.
  intros.
  destruct (goto n) as [x y] eqn: Heq.
  unfold comefrom. cbn.
  rewrite (comefrom'_goto' 0 0 n x y).
    cbn. reflexivity.
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
    induction y as [| y'].
      cbn. reflexivity.
      rewrite comefrom'_up, Nat.add_comm, goto_add, IHy'. cbn. rewrite goto'_small.
        f_equal; lia.
        reflexivity.
    intros. rewrite comefrom'_right, Nat.add_comm, goto_add, IHx'.
      unfold fst, snd. apply goto'_right.
Qed.

#[refine]
#[export]
Instance iso_nat_prod_nat_nat : iso nat (nat * nat) :=
{
  coel := goto;
  coer := comefrom;
}.
Proof.
  apply comefrom_goto.
  apply goto_comefrom.
Defined.

(** Jak trudno jest z podstawowych izomorfizmów dla produktów i sum
    uskładać coś w stylu nat ~ list nat? A może nie da się i trzeba
    robić ręcznie? *)

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
  dependent destruction v1.
  dependent destruction v2.
  cbn. destruct 1, 1. reflexivity.
Qed.

From Typonomikon Require Import H1.

Lemma transport_cons :
  forall {A : Type} {n m : nat} (h : A) (t : vec A n) (p : n = m),
    transport (fun n : nat => vec A (S n)) p
     (h :: t) = h :: transport (fun n : nat => vec A n) p t.
Proof.
  destruct p. cbn. reflexivity.
Qed.

#[refine]
#[export]
Instance iso_list_vlist (A : Type) : iso (list A) (vlist A) :=
{
  coel := vectorize;
  coer := listize;
}.
Proof.
  induction a as [| h t]; cbn in *.
    reflexivity.
    rewrite IHt. reflexivity.
  destruct b as [n v]. unfold vectorize. cbn.
    induction v as [| h t]; cbn.
      reflexivity.
      apply sigT_eq' in IHv. cbn in IHv. destruct IHv.
        eapply sigT_eq. Unshelve. all: cycle 1.
          exact (ap S x).
          rewrite transport_ap, transport_cons, e. reflexivity.
Defined.

(** Wnioski: da się zrobić trochę... *)

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
  intro. refine (match a with vcons _ _ => _ end). cbn. reflexivity.
  destruct b. cbn. reflexivity.
Defined.

#[export]
Instance iso_nat_vlist_S :
  forall n : nat,
    iso nat (vec nat (S n)).
Proof.
  induction n as [| n'].
    split with
            (coel := fun n => vcons n vnil)
            (coer := head).
      cbn. reflexivity.
      intro.
        refine (match b with vcons _ _ => _ end).
        destruct n; cbn; f_equal.
          refine (match v with vnil => _ end). reflexivity.
          red. trivial.
    eapply iso_trans.
      apply iso_nat_prod_nat_nat.
      eapply iso_trans.
        2: { apply iso_sym, vec_S. }
        apply iso_pres_prod.
          apply iso_refl.
          assumption.
Defined.

#[export]
Instance iso_vlist_option :
  forall A : Type,
    iso (vlist A) (option {n : nat & vec A (S n)}).
Proof.
  intros.
  esplit. Unshelve. all: cycle 2.
    intros [[]].
      exact None.
      apply Some. exists n. exact v.
    intros [[n v] |].
      exists (S n). exact v.
      exists 0. exact vnil.
    destruct a, v; reflexivity.
    destruct b.
      destruct s. reflexivity.
      reflexivity.
Defined.

Definition fmap_option {A B : Type} (f : A -> B) (x : option A) : option B :=
match x with
| None   => None
| Some a => Some (f a)
end.

#[refine]
#[export]
Instance iso_pres_option
  (A B : Type) (i : iso A B) : iso (option A) (option B) :=
{
  coel := fmap_option (coel i);
  coer := fmap_option (coer i);
}.
Proof.
  destruct a; f_equal; cbn; f_equal. apply coel_coer.
  destruct b; f_equal; cbn; f_equal. apply coer_coel.
Defined.

#[export]
Instance iso_prod_sigT :
  forall (A B : Type) (B' : A -> Type),
    (forall x : A, iso B (B' x)) -> iso (A * B) {x : A & B' x}.
Proof.
  intros A B B' H.
  esplit. Unshelve. all: cycle 2.
    intros [a b]. exists a. destruct (H a) as [f g H1 H2]. apply f. exact b.
    intros [a b']. split.
      exact a.
      destruct (H a) as [f g H1 H2]. apply g. exact b'.
    destruct a, (H a); cbn. f_equal. apply coel_coer0.
    intros [a b']. cbn. destruct (H a). f_equal. apply coer_coel0.
Defined.

#[export]
Instance iso_nat_list_nat :
  iso nat (list nat).
Proof.
  eapply iso_trans.
    2: { apply iso_sym. apply iso_list_vlist. }
  unfold vlist.
  eapply iso_trans.
    apply iso_nat_option_nat.
  eapply iso_trans.
    2: { apply iso_sym. apply iso_vlist_option. }
  apply iso_pres_option.
  eapply iso_trans.
    apply iso_nat_prod_nat_nat.
  apply iso_prod_sigT.
  apply iso_nat_vlist_S.
Defined.

(* Compute D5.map (coel iso_nat_list_nat) (D5.iterate S 100 0). *)

(** ... ale [nat ~ list nat] jest dość trudne. *)