(** * X9: Kolisty *)

Require Import book.X3.

CoInductive coList (A : Type) : Type :=
{
    uncons : option (A * coList A);
}.

Arguments uncons {A}.

(** Zdefiniuj [conil], czyli kolistę pustą, oraz [cocons], czyli funkcję,
    która dokleja do kolisty nową głowę. *)

(* begin hide *)
Definition conil {A : Type} : coList A :=
{|
    uncons := None;
|}.

Definition cocons {A : Type} (h : A) (t : coList A) : coList A :=
{|
    uncons := Some (h, t);
|}.
(* end hide *)

(** Zdefiniuj relację bipodobieństwa dla kolist. Udowodnij, że jest ona
    relacją równoważności. *)

(* begin hide *)
CoInductive lsim {A : Type} (l1 l2 : coList A) : Prop :=
{
    lsim' :
      uncons l1 = None /\ uncons l2 = None \/
      exists (h1 : A) (t1 : coList A) (h2 : A) (t2 : coList A),
        uncons l1 = Some (h1, t1) /\
        uncons l2 = Some (h2, t2) /\
          h1 = h2 /\ lsim t1 t2
}.

Hint Constructors lsim.

Axiom eq_lsim :
  forall (A : Type) (l1 l2 : coList A), lsim l1 l2 -> l1 = l2.

Lemma eq_uncons :
  forall (A : Type) (l1 l2 : coList A),
    uncons l1 = uncons l2 -> l1 = l2.
Proof.
  destruct l1, l2. cbn. intro. rewrite H. reflexivity.
Qed.

(* end hide *)

Lemma lsim_refl :
  forall (A : Type) (l : coList A), lsim l l.
(* begin hide *)
Proof.
  cofix CH.
  destruct l as [[[h t]|]].
    constructor. right. exists h, t, h, t; auto.
    constructor. left. cbn. split; reflexivity.
Qed.
(* end hide *)

Lemma lsim_symm :
  forall (A : Type) (l1 l2 : coList A),
    lsim l1 l2 -> lsim l2 l1.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [[[] | (h1 & t1 & h2 & t2 & p1 & p2 & p3 & H)]].
    constructor. left. split; assumption.
    constructor. right. exists h2, t2, h1, t1. auto.
Qed.
(* end hide *)

Lemma lsim_trans :
  forall (A : Type) (l1 l2 l3 : coList A),
    lsim l1 l2 -> lsim l2 l3 -> lsim l1 l3.
(* begin hide *)
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
(* end hide *)

Require Import X7.

CoFixpoint len {A : Type} (l : coList A) : conat :=
{|
    pred :=
      match uncons l with
          | None => None
          | Some (_, t) => Some (len t)
      end;
|}.

(** Zdefiniuj funkcję [snoc], która dostawia element na koniec kolisty. *)

(* begin hide *)
CoFixpoint snoc {A : Type} (l : coList A) (x : A) : coList A :=
{|
    uncons :=
      match uncons l with
          | None => Some (x, conil)
          | Some (h, t) => Some (h, snoc t x)
      end;
|}.
(* end hide *)

Lemma len_cocons :
  forall (A : Type) (x : A) (l : coList A),
    len (cocons x l) = succ (len l).
(* begin hide *)
Proof.
  intros. apply eq_pred. cbn. reflexivity.
Qed.
(* end hide *)

Lemma len_snoc :
  forall (A : Type) (l : coList A) (x : A),
    sim (len (snoc l x)) (succ (len l)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. right. destruct l as [[[h t] |]]; cbn.
    exists (len (snoc t x)), (succ (len t)). intuition.
      f_equal. apply eq_pred. cbn. reflexivity.
    do 2 eexists. intuition. reflexivity.
Qed.
(* end hide *)

CoFixpoint app {A : Type} (l1 l2 : coList A) : coList A :=
{|
    uncons :=
      match uncons l1 with
          | None => uncons l2
          | Some (h, t) => Some (h, app t l2)
      end
|}.

Lemma app_conil_l :
  forall (A : Type) (l : coList A),
    app conil l = l.
(* begin hide *)
Proof.
  intros. apply eq_uncons. cbn. reflexivity.
Qed.
(* end hide *)

Lemma app_conil_r :
  forall (A : Type) (l : coList A),
    lsim (app l conil) l.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l as [[[h t] |]]; cbn.
    right. do 4 eexists. intuition.
    left. split; reflexivity.
Qed.
(* end hide *)

Lemma app_assoc :
  forall (A : Type) (l1 l2 l3 : coList A),
    lsim (app (app l1 l2) l3) (app l1 (app l2 l3)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l1 as [[[h1 t1] |]]; cbn.
    right. do 4 eexists. intuition.
    destruct l2 as [[[h2 t2] |]]; cbn.
      right. do 4 eexists. intuition. apply lsim_refl.
      destruct l3 as [[[h3 t3] |]]; cbn.
        right. do 4 eexists. intuition. apply lsim_refl.
        left. split; reflexivity.
Qed.
(* end hide *)

Lemma len_app :
  forall (A : Type) (l1 l2 : coList A),
    sim (len (app l1 l2)) (add (len l1) (len l2)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l1 as [[[h1 t1] |]]; cbn.
    right. do 2 eexists. intuition.
    destruct l2 as [[[h2 t2] |]]; cbn.
      right. do 2 eexists. intuition.
      left. split; reflexivity.
Qed.
(* end hide *)

Lemma snoc_app :
  forall (A : Type) (l1 l2 : coList A) (x : A),
    lsim (snoc (app l1 l2) x) (app l1 (snoc l2 x)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l1 as [[[h1 t1] |]]; cbn.
    right. do 4 eexists. intuition.
    destruct l2 as [[[h2 t2] |]]; cbn.
      right. do 4 eexists. intuition. apply lsim_refl.
      right. do 4 eexists. intuition.
Qed.
(* end hide *)

Lemma app_snoc_l :
  forall (A : Type) (l1 l2 : coList A) (x : A),
    lsim (app (snoc l1 x) l2) (app l1 (cocons x l2)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l1 as [[[h1 t1] |]]; cbn.
    right. do 4 eexists. intuition.
    right. do 4 eexists. intuition. rewrite app_conil_l. apply lsim_refl.
Qed.
(* end hide *)

(* begin hide *)
CoFixpoint lmap {A B : Type} (f : A -> B) (l : coList A) : coList B :=
{|
    uncons :=
    match uncons l with
        | None => None
        | Some (h, t) => Some (f h, lmap f t)
    end
|}.
(* end hide *)

Lemma lmap_id :
  forall (A : Type) (l : coList A),
    lsim (lmap id l) l.
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l as [[[h t] |]]; cbn.
    right. do 4 eexists. intuition.
    left. split; reflexivity.
Qed.
(* end hide *)

Lemma lmap_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : coList A),
    lsim (lmap g (lmap f l)) (lmap (fun x => g (f x)) l).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l as [[[h t]|]]; [right | left]; cbn.
    exists (g (f h)), (lmap g (lmap f t)),
           (g (f h)), (lmap (fun x => g (f x)) t).
      repeat (split; [reflexivity | idtac]). apply CH.
    do 2 split.
Qed.
(* end hide *)

Lemma lmap_conil :
  forall (A B : Type) (f : A -> B),
    lmap f conil = conil.
(* begin hide *)
Proof.
  intros. apply eq_uncons. cbn. reflexivity.
Qed.
(* end hide *)

Lemma lmap_cocons :
  forall (A B : Type) (f : A -> B) (x : A) (l : coList A),
    lsim (lmap f (cocons x l)) (cocons (f x) (lmap f l)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. right. exists (f x), (lmap f l), (f x), (lmap f l).
    cbn. intuition. apply lsim_refl.
Qed.
(* end hide *)

Lemma len_lmap :
  forall (A B : Type) (f : A -> B) (l : coList A),
    sim (len (lmap f l)) (len l).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l as [[[h t] |]]; cbn.
    right. exists (len (lmap f t)), (len t). intuition.
    left. split; reflexivity.
Qed.
(* end hide *)

Lemma lmap_snoc :
  forall (A B : Type) (f : A -> B) (l : coList A) (x : A),
    lsim (lmap f (snoc l x)) (snoc (lmap f l) (f x)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l as [[[h t] |]]; cbn.
    right. do 4 eexists. eauto.
    right. exists (f x), (lmap f conil), (f x), conil. intuition.
Qed.
(* end hide *)

Lemma lmap_app :
  forall (A B : Type) (f : A -> B) (l1 l2 : coList A),
    lsim (lmap f (app l1 l2)) (app (lmap f l1) (lmap f l2)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l1 as [[[h1 t1] |]]; cbn.
    right. do 4 eexists. eauto.
    destruct l2 as [[[h2 t2] |]]; cbn.
      right. exists (f h2), (lmap f t2), (f h2), (lmap f t2). intuition.
        apply lsim_refl.
      left. split; reflexivity.
Qed.
(* end hide *)

Lemma lmap_ext :
  forall (A B : Type) (f g : A -> B) (l : coList A),
    (forall x : A, f x = g x) -> lsim (lmap f l) (lmap g l).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l as [[[h t] |]]; cbn.
    right. do 4 eexists. intuition.
    left. split; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
CoFixpoint iterate {A : Type} (f : A -> A) (x : A) : coList A :=
{|
    uncons := Some (x, iterate f (f x));
|}.
(* end hide *)

Lemma len_iterate :
  forall (A : Type) (f : A -> A) (x : A),
    sim (len (iterate f x)) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. right.
  eexists (len (iterate f (f x))), omega. intuition.
Qed.
(* end hide *)

(* begin hide *)
CoFixpoint piterate {A : Type} (f : A -> option A) (x : A) : coList A :=
{|
    uncons := Some (x,
      match f x with
          | None => conil
          | Some y => piterate f y
      end)
|}.
(* end hide *)

Fixpoint splitAt
  {A : Type} (l : coList A) (n : nat) : option (list A * A * coList A) :=
match n, uncons l with
    | _, None => None
    | 0, Some (h, t) => Some ([], h, t)
    | S n', Some (h, t) =>
        match splitAt t n' with
            | None => None
            | Some (start, mid, rest) => Some (h :: start, mid, rest)
        end
end.

Definition nth {A : Type} (l : coList A) (n : nat) : option A :=
match splitAt l n with
    | None => None
    | Some (_, x, _) => Some x
end.

Definition take {A : Type} (l : coList A) (n : nat) : option (list A) :=
match splitAt l n with
    | None => None
    | Some (l, _, _) => Some l
end.

Definition drop {A : Type} (l : coList A) (n : nat) : option (coList A) :=
match splitAt l n with
    | None => None
    | Some (_, _, l) => Some l
end.

Fixpoint fromList {A : Type} (l : list A) : coList A :=
match l with
    | [] => conil
    | h :: t => cocons h (fromList t)
end.

Definition insert {A : Type} (l : coList A) (n : nat) (x : A)
  : option (coList A) :=
match splitAt l n with
    | None => None
    | Some (start, mid, rest) =>
        Some (app (fromList start) (cocons x (cocons mid rest)))
end.

Definition remove {A : Type} (l : coList A) (n : nat)
  : option (coList A) :=
match splitAt l n with
    | None => None
    | Some (start, _, rest) => Some (app (fromList start) rest)
end.


(** TODO: zip, unzip *)

(* begin hide *)
CoFixpoint zipW {A B C : Type}
  (f : A -> B -> C) (l1 : coList A) (l2 : coList B) : coList C :=
{|
    uncons :=
      match uncons l1, uncons l2 with
          | Some (h1, t1), Some (h2, t2) => Some (f h1 h2, zipW f t1 t2)
          | _, _ => None
      end;
|}.
(* end hide *)




(*
Require Import CoqBookPL.book.X7.

CoFixpoint fromStream {A : Type} (s : Stream A) : coList A :=
{|
    uncons := Some (hd s, fromStream (tl s));
|}.

Lemma Infinite_splitAt :
  forall (A : Type) (n : nat) (l : coList A),
    Infinite l ->
      exists (start : list A) (mid : A) (rest : coList A),
        splitAt l n = Some (start, mid, rest).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct H. rewrite p. exists [], h, t. reflexivity.
    destruct l as [[[h t] |]].
      destruct H. destruct (IHn' _ H) as (start & mid & rest & spec).
        exists (h :: start), mid, rest. cbn. inversion p. rewrite spec.
        reflexivity.
      inversion H. inversion p.
Qed.
(* end hide *)
*)

(** TODO: modyfikacje *)

(*
CoFixpoint takeWhile {A : Type} (f : A -> bool) (l : coList A) : coList A :=
{|
    uncons :=
      match uncons l with
          | None => None
          | Some (h, t) =>
              if f h then Some (h, takeWhile f t) else takeWhile f t
      end;
|}.
*)

(* begin hide *)
CoFixpoint scan
  {A B : Type} (l : coList A) (f : B -> A -> B) (b : B) : coList B :=
{|
    uncons :=
      match uncons l with
          | None => None
          | Some (h, t) => Some (b, scan t f (f b h))
      end;
|}.
(* end hide *)

(* begin hide *)
CoFixpoint intersperse {A : Type} (x : A) (l : coList A) : coList A :=
{|
    uncons :=
      match uncons l with
          | None => None
          | Some (h, t) =>
              match uncons t with
                  | None => Some (h, t)
                  | Some (h', t') => Some (h, cocons x (intersperse x t))
              end
      end;
|}.
(* end hide *)

(* begin hide *)
Inductive Finite {A : Type} : coList A -> Prop :=
    | Finite_None :
        forall l : coList A, uncons l = None -> Finite l
    | Finite_Some :
        forall (h : A) (t l : coList A),
          uncons l = Some (h, t) -> Finite t -> Finite l.

CoInductive Infinite {A : Type} (l : coList A) : Prop :=
{
    h : A;
    t : coList A;
    p : uncons l = Some (h, t);
    inf' : Infinite t;
}.
(* end hide *)

Lemma Finite_not_Infinite :
  forall (A : Type) (l : coList A),
    Finite l -> Infinite l -> False.
(* begin hide *)
Proof.
  induction 1; intro.
    destruct H0. congruence.
    apply IHFinite. destruct H1. congruence.
Qed.
(* end hide *)

Lemma sim_Infinite :
  forall (A : Type) (l1 l2 : coList A),
    lsim l1 l2 -> Infinite l1 -> Infinite l2.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [[[] | (h1 & t1 & h2 & t2 & p1 & p2 & p3 & H)]], 1.
    rewrite H in p. inversion p.
    econstructor.
      exact p2.
      rewrite p1 in p. inversion p; subst. eapply CH; eauto.
Qed.
(* end hide *)

Lemma len_Finite :
  forall (A : Type) (l : coList A),
    Finite l -> len l <> omega.
(* begin hide *)
Proof.
  induction 1; cbn.
    intro. destruct l as [[]]; cbn in *.
      inv H.
      apply (f_equal pred) in H0. cbn in H0. inv H0.
    destruct l as [[]]; cbn in *.
      intro. apply (f_equal pred) in H1. cbn in H1. inv H. inv H1.
      inv H.
Qed.
(* end hide *)

Lemma len_Infinite :
  forall (A : Type) (l : coList A),
    len l = omega -> Infinite l.
(* begin hide *)
Proof.
  cofix CH.
  destruct l as [[[h t] |]]; cbn.
    econstructor.
      cbn. reflexivity.
      apply CH. apply (f_equal pred) in H. cbn in H. inv H.
    intro. apply (f_equal pred) in H. cbn in H. inv H.
Qed.
(* end hide *)

Lemma Finite_snoc :
  forall (A : Type) (l : coList A) (x : A),
    Finite l -> Finite (snoc l x).
(* begin hide *)
Proof.
  induction 1; cbn.
    apply (Finite_Some x conil).
      cbn. rewrite H. reflexivity.
      constructor. cbn. reflexivity.
    apply (Finite_Some h (snoc t x)).
      cbn. rewrite H. reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma Infinite_snoc :
  forall (A : Type) (l : coList A) (x : A),
    Infinite l -> lsim (snoc l x) l.
(* begin hide *)
Proof.
  cofix CH.
  constructor. right. destruct H.
  exists h, (snoc t x), h, t.
  cbn. rewrite p. do 3 split.
    reflexivity.
    apply CH. assumption.
Qed.
(* end hide *)

Lemma Infinite_app_l :
  forall (A : Type) (l1 l2 : coList A),
    Infinite l1 -> Infinite (app l1 l2).
(* begin hide *)
Proof.
  cofix CH.
  destruct 1. econstructor.
    destruct l1; cbn in *; inversion p; cbn. reflexivity.
    apply CH. assumption.
Qed.
(* end hide *)

Lemma Infinite_app_r :
  forall (A : Type) (l1 l2 : coList A),
    Infinite l2 -> Infinite (app l1 l2).
(* begin hide *)
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
(* end hide *)

Lemma Finite_app :
  forall (A : Type) (l1 l2 : coList A),
    Finite l1 -> Finite l2 -> Finite (app l1 l2).
(* begin hide *)
Proof.
  induction 1; cbn; intros.
    destruct H0.
      left. cbn. rewrite H. assumption.
      eright; eauto. cbn. rewrite H. exact H0.
    eright.
      cbn. rewrite H. reflexivity.
      apply IHFinite. assumption.
Qed.
(* end hide *)

Lemma Finite_app_conv :
  forall (A : Type) (l1 l2 : coList A),
    Finite (app l1 l2) -> Finite l1 \/ Finite l2.
(* begin hide *)
Proof.
  intros. remember (app l1 l2) as l. revert l1 l2 Heql.
  induction H; intros; subst; cbn in *.
    destruct l1 as [[[h t]|]]; cbn in H.
      inversion H.
      left. constructor. cbn. reflexivity.
    destruct l1 as [[[h' t']|]]; cbn in H.
      inversion H; subst. destruct (IHFinite _ _ eq_refl).
        left. eright; eauto. cbn. reflexivity.
        right. assumption.
      left. constructor. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Finite_lmap :
  forall (A B : Type) (f : A -> B) (l : coList A),
    Finite l -> Finite (lmap f l).
(* begin hide *)
Proof.
  induction 1.
    constructor. cbn. rewrite H. reflexivity.
    eright; eauto. cbn. rewrite H. reflexivity.
Qed.
(* end hide *)

Lemma Infinite_lmap :
  forall (A B : Type) (f : A -> B) (l : coList A),
    Infinite l -> Infinite (lmap f l).
(* begin hide *)
Proof.
  cofix CH.
  destruct 1. econstructor.
    cbn. rewrite p. reflexivity.
    apply CH. assumption.
Qed.
(* end hide *)

Lemma Infinite_iterate :
  forall (A : Type) (f : A -> A) (x : A),
    Infinite (iterate f x).
(* begin hide *)
Proof.
  cofix CH.
  econstructor.
    cbn. reflexivity.
    apply CH.
Qed.
(* end hide *)

Lemma piterate_Finite :
  forall (A : Type) (f : A -> option A) (x : A),
    Finite (piterate f x) -> exists x : A, f x = None.
(* begin hide *)
Proof.
  intros. remember (piterate f x) as l.
  revert f x Heql.
  induction H; intros; subst; cbn in *; inversion H; subst.
  clear H. case_eq (f h); intros; rewrite H in *.
    eapply IHFinite. reflexivity.
    exists h. assumption.
Qed.
(* end hide *)

Lemma Infinite_splitAt :
  forall (A : Type) (n : nat) (l : coList A),
    Infinite l ->
      exists (start : list A) (x : A) (rest : coList A),
        splitAt l n = Some (start, x, rest).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct H.
      rewrite p. exists [], h, t. reflexivity.
      destruct H. rewrite p. destruct (IHn' _ H) as (start & x & rest & IH).
        rewrite IH. exists (h :: start), x, rest. reflexivity.
Qed.
(* end hide *)

Lemma Finite_zipW_l :
  forall (A B C : Type) (f : A -> B -> C) (l1 : coList A) (l2 : coList B),
    Finite l1 -> Finite (zipW f l1 l2).
(* begin hide *)
Proof.
  intros until 1. revert l2.
  induction H.
    constructor. cbn. rewrite H. reflexivity.
    destruct l2 as [[[h2 t2] |]]; cbn.
      eright.
        cbn. rewrite H. reflexivity.
        apply IHFinite.
      left. cbn. rewrite H. reflexivity.
Qed.
(* end hide *)

Lemma Finite_zipW_r :
  forall (A B C : Type) (f : A -> B -> C) (l1 : coList A) (l2 : coList B),
    Finite l2 -> Finite (zipW f l1 l2).
(* begin hide *)
Proof.
  intros until 1. revert l1.
  induction H.
    destruct l1 as [[[h1 t1] |]]; constructor; cbn.
      rewrite H. 1-2: reflexivity.
    destruct l1 as [[[h1 t1] |]]; cbn.
      eright.
        cbn. rewrite H. reflexivity.
        apply IHFinite.
      left. cbn. reflexivity.
Qed.
(* end hide *)

Lemma Infinite_zipW_l :
  forall (A B C : Type) (f : A -> B -> C) (l1 : coList A) (l2 : coList B),
    Infinite (zipW f l1 l2) -> Infinite l1.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1. destruct l1 as [[[h1 t1] |]]; cbn in *.
    econstructor.
      cbn. reflexivity.
      destruct (uncons l2) as [[] |]; inv p. eapply CH. eassumption.
    inv p.
Qed.
(* end hide *)

Lemma Infinite_zipW_r :
  forall (A B C : Type) (f : A -> B -> C) (l1 : coList A) (l2 : coList B),
    Infinite (zipW f l1 l2) -> Infinite l1.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1.
  destruct l1 as [[[h1 t1] |]], l2 as [[[h2 t2] |]]; cbn in *; inv p.
  econstructor; cbn; eauto.
Qed.
(* end hide *)

Inductive Exists {A : Type} (P : A -> Prop) : coList A -> Prop :=
    | Exists_hd :
        forall (l : coList A) (h : A) (t : coList A),
          uncons l = Some (h, t) -> P h -> Exists P l
    | Exists_tl :
        forall (l : coList A) (h : A) (t : coList A),
          uncons l = Some (h, t) -> Exists P t -> Exists P l.

CoInductive All {A : Type} (P : A -> Prop) (l : coList A) : Prop :=
{
    All' :
      uncons l = None \/
      exists (h : A) (t : coList A),
        uncons l = Some (h, t) /\ P h /\ All P t;
}.