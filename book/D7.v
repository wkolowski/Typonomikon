(** * D7: Listy niepuste [TODO] *)

(** * Typ list niepustych (TODO) *)

Inductive Nel (A : Type) : Type := MkNel
{
  hd : A;
  tl : option (Nel A);
}.

Arguments hd {A} _.
Arguments tl {A} _.
Arguments MkNel {A} _ _.

Definition nsingl {A : Type} (x : A) : Nel A :=
{|
  hd := x;
  tl := None;
|}.

Definition ncons {A : Type} (h : A) (t : Nel A) : Nel A :=
{|
  hd := h;
  tl := Some t;
|}.

(** * Porządna reguła indukcji (TODO) *)

Fixpoint Nel_ind'
  (A : Type) (P : Nel A -> Prop)
  (hd' : forall h : A, P (MkNel h None))
  (tl' : forall (h : A) (t : Nel A), P t -> P (MkNel h (Some t)))
  (l : Nel A) {struct l} : P l :=
match l with
| {| hd := h; tl := None |}   => hd' h
| {| hd := h; tl := Some t |} => tl' h t (Nel_ind' A P hd' tl' t)
end.

(** * Równość, różność i relatory (TODO) *)

Fixpoint relate_Nel {A : Type} (RA : A -> A -> Prop) (l1 l2 : Nel A) : Prop :=
  RA (hd l1) (hd l2) /\
match tl l1, tl l2 with
| None, None => True
| Some t1, Some t2 => relate_Nel RA t1 t2
| _      , _       => False
end.

Lemma eq_Nel_intro' :
  forall {A : Type} {l1 l2 : Nel A},
    relate_Nel eq l1 l2 -> l1 = l2.
Proof.
  fix IH 2.
  destruct l1 as [h1 [t1 |]], l2 as [h2 [t2 |]];  intros [p E]; cbn in *.
  - apply f_equal2; [easy |].
    now apply f_equal, IH.
  - easy.
  - easy.
  - now apply f_equal2.
Defined.

Inductive Relate_option {A : Type} (R : A -> A -> Prop) : option A -> option A -> Prop :=
| Relate_None : Relate_option R None None
| Relate_Some : forall a1 a2 : A, R a1 a2 -> Relate_option R (Some a1) (Some a2).

Inductive Relate_Nel {A : Type} (R : A -> A -> Prop) (l1 l2 : Nel A) : Prop :=
{
  relate_hd : R (hd l1) (hd l2);
  relate_tl : Relate_option (Relate_Nel R) (tl l1) (tl l2);
}.

Arguments relate_hd {A R l1 l2} _.
Arguments relate_tl {A R l1 l2} _.

Lemma eq_Nel_intro :
  forall {A : Type} {l1 l2 : Nel A},
    Relate_Nel eq l1 l2 -> l1 = l2.
Proof.
  fix IH 4.
  destruct 1, l1 as [h1 t1], l2 as [h2 t2]; cbn in *.
  destruct relate_hd0, relate_tl0; [easy |].
  now rewrite (IH _ _ _ H).
Defined.

Lemma eq_Nel_refl :
  forall {A : Type} {R : A -> A -> Prop},
    (forall x : A, R x x) ->
  forall l : Nel A,
    Relate_Nel R l l.
Proof.
  intros A R Hrefl l.
  induction l as [| h t] using Nel_ind'.
  - constructor; cbn; [easy |].
    now constructor.
  - constructor; cbn; [easy |].
    now constructor.
Defined.

Lemma eq_Nel_elim :
  forall {A : Type} {l1 l2 : Nel A},
    l1 = l2 -> Relate_Nel eq l1 l2.
Proof.
  intros A l1 l2 ->.
  now apply eq_Nel_refl.
Defined.

Lemma eq_Nel_comp :
  forall {A : Type} {l1 l2 : Nel A} (r : Relate_Nel eq l1 l2),
    eq_Nel_elim (eq_Nel_intro r) = r.
Proof.
  fix IH 4.
  destruct r, l1 as [h1 t1], l2 as [h2 t2]; cbn in *.
  destruct relate_hd0, relate_tl0; cbn; [easy |].
  unfold eq_ind_r, eq_ind, eq_sym.
  destruct (eq_Nel_intro r); cbn.
  do 2 f_equal.
Abort.

(** * Podstawowe funkcje na listach niepustych *)

Fixpoint len {A : Type} (l : Nel A) : nat :=
match tl l with
| None => 1
| Some l' => 1 + len l'
end.

Fixpoint snoc {A : Type} (x : A) (l : Nel A) : Nel A :=
{|
  hd := hd l;
  tl := Some
    match tl l with
    | None    => nsingl x
    | Some l' => snoc x l'
    end
|}.

Fixpoint napp {A : Type} (l1 l2 : Nel A) : Nel A :=
{|
  hd := hd l1;
  tl :=
    match tl l1 with
    | None => Some l2
    | Some t1 => Some (napp t1 l2)
    end;
|}.

Fixpoint rev {A : Type} (l : Nel A) : Nel A :=
match tl l with
| None => l
| Some l' => snoc (hd l) (rev l')
end.

Fixpoint nmap {A B : Type} (f : A -> B) (l : Nel A) : Nel B :=
{|
  hd := f (hd l);
  tl := option_map (nmap f) (tl l);
|}.

Fixpoint join {A : Type} (l : Nel (Nel A)) : Nel A :=
match tl l with
| None => hd l
| Some l' => napp (hd l) (join l')
end.

Fixpoint bind {A B : Type} (f : A -> Nel B) (l : Nel A) : Nel B :=
match tl l with
| None => f (hd l)
| Some l' => napp (f (hd l)) (bind f l')
end.

Fixpoint replicate {A : Type} (n : nat) (x : A) : Nel A :=
match n with
| 0 => nsingl x
| S n' => ncons x (replicate n' x)
end.
(*
{|
  hd := x;
  tl :=
    match n with
    | 0    => None
    | S n' => Some (replicate n' x)
    end;
|}.
*)

Fixpoint iterate {A : Type} (f : A -> A) (n : nat) (x : A) : Nel A :=
match n with
| 0    => nsingl x
| S n' => ncons x (iterate f n' (f x))
end.

Definition uncons {A : Type} (l : Nel A) : option (A * Nel A) :=
match tl l with
| None => None
| Some l' => Some (hd l, l')
end.

Fixpoint last {A : Type} (l : Nel A) : A :=
match tl l with
| None => hd l
| Some l' => last l'
end.

Fixpoint init {A : Type} (l : Nel A) : option (Nel A) :=
match tl l with
| None => None
| Some l' => Some
    match init l' with
    | None => nsingl (hd l)
    | Some l'' => ncons (hd l) l''
    end
end.

Fixpoint nth {A : Type} (n : nat) (l : Nel A) : option A :=
match n, tl l with
| 0   , _       => Some (hd l)
| _   , None    => None
| S n', Some l' => nth n' l'
end.

Fixpoint takeS {A : Type} (n : nat) (l : Nel A) : Nel A :=
match tl l, n with
| None  , _    => l
| Some t, 0    => nsingl (hd l)
| Some t, S n' => ncons (hd l) (takeS n' t)
end.

Fixpoint take {A : Type} (n : nat) (l : Nel A) : list A :=
match n, tl l with
| 0   , _      => nil
| S n', None   => cons (hd l) nil
| S n', Some t => cons (hd l) (take n' t)
end.

Fixpoint toList {A : Type} (l : Nel A) : list A :=
match tl l with
| None   => cons (hd l) nil
| Some t => cons (hd l) (toList t)
end.

Fixpoint drop {A : Type} (n : nat) (l : Nel A) : list A :=
match n, tl l with
| 0   , _      => toList l
| S n', None   => nil
| S n', Some t => drop n' t
end.

Fixpoint zip {A B : Type} (l1 : Nel A) (l2 : Nel B) : Nel (A * B) :=
match tl l1, tl l2 with
| None   ,   _     => nsingl (hd l1, hd l2)
| _      , None    => nsingl (hd l1, hd l2)
| Some t1, Some t2 => ncons (hd l1, hd l2) (zip t1 t2)
end.

Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (l1 : Nel A) (l2 : Nel B) : Nel C :=
match tl l1, tl l2 with
| None   ,   _     => nsingl (f (hd l1) (hd l2))
| _      , None    => nsingl (f (hd l1) (hd l2))
| Some t1, Some t2 => ncons (f (hd l1) (hd l2)) (zipWith f t1 t2)
end.

Fixpoint unzip {A B : Type} (l : Nel (A * B)) : Nel A * Nel B :=
match tl l with
| None => (nsingl (fst (hd l)), nsingl (snd (hd l)))
| Some t =>
  match unzip t with
  | (t1, t2) => (ncons (fst (hd l)) t1, ncons (snd (hd l)) t2)
  end
end.

Fixpoint unzipWith {A B C : Type} (f : A -> B * C) (l : Nel A) : Nel B * Nel C :=
match tl l with
| None => (nsingl (fst (f (hd l))), nsingl (snd (f (hd l))))
| Some t =>
  match unzipWith f t with
  | (t1, t2) => (ncons (fst (f (hd l))) t1, ncons (snd (f (hd l))) t2)
  end
end.

Fixpoint unzis {A B : Type} (l : Nel (A + B)) : list A * list B :=
match tl l with
| None   =>
  match hd l with
  | inl a => (cons a nil, nil)
  | inr b => (nil, cons b nil)
  end
| Some t =>
  let '(t1, t2) := unzis t in
    match hd l with
    | inl a => (cons a t1, t2)
    | inr b => (t1, cons b t2)
    end
end.

Fixpoint unzis' {A B : Type} (l : Nel (A + B)) : list A * list B :=
  (fun '(t1, t2) =>
    match hd l with
    | inl a => (cons a nil, nil)
    | inr b => (nil, cons b nil)
    end)
match tl l with
| None   => (nil, nil)
| Some t => unzis' t
end.

(** * Funkcje na listach niepustych z predykatem boolowskim *)

Fixpoint any {A : Type} (p : A -> bool) (l : Nel A) : bool :=
  p (hd l) ||
match tl l with
| None   => false
| Some t => any p t
end.

Fixpoint all {A : Type} (p : A -> bool) (l : Nel A) : bool :=
  p (hd l) &&
match tl l with
| None   => true
| Some t => all p t
end.

Fixpoint count {A : Type} (p : A -> bool) (l : Nel A) : nat :=
  (if p (hd l) then 1 else 0) +
match tl l with
| None   => 0
| Some t => count p t
end.

Fixpoint filter {A : Type} (p : A -> bool) (l : Nel A) : list A :=
  (if p (hd l) then cons (hd l) else @id (list A))
match tl l with
| None   => nil
| Some t => filter p t
end.

Fixpoint takeWhile {A : Type} (p : A -> bool) (l : Nel A) : list A :=
  (if p (hd l) then cons (hd l) else @id (list A))
match tl l with
| None   => nil
| Some t => takeWhile p t
end.

Fixpoint takeWhile' {A : Type} (p : A -> bool) (l : Nel A) : option (Nel A) :=
  if negb (p (hd l))
  then None
  else Some (MkNel (hd l)
match tl l with
| None => None
| Some t => takeWhile' p t
end).

Fixpoint dropWhile {A : Type} (p : A -> bool) (l : Nel A) : list A :=
  if negb (p (hd l)) then toList l else cons (hd l)
match tl l with
| None   => nil
| Some t => dropWhile p t
end.

(** * Skomplikowańsze funkcje (TODO) *)

Fixpoint intersperse {A : Type} (x : A) (l : Nel A) : Nel A :=
match tl l with
| None   => l
| Some t => ncons (hd l) (ncons x (intersperse x t))
end.

Fixpoint extrasperse {A : Type} (x : A) (l : Nel A) : Nel A :=
  ncons x (ncons (hd l)
match tl l with
| None   => nsingl x
| Some t => extrasperse x t
end).

Fixpoint pmap {A B : Type} (f : A -> option B) (l : Nel A) : list B :=
  match f (hd l) with
  | None   => @id (list B)
  | Some b => cons b
  end
match tl l with
| None   => nil
| Some t => pmap f t
end.

(** * [foldr] *)

Fixpoint foldr {A B : Type} (b : B) (f : A -> B -> B) (l : Nel A) : B :=
match tl l with
| None => f (hd l) b
| Some t => f (hd l) (foldr b f t)
end.

(** * Predykaty na listach niepustych *)

Inductive Elem {A : Type} (x : A) : Nel A -> Prop :=
| ElemZ : forall {l : Nel A}, hd l = x -> Elem x l
| ElemS : forall {l t : Nel A}, tl l = Some t -> Elem x t -> Elem x l.

Inductive Exists {A : Type} (P : A -> Prop) : Nel A -> Prop :=
| ExZ : forall {l : Nel A}, P (hd l) -> Exists P l
| ExS : forall {l t : Nel A}, tl l = Some t -> Exists P t -> Exists P l.

Inductive Forall_option {A : Type} (P : A -> Type) : option A -> Type :=
| Forall_None : Forall_option P None
| Forall_Some : forall a : A, P a -> Forall_option P (Some a).

Inductive Forall {A : Type} (P : A -> Type) (l : Nel A) : Type :=
{
  Forall_hd : P (hd l);
  Forall_tl : Forall_option (Forall P) (tl l);
}.

Definition DirectSubterm {A : Type} (l1 l2 : Nel A) : Prop :=
  tl l2 = Some l1.

(** * Właściwości funkcji na listach niepustych *)

Lemma len_snoc :
  forall {A : Type} (x : A) (l : Nel A),
    len (snoc x l) = 1 + len l.
Proof.
  now induction l using Nel_ind'; cbn; intros; [| rewrite IHl].
Qed.

Lemma len_napp :
  forall {A : Type} (l1 l2 : Nel A),
    len (napp l1 l2) = len l1 + len l2.
Proof.
  now induction l1 using Nel_ind'; cbn; intros; [| rewrite IHl1].
Qed.

Lemma len_rev :
  forall {A : Type} (l : Nel A),
    len (rev l) = len l.
Proof.
  induction l using Nel_ind'; cbn; intros; [easy |].
  now rewrite len_snoc, IHl.
Qed.

Lemma len_nmap :
  forall {A B : Type} (f : A -> B) (l : Nel A),
    len (nmap f l) = len l.
Proof.
  now induction l using Nel_ind'; cbn; [| rewrite IHl].
Qed.

Lemma napp_assoc :
  forall {A : Type} (l1 l2 l3 : Nel A),
    napp (napp l1 l2) l3 = napp l1 (napp l2 l3).
Proof.
  now induction l1 using Nel_ind'; cbn; intros; [| rewrite IHl1].
Qed.

Lemma nmap_napp :
  forall {A B : Type} (f : A -> B) (l1 l2 : Nel A),
    nmap f (napp l1 l2) = napp (nmap f l1) (nmap f l2).
Proof.
  now induction l1 using Nel_ind'; cbn; intros; [| rewrite IHl1].
Qed.