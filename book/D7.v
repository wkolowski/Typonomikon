(** * D7: Listy niepuste [TODO] *)

Inductive Nel (A : Type) : Type := Cons
{
  hd : A;
  tl : option (Nel A);
}.

Arguments hd {A} _.
Arguments tl {A} _.
Arguments Cons {A} _ _.

Fixpoint Nel_ind'
  (A : Type) (P : Nel A -> Prop)
  (hd' : forall h : A, P (Cons h None))
  (tl' : forall (h : A) (t : Nel A), P t -> P (Cons h (Some t)))
  (l : Nel A) {struct l} : P l :=
match l with
| {| hd := h; tl := None |}   => hd' h
| {| hd := h; tl := Some t |} => tl' h t (Nel_ind' A P hd' tl' t)
end.

Definition nsingl {A : Type} (x : A) : Nel A :=
{|
  hd := x;
  tl := None;
|}.

Fixpoint nmap {A B : Type} (f : A -> B) (l : Nel A) : Nel B :=
{|
  hd := f (hd l);
  tl := option_map (nmap f) (tl l);
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

Lemma napp_assoc :
  forall {A : Type} (l1 l2 l3 : Nel A),
    napp (napp l1 l2) l3 = napp l1 (napp l2 l3).
Proof.
  now induction l1 as [h | h t] using Nel_ind'; cbn; intros; rewrite ?IHt.
Qed.

Lemma nmap_napp :
  forall {A B : Type} (f : A -> B) (l1 l2 : Nel A),
    nmap f (napp l1 l2) = napp (nmap f l1) (nmap f l2).
Proof.
  now induction l1 as [h | h t] using Nel_ind'; cbn; intros; rewrite ?IHt.
Qed.

Fixpoint relate_Nel {A : Type} (RA : A -> A -> Prop) (l1 l2 : Nel A) : Prop :=
  RA (hd l1) (hd l2) /\
match tl l1, tl l2 with
| None, None => True
| Some t1, Some t2 => relate_Nel RA t1 t2
| _      , _       => False
end.

(*
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
  apply f_equal2.
  - easy.
  - inversion relate_tl0.
    + easy.
    + now apply f_equal, IH.
Defined.

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
*)