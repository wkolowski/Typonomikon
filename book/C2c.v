(** * C2c: Izomorfizmy typów [TODO] *)

Require Import FunctionalExtensionality.

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
  coel := fun x => x;
  coer := fun x => x;
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

(** * Zachowywanie izomorfizmów *)

#[refine, export]
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