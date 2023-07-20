(** * G7: Mieszane typy induktywno-koinduktywne [TODO] *)

From Typonomikon Require Import B3b.
From Typonomikon Require Import F2.

(** * Cthulhu zawsze płynie w lewo (TODO) *)

(** ** Pierwsze podejście (TODO) *)

Module Cthulhu_v1.

Inductive CthulhuCI (C I A : Type) : Type :=
| E
| N : A -> C -> I -> CthulhuCI C I A.

Arguments E {C I A}.
Arguments N {C I A} _ _ _.

Module CI.

CoInductive CthulhuC (I A : Type) : Type := MkC
{
  Out : CthulhuCI (CthulhuC I A) I A;
}.

Arguments Out {I A} _.

Inductive Cthulhu (A : Type) : Type :=
| In : CthulhuC (Cthulhu A) A -> Cthulhu A.

Arguments In {A} _.

Definition out {A : Type} (c : Cthulhu A) : CthulhuC (Cthulhu A) A :=
match c with
| In c' => c'
end.

CoFixpoint replicateI (n : nat) : CthulhuC (Cthulhu nat) nat :=
{|
  Out := N n (replicateI (S n)) (In {| Out := E; |});
|}.

Definition replicate (n : nat) : Cthulhu nat :=
  In (replicateI n).

End CI.

Module IC.

Inductive CthulhuI (C A : Type) : Type :=
| In : CthulhuCI C (CthulhuI C A) A -> CthulhuI C A.

Arguments In {C A} _.

CoInductive Cthulhu (A : Type) : Type := MkC
{
  Out : CthulhuI (Cthulhu A) A;
}.

Arguments MkC {A} _.
Arguments Out {A} _.

CoFixpoint replicate (n : nat) : Cthulhu nat :=
{|
  Out := In (N n (replicate (S n)) (In E));
|}.

End IC.

(*
Fixpoint mapI
  {C D A B : Type} (f : A -> B)
  (map : C -> D)
  (c : CthulhuI C A) : CthulhuI C B :=
match c with
| In E => In E
| In (N v l (In r)) => In (N (f v) (map l) (map r))
end.

CoFixpoint map {A B : Type} (f : A -> B) (c : Cthulhu A) : Cthulhu B :=
{|
  Out :=
    match Out c with
    | In E => In E
    | In (N v l r) => In (N (f v) (map f l) (Out (map f (MkC r))))
    end;
|}.
*)

End Cthulhu_v1.

(** ** Drugie podejście *)

Module Cthulhu_v2.

Inductive CthulhuIC (I C : Type -> Type) (A : Type) : Type :=
| E
| N : A -> C A -> I A -> CthulhuIC I C A.

Arguments E {I C A}.
Arguments N {I C A} _ _ _.

Inductive CthulhuI (C : Type -> Type) (A : Type) : Type :=
| In : CthulhuIC (CthulhuI C) C A -> CthulhuI C A.

Arguments In {C A} _.

CoInductive Cthulhu (A : Type) : Type := MkC
{
  Out : CthulhuI Cthulhu A;
}.

Arguments MkC {A} _.
Arguments Out {A} _.

Fixpoint mapI
  {C : Type -> Type} (map : forall {A B : Type}, (A -> B) -> C A -> C B)
  {A B : Type} (f : A -> B)
  (c : CthulhuI C A) : CthulhuI C B :=
match c with
| In E => In E
| In (N v l r) => In (N (f v) (map f l) (mapI (@map) f r))
end.

Fail
CoFixpoint map {A B : Type} (f : A -> B) (c : Cthulhu A) : Cthulhu B :=
{|
  Out :=
    match Out c with
    | In E => In E
    | In (N v l r) => In (N (f v) (map f l) (mapI (@map) f r))
    end;
|}.

Fail
Definition map {A B : Type} (f : A -> B) (c : Cthulhu A) : Cthulhu B :=
  cofix map (c : Cthulhu A) : Cthulhu B :=
  match Out c with
  | In E => MkC (In E)
  | In (N v l r) => MkC (In
      (fix mapI (ci : CthulhuI Cthulhu A) : CthulhuI Cthulhu B :=
      match ci with
      | In E => In E
      | In (N v l r) => In (N (f v) (map l) (mapI r))
      end) r)
  end.

End Cthulhu_v2.

(** ** Trzecie podejście (TODO) *)

Module Cthulhu_v3.

Inductive TreeF (A X : Type) : Type :=
| E : TreeF A X
| N : A -> TreeF A X -> X -> TreeF A X.

Arguments E {A X}.
Arguments N {A X} _ _ _.

CoInductive Tree (A : Type) : Type :=
{
  Out : TreeF A (Tree A);
}.

Arguments Out {A} _.

Fixpoint inums (n : nat) : TreeF nat (Tree nat) :=
match n with
| 0 => E
| S n' => N n' (inums n') {| Out := E |}
end.

CoFixpoint nums (n : nat) : Tree nat :=
{|
  Out := N n (inums n) (nums (S n));
|}.

Fixpoint leftmostF {A X : Type} (t : TreeF A X) : option A :=
match t with
| E => None
| N v l _ =>
        match leftmostF l with
        | None   => Some v
        | Some x => Some x
        end
end.

Definition leftmost {A : Type} (t : Tree A) : option A :=
match Out t with
| E => None
| N v l _ =>
  match leftmostF l with
  | None   => Some v
  | Some x => Some x
  end
end.

Definition leftmost' {A : Type} (t : Tree A) : option A :=
  leftmostF (Out t).

Lemma leftmost_leftmost' :
  forall {A : Type} (t : Tree A),
    leftmost t = leftmost' t.
Proof.
  destruct t as [[]]; cbn; reflexivity.
Qed.

Fixpoint mapF {A B X Y : Type} (f : A -> B) (g : X -> Y) (t : TreeF A X) {struct t} : TreeF B Y :=
match t with
| E       => E
| N x l r => N (f x) (mapF f g l) (g r)
end.

(* CoFixpoint map {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
{|
  Out :=
    match Out t with
    | E => E
    | N x l r => N (f x) (mapF f (map f) l) (map f r)
    end;
|}. *)

Fixpoint complete {A : Type} (n : nat) (x : A) (t : Tree A) : TreeF A (Tree A) :=
match n with
| 0    => E
| S n' => N x (complete n' x t) t
end.

Fail CoFixpoint complete' {A : Type} (n : nat) (x : A) : Tree A :=
{|
  Out :=
    N x
      ((fix aux (n : nat) : TreeF A (Tree A) :=
        match n with
        | 0 => E
        | S n' => N x (aux n') (complete' n x)
        end) n)
      (complete' n x);
|}.

Fail Definition max (n : nat) (m : conat) : conat := max (from_nat n) m.

(* #<a class='link' href='https://www.cse.chalmers.se/~nad/publications/danielsson-docent.pdf'>
   Sprawdź to</a>#. *)

(* Fixpoint max (n : nat) (m : conat) : conat :=
match n, out m with
| 0   , _ => m
| S n', S m' => S (max n' m')
 *)

(*Parameter elem : forall A : Type, A -> BTree A -> Prop.*)




(** Basic observers *)
(* Parameter isEmpty : forall A : Type, BTree A -> bool. *)

(* Parameter root : forall A : Type, BTree A -> option A. *)
(* Parameter left : forall A : Type, BTree A -> option (BTree A). *)
(* Parameter right : forall A : Type, BTree A -> option (BTree A). *)

(* Parameter unN : forall A : Type, BTree A -> option (A * BTree A * BTree A). *)

(*
CoFixpoint size {A : Type} (t : Tree A) : conat :=
{|
  out :=
    match Out t with
    | E => Z
    | N _ l r => S (size l) (size r)
    end;
|}.
*)

(* TODO: zdefiniować wincyj funkcji *)
(*
Parameter height : forall A : Type, BTree A -> nat.

Parameter rightmost : forall A : Type, BTree A -> option A.

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter bfs_aux :
  forall A : Type, list (BTree A) -> list A -> list A.

Parameter bfs : forall A : Type, BTree A -> list A.

(** Basic operations *)
Parameter mirror' : forall A : Type, BTree A -> BTree A.

Fixpoint mirror {A : Type} (t : BTree A) : BTree A :=
match t with
| E => E
| N v l r => N v (mirror r) (mirror l)
end.

(*

Lemma mirror_bijective :
  forall A : Type, bijective (@mirror A).
Proof.
  unfold bijective, injective, surjective. split.
    induction x; destruct x'; cbn; inversion 1; subst; clear H.
      reflexivity.
      rewrite (IHx1 _ H3), (IHx2 _ H2). reflexivity.
    induction b.
      exists E. cbn. reflexivity.
      destruct IHb1 as [r Hr], IHb2 as [l Hl].
        exists (N a l r). cbn. rewrite Hl, Hr. reflexivity.
Qed.
*)

Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> BTree A.

Parameter index : forall A : Type, list bool -> BTree A -> option A.
Parameter nth : forall A : Type, nat -> BTree A -> option A.

Parameter take : forall A : Type, nat -> BTree A -> BTree A.
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).

Parameter intersperse : forall A : Type, A -> BTree A -> BTree A.

Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.

(** Operacje z predykatem boolowskim. *)
Parameter any : forall A : Type, (A -> bool) -> BTree A -> bool.
Parameter all : forall A : Type, (A -> bool) -> BTree A -> bool.

Parameter find : forall A : Type, (A -> bool) -> BTree A -> option A.
Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).

Parameter count : forall A : Type, (A -> bool) -> BTree A -> nat.

Parameter takeWhile : forall A : Type, (A -> bool) -> BTree A -> BTree A.

Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).

(** Operacje z funkcją. *)
Parameter map : forall A B : Type, (A -> B) -> BTree A -> BTree B.

Parameter zipWith :
  forall A B C : Type, (A -> B -> C) -> BTree A -> BTree B -> BTree C.

Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.

(** foldy i scany *)

(** Predykaty *)

Parameter Elem : forall A : Type, A -> BTree A -> Prop.

Parameter Any : forall A : Type, (A -> Prop) -> BTree A -> Prop.
Parameter All : forall A : Type, (A -> Prop) -> BTree A -> Prop.

Parameter Dup : forall A : Type, BTree A -> Prop.

Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtMost : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.

Parameter SameStructure : forall A B : Type, BTree A -> BTree B -> Prop.
Parameter SameShape : forall A B : Type, BTree A -> BTree B -> Prop.

Parameter subtree : forall A : Type, BTree A -> BTree A -> Prop.
Parameter Subterm : forall A : Type, BTree A -> BTree A -> Prop.
*)

End Cthulhu_v3.

(** * Wycinanki-indukcjanki, czyli jak wyciąć typ mieszany z typu koinduktywnego (TODO) *)

Module InductiveScissors.

CoInductive NETree (A : Type) : Type :=
{
  root  : A;
  left  : option (NETree A);
  right : option (NETree A);
}.

Arguments root  {A} _.
Arguments left  {A} _.
Arguments right {A} _.

Inductive WFL {A : Type} : NETree A -> Prop :=
| WFL_None : forall {t : NETree A}, left t = None -> WFL t
| WFL_Some : forall {t t' : NETree A}, left t = Some t' -> WFL t' ->
 WFL t.

Arguments WFL_None {A t} _.

CoInductive WF {A : Type} (t : NETree A) : Prop :=
{
  rootWF : WFL t;
  rightWF : right t = None \/ exists t' : NETree A, right t = Some t' /\ WF t'
}.

(* TODO: fix *)
(*
Fixpoint leftmost {A : Type} {t : NETree A} (wf : WFL t) {struct t} : A :=
match left t with
| None => root t
| Some t' =>
match wf with
| WFL_None _ => root t
| WFL_Some _ wf' => leftmost wf'
end.
*)

End InductiveScissors.

(** * Transformatory strumieni (TODO) *)

(** ** Pierwsze podejście *)

Module StreamProcessor_v1.

Inductive SPXY (X Y A B : Type) : Type :=
| PutX : B -> X -> SPXY X Y A B
| GetX : (A -> Y) -> SPXY X Y A B.

Arguments PutX {X Y A B} _ _.
Arguments GetX {X Y A B} _.

CoInductive SP' (A B : Type) : Type :=
{
  Out : SPXY (SP' A B) (SP' A B) A B;
}.

Arguments Out {A B} _.

Inductive WF {A B : Type} : SP' A B -> Type :=
| WF_Put :
    forall (sp : SP' A B) (h : B) (t : SP' A B),
      Out sp = PutX h t -> WF sp
| wF_Get :
    forall (sp : SP' A B) (get : A -> SP' A B),
      Out sp = GetX get -> (forall a : A, WF (get a)) -> WF sp.

Record SP (A B : Type) : Type :=
{
  sp : SP' A B;
  wf : WF sp;
}.

Definition compSP {A B C : Type} (f : SP A B) (g : SP B C) : SP A C.
Proof.
  esplit. Unshelve. all: cycle 1.
  - destruct f as [f wff], g as [g wfg].
    revert f g wff wfg. cofix compSP. intros.
    inversion wfg as [g' h t H1 H2 | g' get H1 H2 H3].
    + refine {| Out := PutX h _ |}. (* exact (compSP f t wff). *)
Abort.

(** The first, naive way of doing it. *)

(*
Fixpoint head {A B : Type} (g : SP' A B) (s : Stream A) : B :=
match g with
| In (PutX h t) => h
| In (GetX g')  => head (g' (hd s)) (tl s)
end.

Fixpoint tail {A B : Type} (g : SP' A B) (s : Stream A) : SP A B * Stream A :=
match g with
| In (PutX h t) => (t, s)
| In (GetX g')  => tail (g' (hd s)) (tl s)
end.

CoFixpoint toStream {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
{|
  hd :=
    match Out f with
    | PutX h _ => h
    | GetX g   => head (g (hd s)) (tl s)
    end;
  tl :=
    match Out f with
    | PutX _ t => toStream t s
    | GetX g   => let (f', s') := tail (g (hd s)) (tl s) in toStream f' s'
    end;
|}.

(** A better way. *)

Fixpoint aux {A B : Type} (g : SP' A B) (s : Stream A) : B * (SP A B * Stream A) :=
match g with
| In (PutX h t) => (h, (t, s))
| In (GetX g')  => aux (g' (hd s)) (tl s)
end.

CoFixpoint toStream' {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
match Out f with
| PutX h t =>
  {|
    hd := h;
    tl := toStream' t s;
  |}
| GetX g   => let '(h, (f', s')) := aux (g (hd s)) (tl s) in
  {|
    hd := h;
    tl := toStream' f' s';
  |}
end.

(** Lighter syntax. *)

CoFixpoint toStream'' {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
match Out f with
| PutX h t => scons h (toStream'' t s)
| GetX g   =>
  let '(h, (f', s')) := aux (g (hd s)) (tl s) in
    scons h (toStream'' f' s')
end.

(** Some proofs. *)

Lemma head_aux :
  forall {A B : Type} (g : SP' A B) (s : Stream A),
    head g s = fst (aux g s).
Proof.
  fix IH 3.
  intros A B [[h t | g']] s; cbn.
    reflexivity.
    apply IH.
Qed.

Lemma tail_aux :
  forall {A B : Type} (g : SP' A B) (s : Stream A),
    tail g s = snd (aux g s).
Proof.
  fix IH 3.
  intros A B [[h t | g']] s; cbn.
    reflexivity.
    apply IH.
Qed.

Lemma eq_Out :
  forall {A B : Type} (x y : SP A B),
    Out x = Out y -> x = y.
Proof.
  intros A B [] []. cbn. destruct 1. reflexivity.
Qed.

Lemma eq_Stream :
  forall {A : Type} (s1 s2 : Stream A),
    hd s1 = hd s2 -> tl s1 = tl s2 -> s1 = s2.
Proof.
  intros A [] []. cbn. intros [] []. reflexivity.
Qed.

Lemma toStream'_eq :
  forall {A B : Type} (f : SP A B) (s : Stream A),
    toStream' f s =
    match Out f with
    | PutX h t =>
      {|
        hd := h;
        tl := toStream' t s;
      |}
    | GetX g   => let '(h, (f', s')) := aux (g (hd s)) (tl s) in
      {|
        hd := h;
        tl := toStream' f' s';
      |}
  end.
Proof.
  intros. apply eq_Stream. destruct f as [[]]; cbn.
Admitted.

Lemma toStream_toStream' :
  forall {A B : Type} (f : SP A B) (s : Stream A),
    sim (toStream f s) (toStream' f s).
Proof.
  cofix CH.
  destruct f as [[h t | gsp]].
    constructor; cbn.
      reflexivity.
      apply CH.
    {
      constructor; cbn.
        rewrite head_aux, toStream'_eq. cbn. destruct (aux (gsp (hd s)) (tl s)), p; cbn. reflexivity.
        rewrite tail_aux, toStream'_eq. cbn. destruct (aux (gsp (hd s)) (tl s)), p; cbn. apply CH.
    }
Qed.

(** Composition of stream processors. *)

(* Fixpoint whnf {A B : Type} (g : SP' B C) (i : SP A B) : C * (SP B C * SP A B) :=
match g with
| In (PutX h t) => (h, (t, i))
| In (GetX g')  => whnf (g' (hd s)) (tl s)
end.
 *)

Definition comp {X Y A B C : Type} (f : SPXY X Y A B) (g : SPXY X Y B C) : SPXY X Y A C.
Proof.
  destruct g as [hc tc | g'].
    refine (PutX hc tc).
Abort.

Fixpoint compMix {A B C : Type} (f : SP' A B) (g : SP B C) {struct f} : SP' A C.
Proof.
  destruct g as [[hc tc | g']].
    refine (In (PutX hc _)).
Abort.

Fixpoint compI {A B C : Type} (f : SP' A B) (g : SP' B C) : SP' A C.
Proof.
  destruct g as [[hc tc | g']].
    refine (In (PutX hc _)). destruct f as [[hb tb | f']].
      admit.
      constructor. apply GetX. intro a. refine (compI _ _ _ (f' a) _). apply (compI _ B _).
Abort.

CoFixpoint compSP {A B C : Type} (f : SP A B) (g : SP B C) : SP A C.
Proof.
  constructor.
  destruct g as [[hc tc | g']].
    apply (PutX hc). exact (compSP _ _ _ f tc).
    destruct f as [[hb tb | f']].
      apply (compSP A B C).
        exact tb.
        admit.
      apply GetX. intro a.
Abort.
*)

End StreamProcessor_v1.

(** ** Drugie podejście *)

Module StreamProcessor_v2.

Set Primitive Projections.

Inductive SPX (X A B : Type) : Type :=
| PutX : B -> X -> SPX X A B
| GetX : (A -> SPX X A B) -> SPX X A B.

Arguments PutX {X A B} _ _.
Arguments GetX {X A B} _.

CoInductive SP (A B : Type) : Type := MkSP
{
  Out : SPX (SP A B) A B;
}.

Arguments MkSP {A B} _.
Arguments Out  {A B} _.

Notation SP' A B := (SPX (SP A B) A B).

Notation Put := (fun b x => MkSP (PutX b x)).
Notation Get := (fun f => MkSP (GetX f)).

Fail CoFixpoint toStream {A B : Type} (sp : SP A B) (s : Stream A) : Stream B :=
match Out sp with
| PutX b sp' => Cons b (toStream sp' s)
| GetX sp'   => toStream (MkSP (sp' (hd s))) (tl s)
end.

Fail Fixpoint SPX_to_Stream {X A B : Type} (sp : SPX X A B) (s : Stream A) : Stream B :=
match sp with
| PutX b sp' => Cons b (SPX_to_Stream sp')
| GetX sp'   => SPX_to_Stream (sp' (hd s)) (tl s)
end.

(** The first, naive way of doing it. *)

Fixpoint head {X A B : Type} (sp : SPX X A B) (s : Stream A) : B :=
match sp with
| PutX h _ => h
| GetX sp' => head (sp' (hd s)) (tl s)
end.

Fixpoint tail {X A B : Type} (sp : SPX X A B) (s : Stream A) : X * Stream A :=
match sp with
| PutX _ t => (t, s)
| GetX sp' => tail (sp' (hd s)) (tl s)
end.

CoFixpoint toStream {A B : Type} (sp : SP A B) (s : Stream A) : Stream B :=
match Out sp with
| PutX h t => Cons h (toStream t s)
| GetX sp' =>
    let (sp'', s') := tail (sp' (hd s)) (tl s) in
      Cons (head (sp' (hd s)) (tl s)) (toStream sp'' s')
end.

CoFixpoint toStream1 {A B : Type} (sp : SP A B) (s : Stream A) : Stream B :=
  Cons (head (Out sp) s) (let '(sp', s') := tail (Out sp) s in toStream1 sp' s').

(** A better way. *)

Fixpoint aux {X A B : Type} (sp : SPX X A B) (s : Stream A) : B * (X * Stream A) :=
match sp with
| PutX h t => (h, (t, s))
| GetX sp' => aux (sp' (hd s)) (tl s)
end.

CoFixpoint toStream' {A B : Type} (sp : SP A B) (s : Stream A) : Stream B :=
  let '(b, (sp', s')) := aux (Out sp) s in
    Cons b (toStream' sp' s').

(** Lighter syntax. *)

CoFixpoint toStream'' {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
match Out f with
| PutX h t => scons h (toStream'' t s)
| GetX g   =>
  let '(h, (f', s')) := aux (g (hd s)) (tl s) in
    scons h (toStream'' f' s')
end.

(** Some proofs. *)

Lemma head_aux :
  forall {X A B : Type} (sp : SPX X A B) (s : Stream A),
    head sp s = fst (aux sp s).
Proof.
  fix IH 4.
  intros X A B [h t | g'] s; cbn; [easy |].
  now apply IH.
Qed.

Lemma tail_aux :
  forall {X A B : Type} (sp : SPX X A B) (s : Stream A),
    tail sp s = snd (aux sp s).
Proof.
  fix IH 4.
  intros X A B [h t | g'] s; cbn; [easy |].
  now apply IH.
Qed.

Lemma hd_toStream :
  forall {A B : Type} (sp : SP A B) (s : Stream A),
    hd (toStream sp s) = head (Out sp) s.
Proof.
  intros A B sp; cbn.
  destruct (Out sp) as [h t | sp'] eqn: Heq; cbn; intros; [easy |].
  now destruct (tail (sp' (hd s)) (tl s)) eqn: Heq'; cbn.
Qed.

Lemma hd_toStream' :
  forall {A B : Type} (sp : SP A B) (s : Stream A),
    hd (toStream' sp s) = head (Out sp) s.
Proof.
  intros A B sp; cbn.
  induction (Out sp) as [h sp' | sp']; cbn; intros; [easy |].
  now rewrite H.
Qed.

Lemma tl_toStream :
  forall {A B : Type} (sp : SP A B) (s : Stream A),
    tl (toStream sp s) =
    let '(sp', s') := tail (Out sp) s in toStream sp' s'.
Proof.
  intros A B sp; cbn.
  destruct (Out sp) as [h sp' | sp']; cbn; intros; [easy |].
  now destruct (tail (sp' (hd s)) (tl s)); cbn.
Qed.

Lemma tl_toStream' :
  forall {A B : Type} (sp : SP A B) (s : Stream A),
    tl (toStream' sp s) =
    let '(sp', s') := tail (Out sp) s in toStream' sp' s'.
Proof.
  intros A B sp; cbn.
  induction (Out sp) as [h sp' | sp']; cbn; intros; [easy |].
  now rewrite H.
Qed.

Lemma toStream_toStream' :
  forall {A B : Type} (sp : SP A B) (s : Stream A),
    sim (toStream sp s) (toStream' sp s).
Proof.
  cofix CH.
  constructor.
  - now rewrite hd_toStream, hd_toStream'.
  - rewrite tl_toStream, tl_toStream'.
    destruct (tail (Out sp) s).
    now apply CH.
Qed.

Lemma toStream_toStream1 :
  forall {A B : Type} (sp : SP A B) (s : Stream A),
    sim (toStream sp s) (toStream1 sp s).
Proof.
  cofix CH.
  constructor.
  - now rewrite hd_toStream; cbn.
  - rewrite tl_toStream; cbn.
    destruct (tail (Out sp) s).
    now apply CH.
Qed.

(** Composition of stream processors. *)

(*
Fixpoint compSP {A B C : Type} (sp1 : SP A B) (sp2 : SP B C) : SP A C :=
match Out sp2 with
| PutX c sp2' => Put c (compSP sp1 sp2') (* corec *)
| GetX sp2'   =>
  match Out sp1 with
  | PutX b sp1' => compSP sp1' (MkSP (sp2' b)) (* rec on sp2 *)
  | GetX sp1'   => Get (fun a => Out (compSP (MkSP (sp1' a)) sp2)) (* rec on sp1 *)
  end
end.
*)

(*
Definition compSP {A B C : Type} (sp1 : SP A B) (sp2 : SP B C) : SP A C :=
  (cofix compSP_corec (sp1 : SP A B) (sp2 : SP B C) : SP A C :=
    (fix compSP_rec_2 (sp1 : SP A B) (sp2_2 : SPX (SP B C) B C) : SP A C :=
      match sp2_2 with
      | PutX c sp2' => Put c (compSP_corec sp1 sp2')
      | GetX sp2'   =>
        (fix compSP_rec_1 (sp1 : SPX (SP A B) A B) (sp2 : SP B C) : SP A C :=
          match sp1 with
          | PutX b sp1' => compSP_rec_2 sp1' (sp2' b)
          | GetX sp1'   => Get (fun a => Out (compSP_rec_1  (sp1' a) sp2))
          end
        ) (Out sp1) sp2
      end
    ) sp1 (Out sp2)
  ) sp1 sp2.
*)

CoFixpoint compSP {A B C : Type} (sp1 : SP A B) (sp2 : SP B C) : SP A C.
Proof.
  constructor.
  destruct (Out sp2) as [c sp2' | sp2'] eqn: Hsp2; intros.
  - apply (PutX c).
    apply (compSP _ _ _ sp1 sp2').
  - induction (Out sp1) as [b sp1' | sp1'] eqn: Hsp1.
    + admit.
    + apply GetX; intros a.
(*       Check compSP _ _ _ (tail (sp1' a)) (sp2' (head (sp1' a))). *)
Abort.

(*
Definition head_compSP {X A B C : Type} (sp1 : SPX X A B) (sp2 : SPX X B C) : C :=
match sp2 with
| PutX c _  => c
| GetX sp2' =>
  match sp1 with
  | PutX b sp1' => head_compSP sp1' (sp2' b) a
  | GetX sp1'   => 
*)

CoFixpoint compSP {A B C : Type} (sp1 : SP A B) (sp2 : SP B C) : SP A C.
Proof.
  refine (
    (fix aux (sp2 : SPX (SP B C) B C) : SP A C :=
      match sp2 with
      | PutX c sp2' => _
      | GetX sp2'   => _
      end
    )
    (Out sp2)
  ).
  - constructor.
    apply (PutX c).
    admit. (* apply (compSP _ _ _ sp1 sp2'). *)
  - destruct (Out sp1) as [b sp1' | sp1'].
    + apply aux. apply sp2'. exact b.
    + constructor.
      apply GetX; intros a.
Abort.

(*
Fixpoint whnf {A B : Type} (sp1 : SP A B) (sp2 : SPX X B C) : C * (SP A B * SP B C) :=
match sp2 with
| PutX h t  => (h, (t, sp2))
| GetX sp2' => whnf (tail sp1) (sp2' (head sp1))
end.
*)

Definition compSP {A B C : Type} (sp1 : SP A B) (sp2 : SP B C) : SP A C.
Proof.
  destruct sp1 as [sp1], sp2 as [sp2].
  constructor.
  induction sp2 as [c sp2' | sp2' IH].
  - admit.
  - apply GetX; intros a.
    apply IH.
Abort.

End StreamProcessor_v2.

(** * Definiowanie dziwnych funkcji (TODO) *)

(** ** Podejście pierwsze *)

Module ZipWith_v1.

Unset Guard Checking.
CoFixpoint fib : Stream nat := scons 0 (zipWith plus fib (scons 1 fib)).
Set Guard Checking.

Inductive TXY (X Y A : Type) : Type :=
| ConsXY    : A -> X -> TXY X Y A
| ZipWithXY : (A -> A -> A) -> Y -> Y -> TXY X Y A.
(* | YXY       : Y -> TXY X Y A. *)

Arguments ConsXY    {X Y A} _ _.
Arguments ZipWithXY {X Y A} _ _ _.
(* Arguments YXY       {X Y A} _. *)

Inductive SX (X A : Type) : Type :=
| SConsX    : A -> X -> SX X A
| SZipWithX : (A -> A -> A) -> SX X A -> SX X A -> SX X A.

Arguments SConsX    {X A} _ _.
Arguments SZipWithX {X A} _ _ _.

CoInductive StreamZipWith (A : Type) : Type :=
{
  Out : TXY (StreamZipWith A) (SX (StreamZipWith A) A) A;
}.

Arguments Out {A} _.

Definition ZipWith (A : Type) : Type := SX (StreamZipWith A) A.

Definition StreamZipWith_to_ZipWith {A : Type} (s : StreamZipWith A) : ZipWith A :=
match Out s with
| ConsXY h t      => SConsX h t
| ZipWithXY f l r => SZipWithX f l r
(* | YXY s'          => s' *)
end.

Definition Cons {A : Type} (h : A) (t : StreamZipWith A) : StreamZipWith A :=
{|
  Out := ConsXY h t;
|}.

Definition ZipWith' {A : Type} (f : A -> A -> A) (l r : StreamZipWith A) : StreamZipWith A :=
{|
  Out := ZipWithXY f (StreamZipWith_to_ZipWith l) (StreamZipWith_to_ZipWith r);
|}.

Fixpoint whnf {A : Type} (z : ZipWith A) : A * StreamZipWith A :=
match z with
| SConsX h t      => (h, t)
| SZipWithX f l r =>
  let '(h1, t1) := whnf l in
  let '(h2, t2) := whnf r in
    (f h1 h2, ZipWith' f t1 t2)
end.

CoFixpoint toStream {A : Type} (z : StreamZipWith A) : Stream A :=
match Out z with
| ConsXY h t      => scons h (toStream t)
| ZipWithXY f l r =>
  let (h1, t1) := whnf l in
  let (h2, t2) := whnf r in
    scons (f h1 h2) (toStream (ZipWith' f t1 t2))
(* | YXY s' => *)
(*         let (h, t) := whnf s' in scons h (toStream t) *)
end.

CoFixpoint fibSZW : StreamZipWith nat.
Proof.
  apply (Cons 0).
  refine {| Out := ZipWithXY plus _ _ |}.
    exact (StreamZipWith_to_ZipWith fibSZW).
    exact (SConsX 1 fibSZW).
Abort.

(* Compute take 5 (toStream fibSZW). *)

End ZipWith_v1.

(** ** Podejście drugie *)

Module ZipWith_v2.

Unset Guard Checking.
(* CoFixpoint fib : Stream nat := scons 0 (zipWith plus fib (scons 1 fib)). *)
(* CoFixpoint fib : Stream nat := scons 0 (scons 1 (zipWith plus fib (tl fib))). *)
(* Compute take 3 fib. *)
Set Guard Checking.

Inductive CI : Type := Ind | Coind.

Inductive Base (C A : Type) : CI -> Type :=
| BCons    : forall {ci : CI}, A -> C -> Base C A ci
| BZipWith : forall {ci : CI}, (A -> A -> A) -> Base C A Ind -> Base C A Ind -> Base C A ci
| BInj     : C -> Base C A Ind.

Arguments BCons    {C A ci} _ _.
Arguments BZipWith {C A ci} _ _ _.
Arguments BInj     {C A} _.

CoInductive ZipWith (A : Type) : Type :=
{
  Out : Base (ZipWith A) A Coind;
}.

Arguments Out {A} _.

Definition Cons {A : Type} (h : A) (t : ZipWith A) : ZipWith A :=
{|
  Out := BCons h t;
|}.

Definition ZipWith' {A : Type} (f : A -> A -> A) (l r : ZipWith A) : ZipWith A :=
{|
  Out := BZipWith f (BInj l) (BInj r);
|}.

CoFixpoint fib' : ZipWith nat.
Proof.
  apply (Cons 0).
  refine (ZipWith' plus _ _).
    exact fib'.
    apply (Cons 1). exact fib'.
Defined.

(*
Fixpoint whnf {A : Type} (z : ZipWith A) : A * ZipWith A :=
match z with
| SConsX h t      => (h, t)
| SZipWithX f l r =>
  let '(h1, t1) := whnf l in
  let '(h2, t2) := whnf r in
    (f h1 h2, ZipWith' f t1 t2)
| Inj s           => whnf s
end.

CoFixpoint toStream {A : Type} (z : ZipWith A) : Stream A :=
match Out z with
| ConsXY h t      => scons h (toStream t)
| ZipWithXY f l r =>
  let (h1, t1) := whnf l in
  let (h2, t2) := whnf r in
    scons (f h1 h2) (toStream (ZipWith' f t1 t2))
(* | YXY s' => *)
(*         let (h, t) := whnf s' in scons h (toStream t) *)
end.

CoFixpoint fibSZW : ZipWith nat.
Proof.
  apply (Cons 0).
  refine {| Out := ZipWithXY plus _ _ |}.
    exact (ZipWith_to_ZipWith fibSZW).
    exact (SConsX 1 fibSZW).
Defined.

Compute take 5 (toStream fibSZW).
*)

End ZipWith_v2.