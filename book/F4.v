(** * F4: Kolisty [TODO] *)

(** * Kolisty nie znaczy okrągły *)

Require Import D5.

(** Ten rozdział będzie o kolistach, czyli koinduktywnych odpowiednikach
    list różniących się od nich tym, że mogą być potencjalnie
    nieskończone. *)

CoInductive coList (A : Type) : Type :=
{
    uncons : option (A * coList A);
}.

Arguments uncons {A}.

(** Przydatny będzie następujący, dość oczywisty fakt dotyczący równości
    kolist. *)

Lemma eq_uncons :
  forall (A : Type) (l1 l2 : coList A),
    uncons l1 = uncons l2 -> l1 = l2.
(* begin hide *)
Proof.
  destruct l1, l2. cbn. intro. rewrite H. reflexivity.
Qed.
(* end hide *)

(** ** Bipodobieństwo *)

(** Zdefiniuj relację bipodobieństwa dla kolist. Udowodnij, że jest ona
    relacją równoważności. Z powodu konfliktu nazw bipodobieństwo póki
    co nazywać się będzie [lsim]. *)

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

(** Przyda się też instancja klasy [Equivalence], żebyśmy przy dowodzeniu
    o [lsim] mogli używać taktyk [reflexivity], [symmetry] oraz [rewrite]. *)

Instance Equivalence_lsim (A : Type) : Equivalence (@lsim A).
Proof.
  esplit; red.
    apply lsim_refl.
    apply lsim_symm.
    apply lsim_trans.
Defined.

(** ** Różność *)

(** Przyda się też induktywna wersja relacji [<>]. Zdefiniuj ją i pokaż,
    że induktywna wersja implikuje zwykłą. Czy implikacja w drugą stronę
    zachodzi? *)

Inductive coList_neq
  {A : Type} : coList A -> coList A -> Prop :=
    | coList_neq_nc :
        forall l1 l2 : coList A,
          uncons l1 = None -> uncons l2 <> None -> coList_neq l1 l2
    | coList_neq_cn :
        forall l1 l2 : coList A,
          uncons l1 <> None -> uncons l2 = None -> coList_neq l1 l2
    | coList_neq_cc_here :
        forall (h1 h2 : A) (t1 t2 l1 l2 : coList A),
          uncons l1 = Some (h1, t1) ->
          uncons l2 = Some (h2, t2) ->
            h1 <> h2 -> coList_neq l1 l2
    | coList_neq_cc_there :
        forall (h1 h2 : A) (t1 t2 l1 l2 : coList A),
          uncons l1 = Some (h1, t1) ->
          uncons l2 = Some (h2, t2) ->
            coList_neq t1 t2 -> coList_neq l1 l2.

Lemma coList_neq_not_lsim :
  forall {A : Type} {l1 l2 : coList A},
    coList_neq l1 l2 -> ~ lsim l1 l2.
(* begin hide *)
Proof.
  induction 1;
  intros []; decompose [ex or and] lsim'0; clear lsim'0;
  congruence.
Qed.
(* end hide *)

Lemma nlsim_neq :
  forall {A : Type} {l1 l2 : coList A},
    ~ lsim l1 l2 -> l1 <> l2.
(* begin hide *)
Proof.
  intros A l1 l2 Hsim Heq.
  subst.
  apply Hsim, lsim_refl.
Qed.
(* end hide *)

Lemma coList_neq_antirefl :
  forall {A : Type} (l : coList A),
    ~ coList_neq l l.
(* begin hide *)
Proof.
  intros A l H.
  apply coList_neq_not_lsim, nlsim_neq in H.
  contradiction.
Qed.
(* end hide *)

Hint Constructors coList_neq : core.

Lemma coList_neq_sym :
  forall {A : Type} {l1 l2 : coList A},
    coList_neq l1 l2 -> coList_neq l2 l1.
(* begin hide *)
Proof.
  induction 1; eauto.
Qed.
(* end hide *)

(** ** [conil] i [cocons] *)

(** Zdefiniuj [conil], czyli kolistę pustą, oraz [cocons], czyli funkcję,
    która dokleja do kolisty nową głowę. Udowodnij, że [cocons] zachowuje
    i odbija bipodobieństwo. *)

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

Lemma lsim_cocons :
  forall (A : Type) (x y : A) (l1 l2 : coList A),
    x = y -> lsim l1 l2 -> lsim (cocons x l1) (cocons y l2).
(* begin hide *)
Proof.
  constructor. cbn. right. do 4 eexists. eauto.
Qed.
(* end hide *)

Lemma lsim_cocons_inv :
  forall (A : Type) (x y : A) (l1 l2 : coList A),
    lsim (cocons x l1) (cocons y l2) -> x = y /\ lsim l1 l2.
(* begin hide *)
Proof.
  intros. destruct H; decompose [or ex and] lsim'0; clear lsim'0; cbn in *.
    inv H0.
    inv H0. inv H. auto.
Qed.
(* end hide *)

(** ** [len] *)

(** Przygodę z funkcjami na kolistach zaczniemy od długości. Tak jak zwykła,
    induktywna lista ma długość wyrażającą się liczbą naturalną, tak też i
    długość kolisty można wyrazić za pomocą liczby konaturalnej.

    Napisz funkcję [len], która oblicza długość kolisty. Pokaż, że
    bipodobne kolisty mają tę samą długość. Długość kolisty pustej
    oraz [cocons]a powinny być oczywiste. *)

Require Import F2.

(* begin hide *)
CoFixpoint len {A : Type} (l : coList A) : conat :=
{|
    pred :=
      match uncons l with
          | None => None
          | Some (_, t) => Some (len t)
      end;
|}.
(* end hide *)

Lemma sim_len :
  forall (A : Type) (l1 l2 : coList A),
    lsim l1 l2 -> sim (len l1) (len l2).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct H as [[[H1 H2] | (h1 & t1 & h2 & t2 & H1 & H2 & H3 & H4)]];
  cbn in *.
    rewrite H1, H2. left. split; reflexivity.
    rewrite H1, H2. right. exists (len t1), (len t2). intuition.
Qed.
(* end hide *)

Lemma len_conil :
  forall A : Type,
    len (@conil A) = zero.
(* begin hide *)
Proof.
  intros. apply eq_pred. cbn. reflexivity.
Qed.
(* end hide *)

Lemma len_cocons :
  forall (A : Type) (x : A) (l : coList A),
    len (cocons x l) = succ (len l).
(* begin hide *)
Proof.
  intros. apply eq_pred. cbn. reflexivity.
Qed.
(* end hide *)

(** ** [snoc] *)

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

Lemma snoc_cocons :
  forall (A : Type) (l : coList A) (x y : A),
    lsim (snoc (cocons x l) y) (cocons x (snoc l y)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. right. do 4 eexists. intuition.
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
    do 2 eexists. intuition. constructor; eauto.
Qed.
(* end hide *)

(** ** [app] *)

(** Zdefiniuj funkcję [app], która skleja dwie kolisty. Czy jest to w ogóle
    możliwe? Czy taka funkcja ma sens? Porównaj z przypadkiem sklejania
    strumieni. *)

(* begin hide *)
CoFixpoint app {A : Type} (l1 l2 : coList A) : coList A :=
{|
    uncons :=
      match uncons l1 with
          | None => uncons l2
          | Some (h, t) => Some (h, app t l2)
      end
|}.
(* end hide *)

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

Lemma app_cocons_l :
  forall (A : Type) (x : A) (l1 l2 : coList A),
    lsim (app (cocons x l1) l2) (cocons x (app l1 l2)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. cbn. right. do 4 eexists. intuition.
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
      right. do 4 eexists. intuition.
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

Lemma app_assoc :
  forall (A : Type) (l1 l2 l3 : coList A),
    lsim (app (app l1 l2) l3) (app l1 (app l2 l3)).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l1 as [[[h1 t1] |]]; cbn.
    right. do 4 eexists. intuition.
    destruct l2 as [[[h2 t2] |]]; cbn.
      right. do 4 eexists. intuition.
      destruct l3 as [[[h3 t3] |]]; cbn.
        right. do 4 eexists. intuition.
        left. split; reflexivity.
Qed.
(* end hide *)

(** ** [lmap] *)

(** Zdefiniuj funkcję [lmap], która aplikuje funkcję [f : A -> B] do
    każdego elementu kolisty.

    TODO: wyklarować, dlaczego niektóre rzeczy mają "l" na początku nazwy *)

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
  constructor. right.
  exists (f x), (lmap f l), (f x), (lmap f l).
  cbn. intuition.
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
      left. split; reflexivity.
Qed.
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

Lemma lmap_comp :
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

(** ** [iterate] *)

(** Zdefiniuj funkcję [iterate], która tworzy nieskończoną kolistę przez
    iterowanie funkcji [f] poczynając od pewnego ustalonego elementu. *)

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

(** ** [piterate] *)

(** Zdefiniuj funkcję [piterate], która tworzy kolistę przez iterowanie
    funkcji częściowej [f : A -> option B] poczynając od pewnego ustalonego
    elementu. *)

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

(** ** [zipW] *)

(** Zdefiniuj funkcję [zipW], która bierze funkcję [f : A -> B -> C] oraz
    dwie kolisty [l1] i [l2] i zwraca kolistę, której elementy powstają z
    połączenia odpowiadających sobie elementów [l1] i [l2] za pomocą funkcji
    [f]. *)

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

Lemma zipW_conil_l :
  forall (A B C : Type) (f : A -> B -> C) (l : coList B),
    lsim (zipW f conil l) conil.
(* begin hide *)
Proof.
  constructor. cbn. left. split; reflexivity.
Qed.
(* end hide *)

Lemma zipW_conil_r :
  forall (A B C : Type) (f : A -> B -> C) (l1 : coList A) (l2 : coList B),
    sim (len (zipW f l1 l2)) (min (len l1) (len l2)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct l1 as [[[h1 t1] |]],
           l2 as [[[h2 t2] |]];
  cbn.
    right. exists (len (zipW f t1 t2)), (min (len t1) (len t2)). eauto.
    1-3: left; split; reflexivity.
Qed.
(* end hide *)

Lemma len_zipW :
  forall (A B C : Type) (f : A -> B -> C) (l1 : coList A) (l2 : coList B),
    sim (len (zipW f l1 l2)) (min (len l1) (len l2)).
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct l1 as [[[h1 t1] |]],
           l2 as [[[h2 t2] |]];
  cbn.
    right. exists (len (zipW f t1 t2)), (min (len t1) (len t2)). eauto.
    1-3: left; split; reflexivity.
Qed.
(* end hide *)

(** ** [scan] *)

(** Napisz funkcję [scan], która przekształca [l : coList A] w kolistę
    sum częściowych działania [f : B -> A -> B]. *)

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

Lemma scan_conil :
  forall (A B : Type) (f : B -> A -> B) (b : B),
    lsim (scan conil f b) conil.
(* begin hide *)
Proof.
  constructor. cbn. left. split; reflexivity.
Qed.
(* end hide *)

Lemma scan_cocons :
  forall (A B : Type) (x : A) (l : coList A) (f : B -> A -> B) (b : B),
    lsim (scan (cocons x l) f b) (cocons b (scan l f (f b x))).
(* begin hide *)
Proof.
  constructor. cbn. right. do 4 eexists.
  repeat (reflexivity || split).
Qed.
(* end hide *)

Lemma len_scan :
  forall (A B : Type) (l : coList A) (f : B -> A -> B) (b : B),
    sim (len (scan l f b)) (len l).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l as [[[h t] |]]; cbn.
    right. do 2 eexists. eauto.
    left. split; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(** TODO: kolistowy [scan] vs snoc, app, map, iterate, piterate. *)
(* end hide *)

(** ** [intersperse] *)

(** Napisz funkcję [intersperse], która działa analogicznie jak dla list. *)

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

Lemma intersperse_conil :
  forall (A : Type) (x : A),
    lsim (intersperse x conil) conil.
(* begin hide *)
Proof.
  constructor. cbn. left. split; reflexivity.
Qed.
(* end hide *)

(** Pułapka: czy poniższe twierdzenie jest prawdziwe? *)

Lemma add_succ :
  forall n m : conat,
    sim (add (succ n) m) (succ (add n m)).
Proof.
  constructor. cbn.
  right. do 2 eexists. intuition.
Qed.

Lemma len_intersperse :
  forall (A : Type) (x : A) (l : coList A),
    sim (len (intersperse x l)) (succ (add (len l) (len l))).
(* begin hide *)
Proof.
  cofix CH.
  constructor. destruct l as [[[h1 [[[h2 t] |]]] |]]; cbn.
    right. do 2 eexists. intuition. rewrite len_cocons.
      replace ({| uncons := Some (h1, _) |}) with (cocons h1 (cocons h2 t)).
        rewrite !len_cocons. rewrite add_succ. apply sim_succ.
Abort.
(* end hide *)

(** ** [splitAt] *)

(** Napisz rekurencyjną funkcję [splitAt]. [splitAt l n] zwraca
    [Some (begin, x, rest)], gdzie [begin] jest listą reprezentującą
    początkowy fragment kolisty [l] o długości [n], [x] to element
    [l] znajdujący się na pozycji [n], zaś [rest] to kolista będącą
    tym, co z kolisty [l] pozostanie po zabraniu z niej [l] oraz [x].
    Jeżeli [l] nie ma fragmentu początkowego o długości [n], funkcja
    [splitAt] zwraca [None]. *)

(* begin hide *)
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
(* end hide *)

(** Funkcji [splitAt] można użyć do zdefiniowania całej gamy funkcji
    działających na kolistach - rozbierających ją na kawałki, wstawiających,
    zamieniających i usuwających elementy, etc. *)

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

(** ** [Finite] i [Infinite] *)

(** Zdefiniuj predykaty [Finite] oraz [Infinite], które są spełnione,
    odpowiednio, przez skończone i nieskończone kolisty. Zastanów się
    dobrze, czy definicje powinny być induktywne, czy koinduktywne.

    Udowodnij, że niezaprzeczalnie każda kolista jest skończona lub
    nieskończona oraz że żadna kolista nie jest jednocześnia skończona
    i nieskończona.

    Następnie udowodnij własności tych predykatów oraz sprawdź, które
    kolisty i operacje je spełniają. *)

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

Lemma Finite_or_Infinite_irrefutable :
  forall {A : Type} (l : coList A),
    ~ ~ (Finite l \/ Infinite l).
(* begin hide *)
Proof.
  intros A l H.
  apply H. right. revert A l H. cofix CH.
  intros A l H.
  destruct l as [[[h t] |]].
    Focus 2. contradiction H. left. constructor. cbn. reflexivity.
    econstructor.
      cbn. reflexivity.
      apply CH. intros [H' | H']; apply H.
        left. econstructor 2.
          cbn. reflexivity.
          assumption.
        right. econstructor.
          cbn. reflexivity.
          assumption.
Qed.
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

Lemma len_Infinite_conv :
  forall (A : Type) (l : coList A),
    Infinite l -> sim (len l) omega.
(* begin hide *)
Proof.
  cofix CH.
  constructor.
  destruct l as [[[h t] |]]; cbn in *.
    right. exists (len t), omega. do 2 split.
      reflexivity.
      apply CH. inv H. cbn in *. inv p.
    inv H. inv p.
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

Lemma Infinite_app :
  forall (A : Type) (l1 l2 : coList A),
    Infinite l1 \/ Infinite l2 -> Infinite (app l1 l2).
(* begin hide *)
Proof.
  destruct 1.
    apply Infinite_app_l. assumption.
    apply Infinite_app_r. assumption.
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

Hint Constructors Finite.

Lemma Finite_app_conv :
  forall (A : Type) (l1 l2 : coList A),
    Finite (app l1 l2) -> Finite l1 /\ Finite l2.
(* begin hide *)
Proof.
  intros. remember (app l1 l2) as l. revert l1 l2 Heql.
  induction H; intros; subst; cbn in *.
    destruct l1 as [[[h t]|]]; cbn in H.
      inversion H.
      auto.
    destruct l1 as [[[h' t']|]]; cbn in H.
      inversion H; subst. destruct (IHFinite _ _ eq_refl).
        split.
          econstructor 2; cbn; eauto.
          assumption.
      split.
        auto.
        econstructor 2; eauto.
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

(** ** [Exists] i [Forall] *)

(** Zdefiniuj predykaty [Exists P] oraz [Forall P], które są spełnione
    przez kolisty, których odpowiednio jakiś/wszystkie elementy spełniają
    predykat [P]. Zastanów się dobrze, czy definicje powinny być induktywne,
    czy koinduktywne.

    Sprawdź, które z praw de Morgana zachodzą. *)

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

Lemma Exists_not_All :
  forall (A : Type) (P : A -> Prop) (l : coList A),
    Exists P l -> ~ All (fun x : A => ~ P x) l.
(* begin hide *)
Proof.
  induction 1; destruct 1 as [[H' | (h' & t' & H1' & H2' & H3')]];
  congruence.
Qed.
(* end hide *)

Lemma All_Exists :
  forall (A : Type) (P : A -> Prop) (l : coList A),
    All P l -> l = conil \/ Exists P l.
(* begin hide *)
Proof.
  intros. destruct H as [[H | (h & t & H1 & H2 & H3)]].
    left. destruct l as [[]].
      inv H.
      reflexivity.
    right. destruct l as [[]]; inv H1. econstructor.
      cbn. reflexivity.
      assumption.
Qed.
(* end hide *)