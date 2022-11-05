(** * D6: Więcej list [TODO] *)

(* begin hide *)
(*
TODO 1: przenieś [intersperse] na sam koniec funkcji i dorzuć jeszcze
TODO 1: kilka dziwnych (z niestandardowym kształtem indukcji)
TODO 2: opisz niestandardowe reguły indukcyjne dla list (najlepiej przed
TODO 2: funkcją [intersperse])
TODO 3: opisz foldy ([fold] i [foldl]), łączac je z regułami indukcji
TODO 4: opisz sumy prefiksowe (`scanr` i `scanl`)
TODO 5: zrób osobno: funkcje na listach dla typów mających jakieś
TODO 6: specjalne rzeczy (np. rozstrzygalną równość)
TODO 7: ćwiczenia z przetwarzania danych, typu znajdź wszystkie liczby
TODO 7: nieparzyste większe od x, których suma cyfr to dupa konia.
TODO 8: niektóre niedokończone funkcje dla list:
  - isZero (przenieść do rozdziału o arytmetyce)
  - isEmpty
  - snoc
  - bind
  - iterate (od removeFirst wzwyż) i iter (join, bind)
  - insert (join, bind, iterate, init)
  - remove
  - take (join, bind, last_take, take_remove),
  - drop (join, bind, remove)
  - removeFirst (removeFirst_zip)
  - findIndex (init, tail)
  - filter (tail, init)
  - findIndices (join, bind, takeWhile, dropWhile)
  - pmap (iterate, nth, last, tail i init, take i drop, takedrop, zip,
    unzip, zipWith, unzipWith, removeFirst i removeLast, findIndex,
    findIndices)
  - intersperse (init, insert, remove, drop, zip, zipWith, unzip)
  - groupBy
  - Rep (join, nth)
  - AtLeast (nth, head, last, init, tail)
  - Exactly (join, nth, head, tail, init, last, zip)
  - AtMost
  - popracować nad `findIndices` (i to w dwóch wersjach - być może jest to
    dobry pretekst dla wprowadzenia stylu programowania z akumulatorem?)
TODO 9: Dokończyć prace nad resztą rzeczy z folderu List/.
TODO 10: opisać encode-decode dla (nie)równości na typach induktywnych.
TODO 11: poszukać ogólnego pojęcia "różnicy" typów.
*)
(* end hide *)

From Typonomikon Require Import D5.

(** * [revapp] *)

Fixpoint revapp {A : Type} (l1 l2 : list A) : list A :=
match l1 with
| [] => l2
| h :: t => revapp t (h :: l2)
end.

Definition app' {A : Type} (l1 l2 : list A) : list A :=
  revapp (revapp l1 []) l2.

Lemma revapp_spec :
  forall (A : Type) (l1 l2 : list A),
    revapp l1 l2 = rev l1 ++ l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros; trivial.
    rewrite IHt, app_snoc_l. reflexivity.
Qed.
(* end hide *)

Lemma app'_spec :
  forall (A : Type) (l1 l2 : list A),
    app' l1 l2 = l1 ++ l2.
(* begin hide *)
Proof.
  unfold app'. intros. rewrite !revapp_spec, app_nil_r, rev_rev. trivial.
Qed.
(* end hide *)

Definition rev' {A : Type} (l : list A) : list A :=
  revapp l [].

Lemma rev'_spec :
  forall {A : Type} (l : list A),
    rev' l = rev l.
(* begin hide *)
Proof.
  intros. unfold rev'.
  rewrite revapp_spec.
  apply app_nil_r.
Qed.
(* end hide *)

(** * [foldr] i [foldl], czyli standardowe reguły indukcji *)

Fixpoint foldr
  {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : B :=
match l with
| [] => b
| h :: t => f h (foldr f b t)
end.

Fixpoint foldl
  {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : A :=
match l with
| [] => a
| h :: t => foldl f (f a h) t
end.

(** Nie będę na razie tłumaczył, jaka ideologia stoi za [foldr] i [foldl].
    Napiszę o tym później, a na razie porcja zadań.

    Zaimplementuj za pomocą [foldr] i [foldl] następujące funkcje:
    [length], [app], [rev], [map], [join], [filter], [takeWhile],
    [dropWhile].

    Udowodnij, że zdefiniowane przez ciebie funkcje pokrywają się ze
    swoimi klasycznymi odpowiednikami. *)

(* begin hide *)
(* Reszta polecenia: [repeat], [nth], [take], [drop] *)

Functional Scheme foldr_ind := Induction for foldr Sort Prop.
Functional Scheme foldl_ind := Induction for foldl Sort Prop.

Definition lengthF {A : Type} (l : list A) : nat :=
  foldr (fun _ => S) 0 l.

Definition snocF {A : Type} (x : A) (l : list A) : list A :=
  foldr (@cons A) [x] l.

Definition appF {A : Type} (l1 l2 : list A) : list A :=
  foldr (@cons A) l2 l1.

Definition revF {A : Type} (l : list A) : list A :=
  foldr snoc [] l.

Definition revF' {A : Type} (l : list A) : list A :=
  foldl (fun t h => h :: t) [] l.

Definition mapF {A B : Type} (f : A -> B) (l : list A) : list B :=
  foldr (fun h t => f h :: t) [] l.

Definition joinF {A : Type} (l : list (list A)) : list A :=
  foldr app [] l.

Require Import Bool.

Definition allF {A : Type} (p : A -> bool) (l : list A) : bool :=
  foldr (fun h t => p h && t) true l.

Definition anyF {A : Type} (p : A -> bool) (l : list A) : bool :=
  foldr (fun h t => p h || t) false l.

Definition findF {A : Type} (p : A -> bool) (l : list A) : option A :=
  foldr (fun h t => if p h then Some h else t) None l.

Definition omap {A B : Type} (f : A -> B) (x : option A) : option B :=
match x with
| None   => None
| Some a => Some (f a)
end.

Definition findIndexF
  {A : Type} (p : A -> bool) (l : list A) : option nat :=
    foldr (fun h t => if p h then Some 0 else omap S t) None l.

Definition countF {A : Type} (p : A -> bool) (l : list A) : nat :=
  foldr (fun h t => (if p h then 1 else 0) + t) 0 l.

Definition filterF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then h :: t else t) [] l.

Definition takeWhileF {A : Type} (p : A -> bool) (l : list A) : list A :=
  foldr (fun h t => if p h then h :: t else []) [] l.

Ltac solve_fold := intros;
match goal with
| |- context [@foldr ?A ?B ?f ?a ?l] =>
  functional induction @foldr A B f a l; cbn; trivial;
  match goal with
  | H : ?x = _ |- context [?x] => rewrite ?H; auto
  end
| |- context [@foldl ?A ?B ?f ?a ?l] =>
  functional induction @foldl A B f a l; cbn; trivial;
  match goal with
  | H : ?x = _ |- context [?x] => rewrite ?H; auto
  end
end.

(* end hide *)

Lemma lengthF_spec :
  forall (A : Type) (l : list A),
    lengthF l = length l.
(* begin hide *)
Proof.
  unfold lengthF; induction l as [| h t]; cbn.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold lengthF. solve_fold.
Qed.
(* end hide *)

Lemma snocF_spec :
  forall (A : Type) (x : A) (l : list A),
    snocF x l = snoc x l.
(* begin hide *)
Proof.
  intros. unfold snocF. solve_fold.
Qed.
(* end hide *)

Lemma appF_spec :
  forall (A : Type) (l1 l2 : list A),
    appF l1 l2 = l1 ++ l2.
(* begin hide *)
Proof.
  unfold appF; induction l1 as [| h1 t1]; cbn; intros.
    trivial.
    rewrite IHt1. trivial.
Restart.
  intros. unfold appF. solve_fold.
Qed.
(* end hide *)

Lemma revF_spec :
  forall (A : Type) (l : list A),
    revF l = rev l.
(* begin hide *)
Proof.
  unfold revF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold revF. solve_fold.
Qed.
(* end hide *)

(* begin hide *)
Lemma revF'_spec :
  forall (A : Type) (l : list A),
    revF' l = rev l.
Proof.
  unfold revF'. intros. replace (rev l) with (rev l ++ []).
    remember [] as acc. clear Heqacc. generalize dependent acc.
      induction l as [| h t]; cbn; intros; subst.
        reflexivity.
        rewrite IHt, app_snoc_l. reflexivity.
    apply app_nil_r.
Qed.
(* end hide *)

Lemma mapF_spec :
  forall (A B : Type) (f : A -> B) (l : list A),
    mapF f l = map f l.
(* begin hide *)
Proof.
  unfold mapF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold mapF. solve_fold.
Qed.
(* end hide *)

Lemma joinF_spec :
  forall (A : Type) (l : list (list A)),
    joinF l = join l.
(* begin hide *)
Proof.
  unfold joinF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold joinF. solve_fold.
Qed.
(* end hide *)

Lemma allF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    allF p l = all p l.
(* begin hide *)
Proof.
  unfold allF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      assumption.
      reflexivity.
Qed.
(* end hide *)

Lemma anyF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    anyF p l = any p l.
(* begin hide *)
Proof.
  unfold anyF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma findF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    findF p l = find p l.
(* begin hide *)
Proof.
  unfold findF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma findIndexF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    findIndexF p l = findIndex p l.
(* begin hide *)
Proof.
  unfold findIndexF.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      reflexivity.
      rewrite IHt.
      destruct (findIndex p t); cbn; reflexivity.
Qed.
(* end hide *)

Lemma countF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    countF p l = count p l.
(* begin hide *)
Proof.
  unfold countF. induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn.
      rewrite IHt. reflexivity.
      assumption.
Qed.
(* end hide *)

Lemma filterF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    filterF p l = filter p l.
(* begin hide *)
Proof.
  unfold filterF; induction l as [| h t].
    cbn. trivial.
    cbn. rewrite IHt. trivial.
Restart.
  intros. unfold filterF. solve_fold.
Qed.
(* end hide *)

Lemma takeWhileF_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    takeWhileF p l = takeWhile p l.
(* begin hide *)
Proof.
  unfold takeWhileF; induction l as [| h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Restart.
  intros. unfold takeWhileF. solve_fold.
Qed.
(* end hide *)

(** ** Lematy o foldach *)

Lemma foldr_app :
  forall (A B : Type) (f : A -> B -> B) (b : B) (l1 l2 : list A),
    foldr f b (l1 ++ l2) = foldr f (foldr f b l2) l1.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Lemma foldr_rev :
  forall (A B : Type) (f : A -> B -> B) (l : list A) (b : B),
    foldr f b (rev l) = foldl (flip f) b l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite snoc_app_singl, foldr_app. cbn. rewrite IHt. unfold flip. reflexivity.
Qed.
(* end hide *)

Lemma foldl_app :
  forall (A B : Type) (f : A -> B -> A) (l1 l2 : list B) (a : A),
    foldl f a (l1 ++ l2) = foldl f (foldl f a l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma foldl_snoc :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A) (b : B),
    foldl f a (l ++ [b]) = f (foldl f a l) b.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma foldl_rev :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    foldl f a (rev l) = foldr (flip f) a l.
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l). rewrite foldr_rev.
  rewrite rev_rev. reflexivity.
Qed.
(* end hide *)

(** * Sumy kroczące *)

Fixpoint scanl
  {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : list A :=
    a ::
match l with
| [] => []
| h :: t => scanl f (f a h) t
end.

Compute scanl plus 0 [1; 2; 3; 4; 5].

Definition scanl1
  {A : Type} (f : A -> A -> A) (l : list A) : list A :=
match l with
| [] => []
| h :: t => scanl f h t
end.

Compute scanl1 plus [1; 2; 3; 4; 5].

Fixpoint scanr
  {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : list B :=
match l with
| [] => [b]
| h :: t =>
  let
    qs := scanr f b t
  in
  match qs with
  | [] => [f h b]
  | q :: _ => f h q :: qs
  end
end.

Compute scanr plus 0 [1; 2; 3; 4; 5].

Fixpoint scanr1
  {A : Type} (f : A -> A -> A) (l : list A) : list A :=
match l with
| [] => []
| [h] => [h]
| h :: t =>
  let
    qs := scanr1 f t
  in
  match qs with
  | [] => []
  | q :: _ => f h q :: qs
  end
end.

Compute scanr1 plus [1; 2; 3; 4; 5].

Lemma isEmpty_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    isEmpty (scanl f a l) = false.
(* begin hide *)
Proof.
  destruct l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    length (scanl f a l) = 1 + length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma scanl_app :
  forall (A B : Type) (f : A -> B -> A) (l1 l2 : list B) (a : A),
    scanl f a (l1 ++ l2) = 
    take (length l1) (scanl f a l1) ++ scanl f (foldl f a l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    f_equal. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma scanl_snoc :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A) (b : B),
    scanl f a (l ++ [b]) = scanl f a l ++ [foldl f a (l ++ [b])].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma head_scanr :
  forall (A B : Type) (f : A -> B -> B) (b : B) (l : list A),
    head (scanr f b l) =
      match l with
      | [] => Some b
      | _  => Some (foldl (flip f) b (rev l))
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (scanr f b t) eqn: Heq; cbn in *.
      destruct t; inv IHt.
      destruct t; inv IHt.
        inv Heq. cbn. reflexivity.
        cbn. rewrite !snoc_app_singl, !foldl_app. unfold flip; cbn. reflexivity.
Qed.
(* end hide *)

Lemma scanl_rev :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    scanl f a (rev l) = rev (scanr (flip f) a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite snoc_app_singl, scanl_snoc, IHt. destruct (scanr (flip f) a t) eqn: Heq.
      destruct t; cbn in Heq.
        inversion Heq.
        destruct (scanr (flip f) a t); inversion Heq.
      rewrite foldl_app. cbn. unfold flip. do 3 f_equal.
        apply (f_equal head) in Heq. rewrite head_scanr in Heq.
          destruct t; inv Heq.
            cbn. rewrite !snoc_app_singl. reflexivity.
            cbn. rewrite !snoc_app_singl, !foldl_app. unfold flip; cbn. reflexivity.
Qed.
(* end hide *)

Lemma head_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    head (scanl f a l) = Some a.
(* begin hide *)
Proof.
  destruct l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma last_scanl :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (a : A),
    last (scanl f a l) = Some (foldl f a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (scanl f (f a h) t) eqn: Heq.
      apply (f_equal isEmpty) in Heq. rewrite isEmpty_scanl in Heq.
        cbn in Heq. congruence.
      rewrite <- Heq, IHt. reflexivity.
Qed.
(* end hide *)

(** * Niestandardowe reguły indukcyjne (TODO) *)

Fixpoint list_ind_2
  {A : Type} (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (Hcons2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
  (l : list A) : P l :=
match l with
| [] => Hnil
| [x] => Hsingl x
| x :: y :: l' => Hcons2 x y l' (list_ind_2 P Hnil Hsingl Hcons2 l')
end.

Fixpoint rot2 {A : Type} (l : list A) : list A :=
match l with
| [] => []
| [x] => [x]
| x :: y :: t => y :: x :: rot2 t
end.

Lemma rot2_involution :
  forall (A : Type) (l : list A),
    rot2 (rot2 l) = l.
Proof.
  intro. apply list_ind_2; cbn; intros.
    1-2: reflexivity.
    rewrite H. reflexivity.
Qed.

Inductive Rot2 {A : Type} : list A -> list A -> Prop :=
| Rot2_nil : Rot2 [] []
| Rot2_singl : forall x : A, Rot2 [x] [x]
| Rot2_cons2 :
    forall (x y : A) (l l' : list A),
      Rot2 l l' -> Rot2 (x :: y :: l) (y :: x :: l').

Lemma Rot2_correct :
  forall (A : Type) (l : list A),
    Rot2 l (rot2 l).
Proof.
  intro. apply list_ind_2; cbn; constructor. assumption.
Qed.

Lemma Rot2_complete :
  forall (A : Type) (l l' : list A),
    Rot2 l l' -> rot2 l = l'.
Proof.
  induction 1; cbn.
    1-2: reflexivity.
    rewrite IHRot2. reflexivity.
Qed.

(** * Funkcje z niestandardowym schematem rekursji *)

(** ** [interleave] (TODO) *)

(** Zdefiniuj funkcję [interleave], która przeplata ze sobą dwie listy.
    Użyj komendy [Function], coby potem było ci łatwiej dowodzić.

    Przykład: *)

(** [interleave [0; 2; 4; 6; 8] [1; 3; 5]] = [0; 1; 2; 3; 4; 5; 6; 8] *)
(** [interleave [0; 2;] [1; 3; 5; 7; 9]] = [0; 1; 2; 3; 5; 7; 9] *)

(* begin hide *)
Function interleave {A : Type} (l1 l2 : list A) : list A :=
match l1, l2 with
| [], _ => l2
| _, [] => l1
| h1 :: t1, h2 :: t2 => h1 :: h2 :: interleave t1 t2
end.
(* end hide *)

Lemma interleave_nil_r :
  forall {A : Type} (l : list A),
    interleave l [] = l.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_interleave :
  forall {A : Type} (l1 l2 : list A),
    isEmpty (interleave l1 l2) = isEmpty l1 && isEmpty l2.
(* begin hide *)
Proof.
  destruct l1, l2; reflexivity.
Qed.
(* end hide *)

Lemma len_interleave :
  forall {A : Type} (l1 l2 : list A),
    length (interleave l1 l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite plus_0_r. reflexivity.
      rewrite IHt1, plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma map_interleave :
  forall {A B : Type} (f : A -> B) (l1 l2 : list A),
    map f (interleave l1 l2) = interleave (map f l1) (map f l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      reflexivity.
      rewrite IHt1. reflexivity.
Qed.
(* end hide *)

Lemma any_interleave :
  forall {A : Type} (p : A -> bool) (l1 l2 : list A),
    any p (interleave l1 l2) = any p l1 || any p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite orb_false_r. reflexivity.
      rewrite IHt1, <- !orb_assoc. f_equal.
        rewrite orb_assoc. rewrite (orb_comm (p h2)).
        rewrite !orb_assoc. reflexivity.
Qed.
(* end hide *)

Lemma all_interleave :
  forall {A : Type} (p : A -> bool) (l1 l2 : list A),
    all p (interleave l1 l2) = all p l1 && all p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite andb_true_r. reflexivity.
      rewrite IHt1, <- !andb_assoc. f_equal.
        rewrite andb_assoc. rewrite (andb_comm (p h2)).
        rewrite !andb_assoc. reflexivity.
Qed.
(* end hide *)

Lemma count_interleave :
  forall {A : Type} (p : A -> bool) (l1 l2 : list A),
    count p (interleave l1 l2) = count p l1 + count p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    destruct l2 as [| h2 t2]; cbn.
      rewrite plus_0_r. reflexivity.
      {
        rewrite IHt1.
        destruct (p h1) eqn: ph1, (p h2) eqn: ph2; cbn.
        all: try rewrite plus_n_Sm; reflexivity.
      }
Qed.
(* end hide *)

Lemma Exists_interleave :
  forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Exists P (interleave l1 l2) <->
    Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  split; revert l2.
    induction l1 as [| h1 t1]; cbn.
      right. assumption.
      destruct l2 as [| h2 t2]; cbn; intro.
        left. assumption.
        inv H.
          left. constructor. assumption.
          inv H1.
            right. constructor. assumption.
            destruct (IHt1 _ H0).
              left. right. assumption.
              right. right. assumption.
    induction l1 as [| h1 t1]; cbn.
      destruct 1.
        inv H.
        assumption.
      destruct l2 as [| h2 t2]; cbn; intros [].
        assumption.
        inv H.
        inv H.
          left. assumption.
          right. right. apply IHt1. left. assumption.
        inv H.
          right. left. assumption.
          right. right. apply IHt1. right. assumption.
Qed.
(* end hide *)

Lemma Forall_interleave :
  forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Forall P (interleave l1 l2) <->
    Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  split; revert l2.
    induction l1 as [| h1 t1]; cbn.
      split; [constructor | assumption].
      destruct l2 as [| h2 t2]; cbn; intro.
        split; [assumption | constructor].
        inv H. inv H3. destruct (IHt1 _ H4).
          split; constructor; assumption.
    induction l1 as [| h1 t1]; cbn; intros l2 [].
      assumption.
      destruct l2 as [| h2 t2].
        assumption.
        inv H; inv H0. repeat constructor.
          1-2: assumption.
          apply IHt1. split; assumption.
Qed.
(* end hide *)

Lemma elem_Exists :
  forall {A : Type} {x : A} {l : list A},
    elem x l <-> Exists (fun y => x = y) l.
Proof.
  split; induction 1; subst; constructor; auto; fail.
Qed.

Lemma Dup_interleave :
  forall {A : Type} (l1 l2 : list A),
    Dup (interleave l1 l2) <->
    Dup l1 \/ Dup l2 \/ exists x : A, elem x l1 /\ elem x l2.
(* begin hide *)
Proof.
  intros.
  functional induction interleave l1 l2.
    firstorder; inv H.
    firstorder; inv H; inv H0.
    {
      rewrite !Dup_cons, !elem_cons', !IHl,
              !elem_Exists, !Exists_interleave, <- !elem_Exists.
      firstorder; subst; cbn in *.
        do 2 right. exists h2. split; constructor.
        do 2 right. exists h1. split; constructor; assumption.
        do 2 right. exists h2. split; constructor; assumption.
        do 2 right. exists x. split; constructor; assumption.
        inv H3; inv H4; eauto. eauto 7.
    }
Qed.
(* end hide *)

(** ** [groupBy] *)

(** Zdefiniuj funkcję
    [groupBy : forall (A : Type) (p : A -> A -> bool), list A -> list (list A)],
    która dzieli wejściową listę na listę list, których każde dwa sąsiadujące
    elementy spełniają predykat [p].

    Przykłady: *)

(** [groupBy leb [2; 4; 6; 0; 1; 2; 3; 0; 9; 0] = [[2; 4; 6]; [0; 1; 2; 3]; [0; 9]; [0]]] *)

(** [groupBy eqb [1; 1; 2; 3; 3; 3; 4; 5; 4; 4] = [[1; 1]; [2]; [3; 3; 3]; [4]; [5]; [4; 4]]] *)

(* begin hide *)
Function groupBy
  {A : Type} (p : A -> A -> bool) (l : list A) : list (list A) :=
match l with
| [] => []
| h :: t =>
  match groupBy p t with
  | [] => [[h]]
  | [] :: gs => [h] :: gs
  | (h' :: t') :: gs =>
    if p h h'
    then (h :: h' :: t') :: gs
    else [h] :: (h' :: t') :: gs
  end
end.
(* end hide *)

Lemma head_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    ~ head (groupBy p l) = Some [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 1.
    destruct (groupBy p t).
      inversion 1.
      cbn in IHt. destruct l.
        contradiction.
        destruct (p h a); cbn; inversion 1.
Qed.
(* end hide *)

Lemma head_groupBy' :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    head (groupBy p l) = None
    \/
    exists (h : A) (t : list A),
      head (groupBy p l) = Some (h :: t).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    left. constructor.
    destruct (groupBy p t).
      right. exists h, []. cbn. reflexivity.
      destruct IHt as [IH | (h' & t' & IH)].
        inversion IH.
        destruct l.
          right. exists h, []. cbn. reflexivity.
          right. destruct (p h a); cbn.
            exists h, (a :: l). cbn. reflexivity.
            exists h, []. cbn. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_is_nil :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    groupBy p l = [] -> l = [].
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (groupBy p t); cbn in *.
      inversion H.
      destruct l; cbn in *.
        inversion H.
        destruct (p h a); inversion H.
Qed.
(* end hide *)

Lemma isEmpty_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    isEmpty (groupBy p l) = isEmpty l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    length (groupBy p l) <= length l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l;
  rewrite ?e0 in *; try clear e0; cbn in *.
    apply le_n.
    apply le_n_S, IHl0.
    apply le_S, IHl0.
    apply le_S, IHl0.
    apply le_n_S, IHl0.
Qed.
(* end hide *)

Ltac gb :=
match goal with
| H : groupBy _ ?l = [] |- _ =>
  apply (f_equal isEmpty) in H;
  rewrite isEmpty_groupBy in H;
  destruct l; inversion H; subst
| H : groupBy _ _ = [] :: _ |- _ =>
  apply (f_equal head), head_groupBy in H; contradiction
end; cbn; try congruence.

Require Import Arith.

Compute groupBy beq_nat [0; 1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].
Compute groupBy
  (fun n m => negb (beq_nat n m))
  [0; 1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].

Lemma groupBy_decomposition :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    l = [] \/ exists n : nat,
      groupBy p l = take n l :: groupBy p (drop n l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l.
    left. reflexivity.
      gb. right. exists 1. cbn. reflexivity.
      gb.
    destruct IHl0; subst.
      cbn in e0. inversion e0.
      right. destruct H as [n H]. exists (S n). cbn.
        rewrite e0 in H. inversion H. reflexivity.
    destruct IHl0; subst.
      cbn in e0. inversion e0.
      destruct H as [n H]. rewrite e0 in H. inversion H; subst.
        right. exists 1. cbn. rewrite take_0, drop_0, e0. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_cons :
  forall (A : Type) (p : A -> A -> bool) (l h : list A) (t : list (list A)),
    groupBy p l = h :: t -> groupBy p h = [h].
(* begin hide *)
Proof.
  intros A p l. functional induction @groupBy A p l; cbn; intros.
    inv H.
    inv H. cbn. reflexivity.
    gb.
    inv H. rewrite e0 in *. cbn in *.
      specialize (IHl0 _ _ eq_refl). cbn in *. destruct (groupBy p t').
        rewrite e1. inversion IHl0. reflexivity.
        destruct l.
          rewrite e1. inversion IHl0. reflexivity.
          destruct (p h' a); rewrite e1; inversion IHl0; reflexivity.
    inversion H; subst; clear H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_app_decomposition :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    groupBy p l = [] \/
    groupBy p l = [l] \/
    exists l1 l2 : list A,
      l = l1 ++ l2 /\
      groupBy p l = groupBy p l1 ++ groupBy p l2.
(* begin hide *)
Proof.
  intros. destruct (groupBy_decomposition A p l).
    left. rewrite H. cbn. reflexivity.
    destruct H as [n H]. rewrite H. do 2 right.
      exists (take n l), (drop n l). split.
        rewrite app_take_drop. reflexivity.
         apply groupBy_cons in H. rewrite H. cbn. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_middle :
  forall (A : Type) (p : A -> A -> bool) (l1 l2 : list A) (x y : A),
    p x y = false ->
      groupBy p (l1 ++ x :: y :: l2) =
      groupBy p (l1 ++ [x]) ++ groupBy p (y :: l2).
(* begin hide *)
Proof.
  intros A p l1. functional induction @groupBy A p l1; cbn; intros.
    destruct (groupBy p l2) eqn: Heq.
      rewrite H. reflexivity.
      destruct l; cbn; rewrite ?H.
        reflexivity.
        destruct (p y a); rewrite H; reflexivity.
    gb. destruct (groupBy p l2).
      rewrite H. destruct (p h x); reflexivity.
      destruct l; cbn.
        rewrite H. destruct (p h x); reflexivity.
        destruct (p y a); rewrite H; destruct (p h x); reflexivity.
    rewrite (IHl _ _ _ H). destruct t; cbn.
      destruct (p h x); reflexivity.
      destruct (groupBy p (t ++ [x])), (groupBy p l2); cbn.
        destruct (p h a); reflexivity.
        destruct (p h a); reflexivity.
        destruct l; cbn.
          destruct (p h a); reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
        destruct l; cbn.
          destruct (p h a); reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
    rewrite (IHl _ _ _ H); clear IHl. destruct t; cbn.
      destruct (p h x); reflexivity.
      cbn in *. destruct (groupBy p (t ++ [x])), (groupBy p l2); cbn.
        1-2: destruct (p h a); reflexivity.
        destruct l; cbn; destruct (p h a).
          reflexivity.
          cbn. reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
        destruct l; cbn.
          destruct (p h a); cbn; reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
    rewrite (IHl _ _ _ H); clear IHl. destruct t; cbn.
      destruct (p h x); reflexivity.
      cbn in *. destruct (groupBy p (t ++ [x])), (groupBy p l2); cbn.
        1-2: destruct (p h a); reflexivity.
        destruct l; cbn; destruct (p h a).
          reflexivity.
          cbn. reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
        destruct l; cbn.
          destruct (p h a); cbn; reflexivity.
          destruct (p a a0); cbn; destruct (p h a); reflexivity.
Restart.
  Ltac wut H :=
  match H with
  | context [match ?x with _ => _ end] => wut x
  | _ => destruct H
  end.
  Ltac dst :=
  repeat (cbn in *; match goal with
  | |- ?goal => wut goal
  end); cbn in *; try congruence; gb.

  intros A p l1. functional induction @groupBy A p l1; cbn; intros.
    dst.
    gb. dst.
    gb.
    1-2: rewrite (IHl _ _ _ H); clear IHl; destruct t; dst.
Qed.
(* end hide *)

Lemma groupBy_app :
  forall (A : Type) (p : A -> A -> bool) (l1 l2 : list A) (x y : A),
    last l1 = Some x -> head l2 = Some y -> p x y = false ->
      groupBy p (l1 ++ l2) = groupBy p l1 ++ groupBy p l2.
(* begin hide *)
Proof.
  intros. destruct (init l1) eqn: Heq.
    destruct l2.
      cbn. rewrite ?app_nil_r. reflexivity.
      rewrite (init_last _ _ _ _ Heq H), <- app_assoc. cbn.
        rewrite groupBy_middle.
          cbn. reflexivity.
          inversion H0. assumption.
    destruct l1; cbn in *.
      inversion H.
      destruct (init l1); inversion Heq.
Qed.
(* end hide *)

Lemma groupBy_app' :
  forall (A : Type) (p : A -> A -> bool) (l1 l2 : list A),
    groupBy p (l1 ++ l2) =
    match last l1, head l2 with
    | None, _ => groupBy p l2
    | _, None => groupBy p l1
    | Some x, Some y =>
      if p x y
      then groupBy p (l1 ++ l2)
      else groupBy p l1 ++ groupBy p l2
    end.
(* begin hide *)
Proof.
  intros.
  destruct (last l1) eqn: Hlast.
    destruct (head l2) eqn: Hhead.
      destruct (p a a0) eqn: Heq.
        reflexivity.
        erewrite groupBy_app; eauto.
      destruct l2; inv Hhead. rewrite app_nil_r. reflexivity.
    apply last_None in Hlast. subst. cbn. reflexivity.
Qed.
(* end hide *)

Lemma groupBy_singl :
  forall (A : Type) (p : A -> A -> bool) (x : A) (l : list A),
    groupBy p l = [[x]] -> l = [x].
(* begin hide *)
Proof.
  intros.
  functional induction groupBy p l; inv H.
    functional inversion e0. reflexivity.
    functional inversion e0.
Qed.
(* end hide *)

Lemma groupBy_rev_aux :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    (forall x y : A, p x y = p y x) ->
      groupBy p l = rev (map rev (groupBy p (rev l))).
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma rev_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    (forall x y : A, p x y = p y x) ->
      rev (groupBy p l) = map rev (groupBy p (rev l)).
(* begin hide *)
Proof.
  intros. rewrite groupBy_rev_aux.
    rewrite rev_rev. reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma groupBy_rev :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    (forall x y : A, p x y = p y x) ->
      groupBy p (rev l) = rev (map rev (groupBy p l)).
(* begin hide *)
Proof.
  intros. rewrite groupBy_rev_aux.
    rewrite rev_rev. reflexivity.
    assumption.
Qed.
(* end hide *)

Lemma groupBy_map :
  forall (A B : Type) (f : A -> B) (p : B -> B -> bool) (l : list A),
    groupBy p (map f l) =
    map (map f) (groupBy (fun x y => p (f x) (f y)) l).
(* begin hide *)
Proof.
  intros. remember (fun _ => _) as p'.
  functional induction @groupBy A p' l;
  rewrite ?e0 in *; cbn in *; rewrite ?IHl0; trivial.
    destruct (p (f h) (f h')); cbn.
      reflexivity.
      congruence.
    destruct (p (f h) (f h')); cbn.
      congruence.
      reflexivity.
Qed.
(* end hide *)

Lemma map_groupBy_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    map (groupBy p) (groupBy p l) =
    map (fun x => [x]) (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    1-2: reflexivity.
    gb.
    rewrite e0 in *. cbn in *. destruct (groupBy p t').
      rewrite e1. inversion IHl0. reflexivity.
      destruct l; cbn.
        rewrite e1. inversion IHl0. reflexivity.
        destruct (p h' a); rewrite e1.
          inversion IHl0. reflexivity.
          inversion IHl0.
    rewrite e0 in *. cbn in *. destruct (groupBy p t').
      inversion IHl0. reflexivity.
      destruct l; inversion IHl0; reflexivity.
Qed.
(* end hide *)

Lemma join_groupBy :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    join (groupBy p l) = l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    reflexivity.
    gb.
    gb.
    rewrite <- IHl0, e0. cbn. reflexivity.
    rewrite <- IHl0, e0. cbn. reflexivity.
Qed.
(* end hide *)

Definition isZero (n : nat) : bool :=
match n with
| 0 => true
| _ => false
end.

Lemma groupBy_replicate :
  forall (A : Type) (p : A -> A -> bool) (n : nat) (x : A),
    groupBy p (replicate n x) =
    if isZero n
    then []
    else if p x x then [replicate n x] else replicate n [x].
(* begin hide *)
Proof.
  destruct n as [| n']; cbn; intros.
    reflexivity.
    induction n' as [| n'']; cbn.
      destruct (p x x); reflexivity.
      rewrite IHn''. destruct (p x x) eqn: H; rewrite H; reflexivity.
Qed.
(* end hide *)

Lemma groupBy_take :
  exists (A : Type) (p : A -> A -> bool) (l : list A) (n : nat),
    forall m : nat,
      groupBy p (take n l) <> take m (groupBy p l).
(* begin hide *)
Proof.
  exists nat, (fun _ _ => true), [1; 2; 3], 2.
  intro.
  cbn. destruct m; inversion 1.
Qed.
(* end hide *)

Lemma any_groupBy :
  forall (A : Type) (q : A -> bool) (p : A -> A -> bool) (l : list A),
    any (any q) (groupBy p l) = any q l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l;
  cbn; rewrite ?Bool.orb_false_r; try rewrite ?e0 in IHl0.
    reflexivity.
    gb.
    rewrite Bool.orb_false_r. reflexivity.
    gb.
    cbn in IHl0. rewrite <- IHl0. rewrite ?Bool.orb_assoc. reflexivity.
    cbn in IHl0. rewrite <- IHl0. reflexivity.
Qed.
(* end hide *)

Lemma all_groupBy :
  forall (A : Type) (q : A -> bool) (p : A -> A -> bool) (l : list A),
    all (all q) (groupBy p l) = all q l.
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l; cbn.
    reflexivity.
    gb.
    rewrite Bool.andb_true_r. reflexivity.
    gb.
    1-2: rewrite ?e0 in IHl0; cbn in *; rewrite <- IHl0.
      rewrite ?Bool.andb_assoc. reflexivity.
      rewrite <- ?Bool.andb_assoc. cbn. reflexivity.
Qed.
(* end hide *)

Lemma find_groupBy :
  forall (A : Type) (q : A -> bool) (p : A -> A -> bool) (l : list A),
    find q l =
    match find (any q) (groupBy p l) with
    | None => None
    | Some g => find q g
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (q h) eqn: Hqh.
      destruct (groupBy p t); cbn in *.
        rewrite Hqh. cbn. rewrite Hqh. reflexivity.
        destruct l as [| h' t']; cbn in *.
          rewrite Hqh. cbn. rewrite Hqh. reflexivity.
          destruct (p h h'); cbn.
            rewrite Hqh. cbn. rewrite Hqh. reflexivity.
            rewrite Hqh. cbn. rewrite Hqh. reflexivity.
      destruct (groupBy p t); cbn in *.
        rewrite Hqh. cbn. assumption.
        destruct l as [| h' t']; cbn in *.
          rewrite Hqh. cbn. assumption.
          destruct (p h h'); cbn.
            rewrite Hqh. cbn. rewrite IHt. destruct (q h'); cbn.
              rewrite Hqh. reflexivity.
              cbn in *. destruct (any q t'); cbn.
                rewrite Hqh. reflexivity.
                reflexivity.
            rewrite Hqh. cbn. assumption.
Qed.
(* end hide *)

Lemma groupBy_elem_incl :
  forall (A : Type) (p : A -> A -> bool) (l g : list A),
    elem g (groupBy p l) -> Incl g l.
(* begin hide *)
Proof.
  intros. revert g H. functional induction @groupBy A p l; intros;
  try rewrite ?e0 in IHl0.
    inversion H.
    inversion H; subst; clear H.
      gb.
      inversion H2.
    gb.
    inversion H; subst; clear H.
      apply Incl_cons, IHl0. left.
      apply Incl_cons'', IHl0. right. assumption.
    inversion H; subst; clear H.
      apply Incl_cons, Incl_nil.
      apply Incl_cons'', IHl0. assumption.
Qed.
(* end hide *)

Lemma groupBy_elem :
  forall (A : Type) (p : A -> A -> bool) (x : A) (l : list A),
    elem x l -> exists g : list A, elem x g /\ elem g (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l.
    inversion H.
    gb.
    inversion H; subst; clear H.
      exists [h]. split; constructor.
      inversion H2.
    gb.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists (h :: h' :: t'). split; constructor.
      destruct (IHl0 H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists (h :: h' :: t'). split.
            right. assumption.
            left.
          exists g. split; try right; assumption.
    rewrite e0 in IHl0. inversion H; subst; clear H.
      exists [h]. split; constructor.
      destruct (IHl0 H2) as (g & IH1 & IH2).
        inversion IH2; subst; clear IH2.
          exists (h' :: t'). split.
            assumption.
            right. left.
          exists g. split; repeat right; assumption.
Qed.
(* end hide *)

Lemma groupBy_elem_nil :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    ~ elem [] (groupBy p l).
(* begin hide *)
Proof.
  intros. functional induction @groupBy A p l.
    inversion 1.
    intro. inversion H; subst. inversion H2.
    gb.
    inversion 1; subst. apply IHl0. rewrite e0. right. assumption.
    inversion 1; subst. apply IHl0. rewrite e0. assumption.
Qed.
(* end hide *)

(** ** [insertBefore] *)

(** TODO: napisz polecenie do [insertBefore] *)

Module insertBefore.

Fixpoint insertBefore {A : Type} (n : nat) (l1 l2 : list A) : list A :=
match n with
| 0 => l2 ++ l1
| S n' =>
  match l1 with
  | [] => l2
  | h :: t => h :: insertBefore n' t l2
  end
end.

Notation "'insert' l2 'before' n 'in' l1" :=
  (insertBefore n l1 l2) (at level 40).

Lemma insert_nil_before :
  forall (A : Type) (n : nat) (l : list A),
    (insert [] before n in l) = l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct l as [| h t]; cbn; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma insert_before_in_nil:
  forall (A : Type) (n : nat) (l : list A),
    (insert l before n in []) = l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros; rewrite ?app_nil_r; reflexivity.
Qed.
(* end hide *)

Lemma insert_before_in_char :
  forall (A : Type) (l1 l2 : list A) (n : nat),
    insert l2 before n in l1 =
    take n l1 ++ l2 ++ drop n l1.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil, app_nil_r.
      cbn. reflexivity.
    destruct n as [| n']; cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_insertBefore :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    isEmpty (insert l2 before n in l1) =
    andb (isEmpty l1) (isEmpty l2).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    intros. rewrite isEmpty_app.
      destruct (isEmpty l1), (isEmpty l2); reflexivity.
    destruct l1; reflexivity.
Qed.
(* end hide *)

Lemma length_insertBefore :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length (insert l2 before n in l1) =
    length l1 + length l2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    intros. rewrite length_app, plus_comm. reflexivity.
    destruct l1; cbn; intros.
      reflexivity.
      rewrite IHn'. reflexivity.
Restart.
  intros.
  rewrite insert_before_in_char, ?length_app, length_drop.
    rewrite length_take. apply Min.min_case_strong; intros; lia.
Qed.
(* end hide *)

Lemma insert_before_0 :
  forall (A : Type) (l1 l2 : list A),
    insert l2 before 0 in l1 = l2 ++ l1.
(* begin hide *)
Proof.
  cbn. reflexivity.
Qed.
(* end hide *)

Lemma insert_before_gt :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 <= n -> insert l2 before n in l1 = l1 ++ l2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct l1; inversion H. cbn. rewrite app_nil_r. reflexivity.
    destruct l1 as [| h t]; cbn in *.
      reflexivity.
      rewrite IHn'.
        reflexivity.
        apply le_S_n. assumption.
Restart.
  intros.
  rewrite insert_before_in_char, ?length_app.
  rewrite take_length'.
    rewrite drop_length'.
      rewrite app_nil_r. reflexivity.
      1-2: assumption.
Qed.
(* end hide *)

Lemma insert_before_length :
  forall (A : Type) (l1 l2 : list A),
    insert l2 before length l1 in l1 = l1 ++ l2.
(* begin hide *)
Proof.
  intros. rewrite insert_before_gt; reflexivity.
Qed.
(* end hide *)

Lemma insert_before_length_in_app :
  forall (A : Type) (l1 l2 l : list A),
    insert l before length l1 in (l1 ++ l2) =
    l1 ++ l ++ l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros; rewrite ?IHt; reflexivity.
Restart.
  intros.
  rewrite insert_before_in_char,
    take_app_l, drop_app_l, take_length, drop_length. cbn.
  all: reflexivity.
Qed.
(* end hide *)

Lemma insert_before_le_in_app :
  forall (A : Type) (n : nat) (l1 l2 l3 : list A),
    n <= length l1 ->
      insert l3 before n in (l1 ++ l2) =
      (insert l3 before n in l1) ++ l2.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite app_assoc. reflexivity.
    destruct l1 as [| h t]; cbn.
      destruct l2 as [| h' t']; cbn.
        rewrite app_nil_r. reflexivity.
        inversion H.
      rewrite IHn'.
        reflexivity.
        apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma insert_app_before :
  forall (A : Type) (n : nat) (l1 l2 l : list A),
    insert l1 ++ l2 before n in l =
    insert l2 before (n + length l1) in (insert l1 before n in l).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite insert_before_length_in_app, app_assoc. reflexivity.
    destruct l as [| h t]; cbn.
      destruct l1 as [| h1 t1]; cbn.
        reflexivity.
        rewrite insert_before_gt.
          reflexivity.
          eapply le_trans with (n' + length t1).
            apply le_plus_r.
            apply plus_le_compat_l, le_S, le_n.
      rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma insert_before_plus_in_app :
  forall (A : Type) (l1 l2 l3 : list A) (n : nat),
    insert l3 before (length l1 + n) in (l1 ++ l2) =
    l1 ++ insert l3 before n in l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      rewrite plus_0_r, insert_before_length_in_app. reflexivity.
      rewrite IHt. destruct l2 as [| h' t']; cbn.
        reflexivity.
        reflexivity.
Qed.
(* end hide *)

Lemma rev_insert_before :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    rev (insert l2 before n in l1) =
    insert (rev l2) before (length l1 - n) in rev l1.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    rewrite rev_app, <- minus_n_O, <- length_rev, insert_before_length.
      reflexivity.
    destruct l1 as [| h t]; cbn.
      rewrite app_nil_r. reflexivity.
      rewrite IHn', !snoc_app_singl, insert_before_le_in_app.
        reflexivity.
        rewrite length_rev. apply Nat.le_sub_l.
Qed.
(* end hide *)

Lemma minus_wut :
  forall n m : nat,
    n <= m -> n - m = 0.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      inversion H.
      apply IHn', le_S_n. assumption.
Qed.

Lemma minus_wut' :
  forall n m : nat,
    n <= m -> n - (n - m) = n.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      inversion H.
      rewrite minus_wut.
        reflexivity.
        apply le_S_n. assumption.
Qed.

Lemma minus_wut'' :
  forall n m : nat,
    m <= n -> n - (n - m) = m.
Proof.
  intros. lia.
Qed.

Lemma insert_before_in_rev :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    insert l2 before n in rev l1 =
    rev (insert rev l2 before (length l1 - n) in l1).
(* begin hide *)
Proof.
  intros. rewrite rev_insert_before, rev_rev.
  destruct (le_ge_dec (length l1) n).
    rewrite minus_wut'.
      rewrite <- length_rev, ?insert_before_gt.
        1-2: reflexivity.
        rewrite length_rev. 1-2: assumption.
    rewrite minus_wut''.
      reflexivity.
      unfold ge in g. assumption.
Qed.
(* end hide *)

Lemma insert_rev_before :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    insert (rev l2) before n in l1 =
    rev (insert l2 before (length l1 - n) in (rev l1)).
(* begin hide *)
Proof.
  intros. rewrite <- (rev_rev _ l2) at 2.
  rewrite <- (length_rev _ l1), <- insert_before_in_rev, rev_rev.
  reflexivity.
Qed.
(* end hide *)

Lemma map_insert_before_in :
  forall (A B : Type) (f : A -> B) (n : nat) (l1 l2 : list A),
    map f (insert l2 before n in l1) =
    insert (map f l2) before n in (map f l1).
(* begin hide *)
Proof.
  intros A B f n l1. generalize dependent n.
  induction l1 as [| h t]; cbn; intros.
    rewrite ?insert_before_in_nil. reflexivity.
    destruct n as [| n']; cbn.
      rewrite map_app. cbn. reflexivity.
      rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma join_insert_before_in :
  forall (A : Type) (l1 l2 : list (list A)) (n : nat),
    join (insert l2 before n in l1) =
    insert (join l2) before (length (join (take n l1))) in (join l1).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil. cbn. rewrite app_nil_r.
      reflexivity.
    destruct n as [| n']; cbn.
      rewrite join_app. cbn. reflexivity.
      rewrite IHt, length_app, insert_before_plus_in_app. reflexivity.
Qed.
(* end hide *)

Lemma insert_before_in_replicate :
  forall (A : Type) (m n : nat) (x : A) (l : list A),
    insert l before n in replicate m x =
    replicate (min n m) x ++ l ++ replicate (m - n) x.
(* begin hide *)
Proof.
  induction m as [| m']; cbn; intros.
    rewrite insert_before_in_nil, app_nil_r, Min.min_0_r. cbn. reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite IHm'. reflexivity.
Qed.
(* end hide *)

Lemma nth_insert_before_in :
  forall (A : Type) (n m : nat) (l1 l2 : list A),
    nth n (insert l2 before m in l1) =
    if leb (S n) m
    then nth n l1
    else nth (n - m) (l2 ++ drop m l1).
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
Abort.
(* end hide *)

Lemma head_insert_before_in :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    head (insert l2 before n in l1) =
    match l1 with
    | [] => head l2
    | h1 :: _ =>
      match n with
      | 0 =>
        match l2 with
        | [] => Some h1
        | h2 :: _ => Some h2
        end
      | _ => Some h1
      end
    end.
(* begin hide *)
Proof.
  intros.
  rewrite insert_before_in_char, ?head_app.
  destruct n, l1; cbn.
    all: destruct l2; reflexivity.
Qed.
(* end hide *)

Lemma any_insert_before_in :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A) (n : nat),
    any p (insert l2 before n in l1) =
    orb (any p l1) (any p l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil. reflexivity.
    destruct (p h) eqn: Hph, n as [| n']; cbn.
      rewrite any_app, Bool.orb_comm. cbn. rewrite Hph. cbn. reflexivity.
      rewrite Hph, IHt. cbn. reflexivity.
      rewrite any_app, Bool.orb_comm. cbn. rewrite Hph. reflexivity.
      rewrite Hph, IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma all_insert_before_in :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A) (n : nat),
    all p (insert l2 before n in l1) =
    andb (all p l1) (all p l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil. reflexivity.
    destruct (p h) eqn: Hph, n as [| n']; cbn.
      rewrite all_app, Bool.andb_comm. cbn. rewrite Hph. cbn. reflexivity.
      rewrite Hph, IHt. cbn. reflexivity.
      rewrite all_app, Bool.andb_comm. cbn. rewrite Hph. reflexivity.
      rewrite Hph, IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma count_insert_before_in :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A) (n : nat),
    count p (insert l2 before n in l1) =
    count p l1 + count p l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil. reflexivity.
    destruct (p h) eqn: Hph, n as [| n']; cbn.
      rewrite count_app, plus_comm. cbn. rewrite Hph. cbn. reflexivity.
      rewrite Hph, IHt. reflexivity.
      rewrite count_app, plus_comm. cbn. rewrite Hph. reflexivity.
      rewrite Hph, IHt. reflexivity.
Qed.
(* end hide *)

Lemma elem_insert_before_in :
  forall (A : Type) (x : A) (l1 l2 : list A) (n : nat),
    elem x (insert l2 before n in l1) <->
    elem x l1 \/ elem x l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil. firstorder. inversion H.
    destruct n as [| n']; cbn.
      rewrite elem_app, ?elem_cons'. firstorder congruence.
      rewrite ?elem_cons', IHt. firstorder congruence.
Qed.
(* end hide *)

Lemma In_insert_before_in :
  forall (A : Type) (x : A) (l1 l2 : list A) (n : nat),
    In x (insert l2 before n in l1) <->
    In x l1 \/ In x l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil. firstorder.
    destruct n as [| n']; cbn.
      rewrite In_app; cbn. firstorder congruence.
      rewrite IHt. firstorder congruence.
Qed.
(* end hide *)

Lemma Exists_insert_before_in :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A) (n : nat),
    Exists P (insert l2 before n in l1) <->
    Exists P l1 \/ Exists P l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil. firstorder. inversion H.
    destruct n as [| n']; cbn.
      rewrite Exists_app; cbn. firstorder congruence.
      rewrite ?Exists_cons, IHt. firstorder congruence.
Qed.
(* end hide *)

Lemma Forall_insert_before_in :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A) (n : nat),
    Forall P (insert l2 before n in l1) <->
    Forall P l1 /\ Forall P l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    rewrite insert_before_in_nil. firstorder. constructor.
    destruct n as [| n']; cbn.
      rewrite Forall_app, Forall_cons. firstorder congruence.
      rewrite ?Forall_cons, IHt. firstorder congruence.
Qed.
(* end hide *)

Lemma AtLeast_insert_before_in :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A) (n m : nat),
    AtLeast P m (insert l2 before n in l1) <->
    (exists m1 m2 : nat,
      AtLeast P m1 l1 /\ AtLeast P m2 l2 /\ m = m1 + m2).
(* begin hide *)
Proof.
  split.
    revert l2 m n.
    induction l1 as [| h t]; cbn; intros.
      exists 0, m. repeat split.
        constructor.
        rewrite insert_before_in_nil in H. assumption.
      destruct n as [| n']; cbn in *.
        apply AtLeast_app_conv in H. firstorder lia.
        destruct t as [| h' t'].
          rewrite insert_before_in_nil in H.
            change (h :: l2) with ([h] ++ l2) in H.
            apply AtLeast_app_conv in H. firstorder.
          inversion H; subst.
            exists 0, 0. firstorder constructor.
            destruct (IHt _ _ _ H4) as (m1 & m2 & IH).
              exists (S m1), m2. firstorder; subst; constructor; trivial.
            destruct (IHt _ _ _ H2) as (m1 & m2 & IH).
              exists m1, m2. firstorder. constructor. assumption.
    destruct 1 as (m1 & m2 & H1 & H2 & H3); subst.
      rewrite insert_before_in_char.
      apply AtLeast_app_comm. rewrite <- app_assoc. apply AtLeast_app.
        exists m2, m1. split.
          assumption.
          pose (AtLeast_take_drop _ _ _ n _ H1).
            rewrite AtLeast_app. firstorder lia.
Qed.
(* end hide *)

End insertBefore.

(** * Predykaty i relacje na listach - znowu (TODO) *)

Module Recursives.

(** Można zadać sobie pytanie: skoro predykaty takie jak [elem] czy
    [exists] można zdefiniować zarówno induktywnie jak i przez rekursję,
    który sposób jest lepszy?

    Odpowiedź jest prosta: jeżeli możesz użyć rekursji, zrób to. *)

Fixpoint elem {A : Type} (x : A) (l : list A) : Prop :=
match l with
| [] => False
| h :: t => x = h \/ elem x t
end.

Fixpoint all {A : Type} (P : A -> Prop) (l : list A) : Prop :=
match l with
| [] => True
| h :: t => P h /\ all P t
end.

Lemma all_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    all P l <-> Forall P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    rewrite Forall_nil. reflexivity.
    rewrite Forall_cons, IHt. reflexivity.
Qed.
(* end hide *)

Fixpoint exactly
  {A : Type} (P : A -> Prop) (n : nat) (l : list A) : Prop :=
match l, n with
| [], 0 => True
| [], _ => False
| h :: t, 0 => ~ P h /\ exactly P 0 t
| h :: t, S n' =>
    (P h /\ exactly P n' t) \/ (~ P h /\ exactly P n t)
end.

Lemma exactly_spec :
  forall (A : Type) (P : A -> Prop) (n : nat) (l : list A),
    exactly P n l <-> Exactly P n l.
(* begin hide *)
Proof.
  intros. revert n.
  induction l as [| h t]; cbn.
    destruct n; cbn.
      firstorder. apply Ex_0.
      firstorder. inversion H.
    destruct n as [| n']; cbn.
      rewrite IHt, Exactly_0_cons. reflexivity.
      rewrite !IHt, Exactly_S_cons. reflexivity.
Qed.
(* end hide *)

(** ** [exists] *)

(* begin hide *)
Fixpoint ex {A : Type} (P : A -> Prop) (l : list A) : Prop :=
match l with
| [] => False
| h :: t => P h \/ ex P t
end.
(* end hide *)

Lemma ex_spec :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l <-> exists x : A, elem x l /\ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder.
    firstorder congruence.
Qed.
(* end hide *)

Lemma ex_nil :
  forall (A : Type) (P : A -> Prop),
    ex P [] <-> False.
(* begin hide *)
Proof.
  split; inversion 1.
Qed.
(* end hide *)

Lemma ex_cons :
  forall (A : Type) (P : A -> Prop) (h : A) (t : list A),
    ex P (h :: t) <-> P h \/ ex P t.
(* begin hide *)
Proof.
  split.
    inversion 1; subst; [left | right]; assumption.
    destruct 1; [left | right]; assumption.
Qed.
(* end hide *)

Lemma ex_length :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l -> 1 <= length l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    destruct 1.
    intros _. apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma ex_snoc :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    ex P (snoc x l) <-> ex P l \/ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder.
    rewrite IHt. firstorder.
Qed.
(* end hide *)

Lemma ex_app :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    ex P (l1 ++ l2) <-> ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    firstorder.
    rewrite IHt1. tauto.
Qed.
(* end hide *)

Lemma ex_rev :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P (rev l) <-> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite ex_snoc, IHt. cbn. tauto.
Qed.
(* end hide *)

Lemma ex_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (l : list A),
    ex P (map f l) -> ex (fun x : A => P (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    tauto.
Qed.
(* end hide *)

Lemma ex_join :
  forall (A : Type) (P : A -> Prop) (ll : list (list A)),
    ex P (join ll) <->
    ex (fun l : list A => ex  P l) ll.
(* begin hide *)
Proof.
  induction ll as [| h t]; cbn; intros.
    reflexivity.
    rewrite ex_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma ex_replicate :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
    ex P (replicate n x) <-> 1 <= n /\ P x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    firstorder. inversion H.
    firstorder. apply le_n_S, le_0_n.
Qed.
(* end hide *)

Lemma ex_nth :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ex P l <->
    exists (n : nat) (x : A), nth n l = Some x /\ P x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    firstorder congruence.
    rewrite IHt. split.
      destruct 1.
        exists 0, h. split; trivial.
        destruct H as (n & x & H1 & H2).
          exists (S n), x. split; assumption.
      destruct 1 as (n & x & H1 & H2). destruct n as [| n'].
        left. congruence.
        right. exists n', x. split; assumption.
Qed.
(* end hide *)

Lemma ex_remove :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P l ->
    match remove n l with
    | None => True
    | Some (x, l') => ~ P x -> ex P l'
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 2.
    destruct n as [| n'].
      firstorder.
      destruct 1.
        case_eq (remove n' t).
          intros [a la] eq Hnot. cbn. left. assumption.
          trivial.
        case_eq (remove n' t).
          intros [a la] eq Hnot. cbn. specialize (IHt n' H).
            rewrite eq in IHt. right. apply IHt. assumption.
          trivial.
Qed.
(* end hide *)

Lemma ex_take :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P (take n l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      inversion H.
      cbn in H. firstorder.
Qed.
(* end hide *)

Lemma ex_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P (drop n l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct n as [| n']; cbn.
      cbn in H. assumption.
      right. apply (IHt _ H).
Qed.
(* end hide *)

Lemma ex_take_drop :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat),
    ex P l -> ex P (take n l) \/ ex P (drop n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    left. assumption.
    destruct n as [| n']; cbn.
      right. assumption.
      firstorder.
Qed.
(* end hide *)

Lemma ex_splitAt :
  forall (A : Type) (P : A -> Prop) (l l1 l2 : list A) (n : nat) (x : A),
    splitAt n l = Some (l1, x, l2) ->
      ex P l <-> P x \/ ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    inversion 2.
    destruct n as [| n']; cbn; inversion 1; subst.
      cbn. tauto.
      case_eq (splitAt n' t); intros.
        destruct p, p. rewrite (IHt _ _ _ _ H0).
          rewrite H0 in H1. inversion H1; subst. cbn. tauto.
        rewrite H0 in H1. inversion H1.
Restart.
  intros. pose (splitAt_megaspec A l n). rewrite H in y.
  decompose [and] y; clear y. rewrite H4; subst; clear H4.
  rewrite ex_app, ex_cons. firstorder.
Qed.
(* end hide *)

Lemma ex_insert :
  forall (A : Type) (P : A -> Prop) (l : list A) (n : nat) (x : A),
    ex P (insert l n x) <-> P x \/ ex P l.
(* begin hide *)
Proof.
  intros.
  rewrite <- (app_take_drop _ l n) at 2.
  rewrite insert_spec, !ex_app, ex_cons.
  tauto.
Qed.
(* end hide *)

Lemma ex_replace :
  forall (A : Type) (P : A -> Prop) (l l' : list A) (n : nat) (x : A),
    replace l n x = Some l' ->
      ex P l' <->
      ex P (take n l) \/ P x \/ ex P (drop (S n) l).
(* begin hide *)
Proof.
  intros. rewrite replace_spec in H.
  destruct (n <? length l).
    inversion H; subst. rewrite ex_app, ex_cons. reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma ex_filter :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (filter p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h); cbn in H; firstorder.
Qed.
(* end hide *)

Lemma ex_filter_conv :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P l ->
      ex P (filter p l) \/
      ex P (filter (fun x : A => negb (p x)) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 1.
    destruct (p h); cbn; firstorder.
Qed.
(* end hide *)

Lemma ex_filter_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ ex P (filter p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    assumption.
    specialize (IHt H). specialize (H h). destruct (p h); cbn in *.
      firstorder congruence.
      contradiction.
Qed.
(* end hide *)

Lemma ex_partition :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l l1 l2 : list A),
    partition p l = (l1, l2) ->
      ex P l <-> ex P l1 \/ ex P l2.
(* begin hide *)
Proof.
  intros. rewrite partition_spec in H.
  inversion H; subst; clear H. split; intro.
    apply ex_filter_conv. assumption.
    destruct H; apply ex_filter in H; assumption.
Qed.
(* end hide *)

Lemma ex_takeWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (takeWhile p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros;
  try destruct (p h); inversion H; subst; clear H.
    left. assumption.
    right. apply IHt, H0.
Qed.
(* end hide *)

Lemma ex_takeWhile_compat :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    (forall x : A, P x <-> p x = false) -> ~ ex P (takeWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros; intro.
    assumption.
    specialize (IHt H). specialize (H h).
      destruct (p h); cbn in *; firstorder congruence.
Qed.
(* end hide *)

Lemma ex_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P (dropWhile p l) -> ex P l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    destruct (p h); firstorder.
Qed.
(* end hide *)

Lemma ex_takeWhile_dropWhile :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (l : list A),
    ex P l -> ex P (takeWhile p l) \/ ex P (dropWhile p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct 1.
    destruct (p h); cbn; firstorder.
Qed.
(* end hide *)

Lemma ex_span :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (x : A) (l b e : list A),
      (forall x : A, P x <-> p x = true) ->
      span p l = Some (b, x, e) ->
        ex P l <-> ex P b \/ P x \/ ex P e.
(* begin hide *)
Proof.
  intros. apply span_spec in H0.
  rewrite H0, ex_app, ex_cons.
  reflexivity.
Qed.
(* end hide *)

Lemma ex_interesting :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (hb : B) (tb : list B),
    ex (fun a : A => ex (fun b : B => P (a, b)) tb) la ->
    ex (fun a : A => ex (fun b : B => P (a, b)) (hb :: tb)) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn.
    contradiction.
    intros. destruct H.
      left. right. assumption.
      right. cbn in IHta. apply IHta. assumption.
Qed.
(* end hide *)

Lemma ex_zip :
  forall (A B : Type) (P : A * B -> Prop) (la : list A) (lb : list B),
    ex P (zip la lb) ->
      ex (fun a : A => ex (fun b : B => P (a, b)) lb) la.
(* begin hide *)
Proof.
  induction la as [| ha ta]; cbn; intros.
    assumption.
    induction lb as [| hb tb]; inversion H; subst; clear H.
      left. left. assumption.
      specialize (IHta _ H0). right.
        apply ex_interesting. assumption.
Qed.
(* end hide *)

Lemma ex_pmap :
  forall (A B : Type) (f : A -> option B) (P : B -> Prop) (l : list A),
    ex P (pmap f l) <->
      ex (fun x : A => match f x with | Some b => P b | _ => False end) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite IHt.
      reflexivity.
      tauto.
Qed.
(* end hide *)

Lemma ex_intersperse :
  forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
    ex P (intersperse x l) <->
    ex P l \/ (P x /\ 2 <= length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    firstorder lia.
    destruct (intersperse x t) eqn: eq; cbn in *.
      rewrite IHt. firstorder. destruct t; cbn in eq.
        inversion H2. inversion H4.
        destruct (intersperse x t); inversion eq.
      rewrite IHt. firstorder. destruct t; cbn in *.
        inversion eq.
        right. split.
          assumption.
          apply le_n_S, le_n_S, le_0_n.
Qed.
(* end hide *)

End Recursives.

(** * Rozstrzyganie predykatów i relacji na listach (TODO) *)

Fixpoint list_eq_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| [], _ => false
| _, [] => false
| h1 :: t1, h2 :: t2 => eq_dec h1 h2 && list_eq_dec eq_dec t1 t2
end.

Lemma list_eq_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (l1 = l2) (list_eq_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
    1-3: constructor; reflexivity + inversion 1.
    destruct (eq_dec_spec h1 h2); cbn.
      destruct (IHt1 t2); constructor.
        f_equal; assumption.
        intro. inv H. contradiction.
      constructor. intro. inv H. contradiction.
Qed.
(* end hide *)

Definition elem_dec
  {A : Type} (eq_dec : A -> A -> bool) (x : A) (l : list A) : bool :=
    any (eq_dec x) l.

Lemma elem_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (x : A) (l : list A),
      reflect (elem x l) (elem_dec eq_dec x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor. inversion 1.
    destruct (eq_dec_spec x h).
      subst. cbn. constructor. left.
      cbn. unfold elem_dec in IHt. destruct IHt; constructor.
        right. assumption.
        intro. apply n0. inv H.
          contradiction.
          assumption.
Qed.
(* end hide *)

Lemma In_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (x : A) (l : list A),
      reflect (In x l) (elem_dec eq_dec x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor. inversion 1.
    destruct (eq_dec_spec x h); cbn.
      constructor. left. assumption.
      unfold elem_dec in IHt. destruct IHt; constructor.
        right. assumption.
        intro. apply n0. inv H.
          contradiction.
          assumption.
Qed.
(* end hide *)

Fixpoint Dup_dec
  {A : Type} (eq_dec : A -> A -> bool) (l : list A) : bool :=
match l with
| [] => false
| h :: t => elem_dec eq_dec h t || Dup_dec eq_dec t
end.

Lemma Dup_dec_spec :
  forall
    (A : Type) (eq_dec : A -> A -> bool)
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l : list A),
      reflect (Dup l) (Dup_dec eq_dec l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor. inversion 1.
    destruct (elem_dec_spec eq_dec_spec h t); cbn.
      constructor. left. assumption.
      destruct IHt; constructor.
        right. assumption.
        intro. apply n0. inv H.
          contradiction.
          assumption.
Qed.
(* end hide *)

Lemma Exists_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A),
      reflect (Exists P l) (any p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor. inversion 1.
    destruct (P_dec_spec h); cbn.
      constructor. left. assumption.
      destruct IHt; constructor.
        right. assumption.
        intro. apply n0. inv H.
          contradiction.
          assumption.
Qed.
(* end hide *)

Lemma Forall_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A),
      reflect (Forall P l) (all p l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    do 2 constructor.
    destruct (P_dec_spec h); cbn.
      destruct IHt; constructor.
        constructor; assumption.
        intro. apply n. inv H. assumption.
      constructor. intro. inv H. contradiction.
Qed.
(* end hide *)

Definition Exactly_dec
  {A : Type} (p : A -> bool) (n : nat) (l : list A) : bool :=
    count p l =? n.

Lemma Exactly_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A) (n : nat),
      reflect (Exactly P n l) (Exactly_dec p n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; constructor.
      constructor.
      inversion 1.
    destruct (P_dec_spec h).
      destruct n as [| n']; cbn.
        constructor. intro. inv H. contradiction.
        unfold Exactly_dec in IHt. destruct (IHt n'); constructor.
          constructor; assumption.
          intro. inv H; contradiction.
      unfold Exactly_dec in IHt. destruct (IHt n); constructor.
        constructor; assumption.
        intro. inv H; contradiction.
Qed.
(* end hide *)

Definition AtLeast_dec
  {A : Type} (p : A -> bool) (n : nat) (l : list A) : bool :=
    n <=? count p l.

Lemma AtLeast_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A) (n : nat),
      reflect (AtLeast P n l) (AtLeast_dec p n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; constructor.
      constructor.
      inversion 1.
    unfold AtLeast_dec. cbn. destruct (P_dec_spec h).
      destruct n as [| n']; cbn.
        do 2 constructor.
        unfold AtLeast_dec in IHt. destruct (IHt n'); constructor.
          constructor; assumption.
          intro. inv H.
            contradiction.
            apply (AtLeast_le _ _ (S n') n') in H2.
              contradiction.
              apply le_S, le_n.
      unfold AtLeast_dec in IHt. destruct (IHt n); constructor.
        constructor; assumption.
        intro. inv H.
          apply n1. constructor.
          contradiction.
          contradiction.
Qed.
(* end hide *)

Definition AtMost_dec
  {A : Type} (p : A -> bool) (n : nat) (l : list A) : bool :=
    count p l <=? n.

Lemma AtMost_dec_spec :
  forall
    {A : Type} {P : A -> Prop} {p : A -> bool}
    (P_dec_spec : forall x : A, reflect (P x) (p x))
    (l : list A) (n : nat),
      reflect (AtMost P n l) (AtMost_dec p n l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    constructor. constructor.
    destruct (P_dec_spec h).
      destruct n as [| n']; cbn.
        constructor. intro. inv H. contradiction.
        unfold AtMost_dec in IHt. destruct (IHt n'); constructor.
          constructor; assumption.
          intro. inv H; contradiction.
      unfold AtMost_dec in IHt. destruct (IHt n); constructor.
        constructor; assumption.
        intro. inv H.
          contradiction.
          apply n1. apply AtMost_le with n2.
            assumption.
            apply le_S, le_n.
Qed.
(* end hide *)

Fixpoint Sublist_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l2 with
| [] => false
| h2 :: t2 =>
    list_eq_dec eq_dec l1 t2 || Sublist_dec eq_dec l1 t2
end.

Lemma Sublist_dec_spec :
  forall
    (A : Type) (eq_dec : A -> A -> bool)
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Sublist l1 l2) (Sublist_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    destruct l1; constructor; inversion 1.
    destruct (list_eq_dec_spec eq_dec_spec l1 t2); cbn.
      constructor. subst. constructor.
      destruct (IHt2 l1); constructor.
        constructor. assumption.
        intro. inv H; contradiction.
Qed.
(* end hide *)

Fixpoint Prefix_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], _ => true
| _, [] => false
| h1 :: t1, h2 :: t2 => eq_dec h1 h2 && Prefix_dec eq_dec t1 t2
end.

Lemma Prefix_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Prefix l1 l2) (Prefix_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    do 2 constructor.
    destruct l2 as [| h2 t2].
      constructor. inversion 1.
      destruct (eq_dec_spec h1 h2); cbn.
        destruct (IHt1 t2); constructor.
          subst. constructor. assumption.
          intro. inv H. contradiction.
        constructor. intro. inv H. contradiction.
Qed.
(* end hide *)

Definition Suffix_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
    Prefix_dec eq_dec (rev l1) (rev l2).

Lemma Suffix_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Suffix l1 l2) (Suffix_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros.
  pose (Prefix_Suffix _ (rev l1) (rev l2)).
  rewrite 2!rev_rev in i.
  unfold Suffix_dec.
  destruct (Prefix_dec_spec eq_dec_spec (rev l1) (rev l2)).
    constructor. rewrite <- i. assumption.
    constructor. intro. rewrite <-i in H. contradiction.
Qed.
(* end hide *)

Fixpoint Subseq_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], _ => true
| _, [] => false
| h1 :: t1, h2 :: t2 =>
    (eq_dec h1 h2 && Subseq_dec eq_dec t1 t2) ||
    Subseq_dec eq_dec l1 t2
end.

Lemma Subseq_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Subseq l1 l2) (Subseq_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. revert l1.
  induction l2 as [| h2 t2]; cbn; intro.
    destruct l1; constructor.
      constructor.
      inversion 1.
    destruct l1 as [| h1 t1].
      do 2 constructor.
      destruct (IHt2 (h1 :: t1)).
        rewrite Bool.orb_true_r. do 2 constructor. assumption.
        rewrite Bool.orb_false_r. destruct (eq_dec_spec h1 h2); cbn.
          destruct (IHt2 t1); constructor.
            subst. constructor. assumption.
            intro. inv H; contradiction.
          constructor. intro. inv H; contradiction.
Qed.
(* end hide *)

Fixpoint Incl_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1 with
| [] => true
| h :: t => elem_dec eq_dec h l2 && Incl_dec eq_dec t l2
end.

Lemma Incl_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Incl l1 l2) (Incl_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intro.
    constructor. unfold Incl. inversion 1.
    destruct (elem_dec_spec eq_dec_spec h l2); cbn.
      destruct (IHt l2); constructor; unfold Incl in *.
        intros. inv H.
          assumption.
          apply i. assumption.
        intro. apply n. intros. apply H. right. assumption.
      constructor. unfold Incl. intro. apply n, H. left.
Qed.
(* end hide *)

Definition SetEquiv_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
    Incl_dec eq_dec l1 l2 && Incl_dec eq_dec l2 l1.

Lemma SetEquiv_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (SetEquiv l1 l2) (SetEquiv_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. unfold SetEquiv_dec.
  destruct (Incl_dec_spec eq_dec_spec l1 l2); cbn.
    destruct (Incl_dec_spec eq_dec_spec l2 l1); constructor.
      rewrite SetEquiv_Incl. split; assumption.
      rewrite SetEquiv_Incl. destruct 1; contradiction.
    constructor. rewrite SetEquiv_Incl. destruct 1; contradiction.
Qed.
(* end hide *)

Fixpoint Permutation_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1 with
| [] => isEmpty l2
| h :: t =>
  match removeFirst (eq_dec h) l2 with
  | None => false
  | Some (_, l2') => Permutation_dec eq_dec t l2'
  end
end.

Lemma Permutation_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l1 l2 : list A),
      reflect (Permutation l1 l2) (Permutation_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    destruct l2; constructor.
      reflexivity.
      intro. apply Permutation_length in H. inv H.
    destruct (removeFirst (eq_dec h) l2) eqn: Heq.
      destruct p. assert (h = a); subst.
        apply removeFirst_satisfies in Heq. destruct (eq_dec_spec h a).
          assumption.
          congruence.
        apply Permutation_removeFirst in Heq. destruct (IHt l); constructor.
          rewrite Heq, p. reflexivity.
          intro. rewrite Heq in H. apply Permutation_cons_inv in H.
            contradiction.
      constructor. intro. assert (elem h l2).
        rewrite <- Permutation_elem.
          left.
          exact H.
        assert (eq_dec h h = false).
          apply elem_removeFirst_None with l2; assumption.
          destruct (eq_dec_spec h h).
            congruence.
            contradiction.
Qed.
(* end hide *)

Fixpoint Cycle_dec_aux
  {A : Type} (eq_dec : A -> A -> bool) (n : nat) (l1 l2 : list A) : bool :=
match n with
| 0 => list_eq_dec eq_dec l1 l2
| S n' =>
    list_eq_dec eq_dec l1 (drop n l2 ++ take n l2) ||
    Cycle_dec_aux eq_dec n' l1 l2
end.

Definition Cycle_dec
  {A : Type} (eq_dec : A -> A -> bool) (l1 l2 : list A) : bool :=
    Cycle_dec_aux eq_dec (length l1) l1 l2.

Lemma Cycle_dec_aux_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (m : nat) (l1 l2 : list A),
      reflect
        (exists n : nat, n <= m /\ l1 = drop n l2 ++ take n l2)
        (Cycle_dec_aux eq_dec m l1 l2).
(* begin hide *)
Proof.
  induction m as [| m']; cbn; intros.
    destruct (list_eq_dec_spec eq_dec_spec l1 l2); constructor.
      subst. exists 0. split.
        apply le_0_n.
        rewrite drop_0, take_0, app_nil_r. reflexivity.
      destruct 1 as (n' & H1 & H2). inv H1.
        rewrite drop_0, take_0, app_nil_r in n. contradiction.
    destruct (list_eq_dec_spec eq_dec_spec l1
                               (drop (S m') l2 ++ take (S m') l2)); cbn.
      constructor. exists (S m'). split.
        reflexivity.
        assumption.
      destruct (IHm' l1 l2); constructor.
        firstorder.
        destruct 1 as (n' & H1 & H2). apply n0. exists n'. split.
          assert (n' <> S m').
            intro. subst. contradiction.
            lia.
          assumption.
Qed.
(* end hide *)

Lemma Cycle_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (m : nat) (l1 l2 : list A),
      reflect (Cycle l1 l2) (Cycle_dec eq_dec l1 l2).
(* begin hide *)
Proof.
  intros. unfold Cycle_dec.
  destruct (Cycle_dec_aux_spec eq_dec_spec (length l1) l1 l2); constructor.
    rewrite Cycle_spec. assumption.
    intro. apply n. rewrite <- Cycle_spec. assumption.
Qed.
(* end hide *)

Definition Palindrome_dec
  {A : Type} (eq_dec : A -> A -> bool) (l : list A) : bool :=
    list_eq_dec eq_dec l (rev l).

Lemma Palindrome_dec_spec :
  forall
    {A : Type} {eq_dec : A -> A -> bool}
    (eq_dec_spec : forall x y : A, reflect (x = y) (eq_dec x y))
    (l : list A),
      reflect (Palindrome l) (Palindrome_dec eq_dec l).
(* begin hide *)
Proof.
  intros. unfold Palindrome_dec.
  destruct (list_eq_dec_spec eq_dec_spec l (rev l)); constructor.
    rewrite Palindrome_spec. assumption.
    intro. apply n. rewrite <- Palindrome_spec. assumption.
Qed.
(* end hide *)

(** * Znajdowanie wszystkich podstruktur (TODO) *)

(** ** Podlisty/podtermy *)

Module sublists.

Fixpoint sublists {A : Type} (l : list A) : list (list A) :=
match l with
| [] => []
| h :: t => t :: sublists t
end.

Lemma sublists_spec :
  forall {A : Type} (l1 l2 : list A),
    Sublist l1 l2 -> elem l1 (sublists l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    constructor.
    right. assumption.
Qed.
(* end hide *)

Lemma sublists_spec' :
  forall {A : Type} (l1 l2 : list A),
    elem l1 (sublists l2) -> Sublist l1 l2.
(* begin hide *)
Proof.
  induction l2 as [| h2 t2]; cbn.
    inversion 1.
    inversion 1; subst.
      constructor.
      constructor. apply IHt2. assumption.
Qed.
(* end hide *)

End sublists.

(** ** Sufiksy *)

Module suffixes.

Fixpoint suffixes {A : Type} (l : list A) : list (list A) :=
  l ::
match l with
| [] => []
| h :: t => suffixes t
end.

Lemma suffixes_spec :
  forall {A : Type} (l1 l2 : list A),
    Suffix l1 l2 -> elem l1 (suffixes l2).
(* begin hide *)
Proof.
  induction 1.
    destruct l; constructor.
    cbn. constructor. assumption.
Qed.
(* end hide *)

Lemma suffixes_spec' :
  forall {A : Type} (l1 l2 : list A),
    elem l1 (suffixes l2) -> Suffix l1 l2.
(* begin hide *)
Proof.
  induction l2 as [| h2 t2]; cbn.
    inversion 1; subst.
      constructor.
      inversion H2.
    inversion 1; subst.
      constructor.
      constructor. apply IHt2. assumption.
Qed.
(* end hide *)

End suffixes.

(** ** Prefiksy *)

Module prefixes.

Import suffixes.

Fixpoint prefixes {A : Type} (l : list A) : list (list A) :=
  [] ::
match l with
| [] => []
| h :: t => map (cons h) (prefixes t)
end.

Lemma prefixes_spec :
  forall {A : Type} (l1 l2 : list A),
    Prefix l1 l2 -> elem l1 (prefixes l2).
(* begin hide *)
Proof.
  induction 1.
    destruct l; constructor.
    cbn. constructor. apply elem_map. assumption.
Qed.
(* end hide *)

Lemma elem_map_cons :
  forall {A : Type} (h1 h2 : A) (t1 : list A) (t2 : list (list A)),
    elem (h1 :: t1) (map (cons h2) t2) -> h1 = h2.
(* begin hide *)
Proof.
  intros until t2. revert h1 h2 t1.
  induction t2 as [| h t]; cbn; intros.
    inv H.
    inv H.
      reflexivity.
      apply (IHt _ _ _ H2).
Qed.
(* end hide *)

Lemma prefixes_spec' :
  forall {A : Type} (l1 l2 : list A),
    elem l1 (prefixes l2) -> Prefix l1 l2.
(* begin hide *)
Proof.
  intros until l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inv H.
      constructor.
      inv H2.
    inv H.
      constructor.
      destruct l1 as [| h1 t1].
        constructor.
        replace h1 with h2 in *.
          constructor. apply IHt2. apply elem_map_conv' in H2.
            assumption.
            inversion 1; auto.
          apply elem_map_cons in H2. symmetry. assumption.
Qed.
(* end hide *)

End prefixes.

(** ** Podciągi *)

Module subseqs.

Fixpoint subseqs {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| h :: t => map (cons h) (subseqs t) ++ subseqs t
end.

Compute subseqs [1; 2; 3; 4; 5].

Lemma Subseq_subseqs :
  forall (A : Type) (l1 l2 : list A),
    Subseq l1 l2 -> elem l1 (subseqs l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn.
      constructor.
      apply elem_app_r. assumption.
    apply elem_app_l, elem_map. assumption.
    apply elem_app_r. assumption.
Qed.
(* end hide *)

Lemma subseqs_Subseq :
  forall (A : Type) (l1 l2 : list A),
    elem l1 (subseqs l2) -> Subseq l1 l2.
(* begin hide *)
Proof.
  intros A l1 l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inversion H; subst.
      constructor.
      inversion H2.
    apply elem_app in H. destruct H.
      rewrite elem_map_conv in H. destruct H as (x & Heq & Hel).
        subst. constructor. apply IHt2. assumption.
      constructor. apply IHt2, H.
Qed.
(* end hide *)

End subseqs.

(** ** Podzbiory *)

Module subsets.

(* begin hide *)
(* TODO: znaleźć specyfikację dla [subsets] *)
(* end hide *)

Fixpoint subsets {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| h :: t => subsets t ++ map (cons h) (subsets t)
end.

Import prefixes.

End subsets.

(** ** Cykle *)

Module cycles.

Fixpoint cycles_aux {A : Type} (n : nat) (l : list A) : list (list A) :=
match n with
| 0 => []
| S n' => cycle n l :: cycles_aux n' l
end.

Compute cycles_aux 0 [1; 2; 3; 4; 5].
Compute cycles_aux 5 [1; 2; 3; 4; 5].

Definition cycles {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| _ => cycles_aux (length l) l
end.

Compute cycles [].
Compute cycles [1].
Compute cycles [1; 2; 3; 4; 5].

Lemma Cycle_cycles_aux :
  forall (A : Type) (l1 l2 : list A),
    Cycle l1 l2 -> forall n : nat,
      elem l1 (cycles_aux (S (length l2) + n) l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    induction l as [| h t]; cbn; intros.
      constructor.
      destruct (IHt n).
Admitted.
(* end hide *)

End cycles.

(** * Permutacje (TODO) *)

(** ** Permutacje jako ciągi transpozycji *)

Module Transpositions.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_refl : forall l : list A, Perm l l
| Perm_transp :
    forall (x y : A) (l1 l2 l3 l4 : list A),
      Perm (l1 ++ x :: l2 ++ y :: l3) l4 ->
        Perm (l1 ++ y :: l2 ++ x :: l3) l4.

Lemma Perm_cons :
  forall {A : Type} (h : A) (t1 t2 : list A),
    Perm t1 t2 -> Perm (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply (Perm_transp x y (h :: l1)). cbn. assumption.
Qed.
(* end hide *)

Lemma Perm_trans :
  forall {A : Type} {l1 l2 l3 : list A},
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  induction 1; intro.
    assumption.
    constructor. apply IHPerm. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_transp x y [] []). cbn. constructor.
    eapply Perm_trans; eassumption.
Qed.
(* end hide *)

Lemma Permutation_transpose :
  forall {A : Type} {x y : A} {l1 l2 l3 : list A},
    Permutation (l1 ++ x :: l2 ++ y :: l3) (l1 ++ y :: l2 ++ x :: l3).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    {
      change (x :: l2 ++ y :: l3) with ((x :: l2) ++ y :: l3).
      change (y :: l2 ++ x :: l3) with ((y :: l2) ++ x :: l3).
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite (Permutation_app_comm _ l3).
      rewrite (Permutation_app_comm _ l2).
      cbn. constructor.
      apply Permutation_app_comm.
    }
    constructor. apply IHt1.
Qed.
(* end hide *)

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite Permutation_transpose. assumption.
Qed.
(* end hide *)

End Transpositions.

(** ** Permutacje jako ciągi transpozycji v2 *)

Module InductiveTranspositions.

Inductive Transposition {A : Type} : list A -> list A -> Prop :=
| Transposition' :
    forall (l1 : list A) (x : A) (l2 : list A) (y : A) (l3 : list A),
      Transposition (l1 ++ x :: l2 ++ y :: l3) (l1 ++ y :: l2 ++ x :: l3).

Inductive Transposition2 {A : Type} : list A -> list A -> Prop :=
| Transposition2' :
    forall (l1 : list A) (x : A) (l2 : list A) (y : A) (l3 r1 r2: list A),
      r1 = l1 ++ x :: l2 ++ y :: l3 ->
      r2 = l1 ++ y :: l2 ++ x :: l3 ->
        Transposition2 r1 r2.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_refl : forall l : list A, Perm l l
| Perm_step_trans :
    forall l1 l2 l3 : list A,
      Transposition l1 l2 -> Perm l2 l3 -> Perm l1 l3.

Lemma Perm_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Perm l1 l2 -> Perm (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    eapply Perm_step_trans.
      2: eassumption.
      destruct H as [l11 y l12 z l13].
        apply (Transposition' (x :: l11) y l12 z l13).
Qed.
(* end hide *)

Lemma Perm_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  intros until 1. revert l3.
  induction H; intros.
    assumption.
    econstructor.
      exact H.
      apply IHPerm. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_step_trans _ (x :: y :: l)).
      apply (Transposition' [] y [] x l).
      constructor.
    eapply Perm_trans; eassumption.
Qed.
(* end hide *)

Lemma Perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite <- IHPerm. destruct H as [l11 x l12 y l13].
      apply Transpositions.Permutation_transpose.
Qed.
(* end hide *)

Lemma Perm_spec :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 <-> Permutation l1 l2.
(* begin hide *)
Proof.
  split.
    apply Perm_Permutation.
    apply Permutation_Perm.
Qed.
(* end hide *)

Lemma Perm_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Perm l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite <- IHPerm. destruct H as [l11 x l12 y l13].
      repeat (rewrite count_app; cbn).
      destruct (p x), (p y); rewrite ?plus_n_Sm; reflexivity.
Qed.
(* end hide *)

End InductiveTranspositions.

(** ** Permutacje jako ciągi transpozycji elementów sąsiednich *)

Module AdjacentTranspositions.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_refl : forall l : list A, Perm l l
| Perm_steptrans :
    forall (x y : A) (l1 l2 l3 : list A),
      Perm (l1 ++ y :: x :: l2) l3 -> Perm (l1 ++ x :: y :: l2) l3.

Lemma Perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    apply Permutation_refl.
    rewrite <- IHPerm. apply Permutation_app.
      reflexivity.
      constructor.
Qed.
(* end hide *)

Lemma Perm_cons :
  forall {A : Type} (x : A) {l1 l2 : list A},
    Perm l1 l2 -> Perm (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply (Perm_steptrans x0 y (x :: l1) l2). cbn. assumption.
Qed.
(* end hide *)

Lemma Perm_trans :
  forall {A : Type} {l1 l2 l3 : list A},
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  induction 1; intro H23.
    assumption.
    apply (Perm_steptrans x y l1 l2), IHPerm, H23.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_steptrans y x [] l). cbn. constructor.
    eapply Perm_trans; eassumption.
Qed.
(* end hide *)

End AdjacentTranspositions.

(** ** Permutacje jako ciągi transpozycji elementów sąsiednich v2 *)

Module Exchange.

Definition exchange {A : Type} (l1 l2 : list A) : Prop :=
  exists (x y : A) (r1 r2 : list A),
    l1 = r1 ++ x :: y :: r2 /\
    l2 = r1 ++ y :: x :: r2.

Inductive Perm {A : Type} : list A -> list A -> Prop :=
| Perm_refl : forall l : list A, Perm l l
| Perm_step_trans :
    forall l1 l2 l3 : list A,
      exchange l1 l2 -> Perm l2 l3 -> Perm l1 l3.

Lemma Perm_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    Perm l1 l2 -> Perm (x :: l1) (x :: l2).
(* begin hide *)
Proof.
  induction 1.
    constructor.
    destruct H as (y & z & r1 & r2 & eq1 & eq2); subst.
      apply (Perm_step_trans) with (x :: r1 ++ z :: y :: r2).
        red. exists y, z, (x :: r1), r2. split; reflexivity.
        assumption.
Qed.
(* end hide *)

Lemma Perm_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3.
(* begin hide *)
Proof.
  intros until 1. revert l3.
  induction H; intros.
    assumption.
    econstructor.
      exact H.
      apply IHPerm. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  induction 1.
    constructor.
    apply Perm_cons. assumption.
    apply (Perm_step_trans _ (x :: y :: l)).
      red. exists y, x, [], l. cbn. split; trivial.
      apply Perm_refl.
    apply Perm_trans with l'; assumption.
Qed.
(* end hide *)

Lemma Perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    rewrite <- IHPerm.
      destruct H as (x & y & r1 & r2 & eq1 & eq2). subst.
      apply Permutation_app_l. constructor.
Qed.
(* end hide *)

Lemma Perm_spec :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 <-> Permutation l1 l2.
(* begin hide *)
Proof.
  split.
    apply Perm_Permutation.
    apply Permutation_Perm.
Qed.
(* end hide *)

Lemma Perm_count :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    Perm l1 l2 -> count p l1 = count p l2.
(* begin hide *)
Proof.
  induction 1.
    reflexivity.
    destruct H as (x & y & r1 & r2 & eq1 & eq2). subst.
      rewrite <- IHPerm, !count_app. f_equal. cbn.
      destruct (p x), (p y); reflexivity.
Qed.
(* end hide *)

End Exchange.

(** ** Permutacje za pomocą liczenia właściwości *)

Module Exactly.

Ltac inv H := inversion H; subst; clear H.

Definition Perm {A : Type} (l1 l2 : list A) : Prop :=
  forall (P : A -> Prop) (n : nat),
    Exactly P n l1 <-> Exactly P n l2.

Lemma Permutation_Exactly :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat),
        Exactly P n l1 -> Exactly P n l2.
(* begin hide *)
Proof.
  induction 1; intros.
    assumption.
    inv H0.
      constructor.
        assumption.
        apply IHPermutation. assumption.
      constructor 3.
        assumption.
        apply IHPermutation. assumption.
    inv H.
      inv H4; repeat constructor; assumption.
      inv H4; repeat constructor; assumption.
    apply IHPermutation2, IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  split.
    apply Permutation_Exactly. assumption.
    apply Permutation_Exactly. symmetry. assumption.
Qed.
(* end hide *)

Lemma Perm_front_ex :
  forall {A : Type} {h : A} {t l : list A},
    Perm (h :: t) l ->
      exists l1 l2 : list A,
        l = l1 ++ h :: l2 /\ Perm t (l1 ++ l2).
(* begin hide *)
Proof.
  intros until 1.
  revert h t H.
  induction l as [| h' t']; intros.
    admit.
    unfold Perm in H.
Admitted.
(* end hide *)

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; intros.
    destruct l2 as [| h2 t2].
      constructor.
      {
        unfold Perm in H. destruct (H (fun x => x = h2) 0).
        rewrite Exactly_0_cons in *.
        destruct (H0 ltac:(constructor)).
        contradiction.
      }
    {
      apply Perm_front_ex in H.
      destruct H as (l1 & l3 & H1 & H2). subst.
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite Permutation_app_comm.
      apply IHt1.
      assumption.
    }
Qed.
(* end hide *)

End Exactly.

(** ** Permutacje za pomocą liczenia właściwości v2 *)

Module AtLeast.

Ltac inv H := inversion H; subst; clear H.

Definition Perm {A : Type} (l1 l2 : list A) : Prop :=
  forall (P : A -> Prop) (n : nat),
    (AtLeast P n l1 <-> AtLeast P n l2).

#[global] Hint Constructors AtLeast : core.

Lemma Permutation_AtLeast :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 ->
      forall (P : A -> Prop) (n : nat),
        AtLeast P n l1 -> AtLeast P n l2.
(* begin hide *)
Proof.
  induction 1; intros.
    assumption.
    inv H0; auto.
    inv H.
      auto.
      inv H4; auto.
      inv H2; auto.
    apply IHPermutation2, IHPermutation1. assumption.
Qed.
(* end hide *)

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  split.
    apply Permutation_AtLeast. assumption.
    apply Permutation_AtLeast. symmetry. assumption.
Qed.
(* end hide *)

Lemma AtLeast_1 :
  forall {A : Type} {P : A -> Prop} {l : list A},
    AtLeast P 1 l ->
      exists (x : A) (l1 l2 : list A),
        P x /\ l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  induction l as [| h t]; intros.
    inv H.
    inv H.
      exists h, [], t. auto.
      destruct (IHt H2) as (x & l1 & l2 & IH1 & IH2).
        subst. exists x, (h :: l1), l2. auto.
Qed.
(* end hide *)

Lemma AtLeast_app_comm' :
  forall {A : Type} {P : A -> Prop} {n : nat} {l1 l2 : list A},
    AtLeast P n (l1 ++ l2) <-> AtLeast P n (l2 ++ l1).
(* begin hide *)
Proof.
  split; intro; apply AtLeast_app_comm; assumption.
Qed.
(* end hide *)

Lemma AtLeast_cons_app :
  forall
    {A : Type} {P : A -> Prop} {n : nat}
    (x : A) (l1 l2 : list A),
      AtLeast P n (l1 ++ x :: l2) <->
      AtLeast P n (x :: l1 ++ l2).
(* begin hide *)
Proof.
  intros.
  change (x :: l1 ++ l2) with ((x :: l1) ++ l2).
  rewrite AtLeast_app_comm'. cbn.
  rewrite !AtLeast_cons.
  rewrite !(@AtLeast_app_comm' _ _ _ l1 l2).
  reflexivity.
Qed.
(* end hide *)

Lemma Perm_front_ex :
  forall {A : Type} {h : A} {t l : list A},
    Perm (h :: t) l ->
      exists l1 l2 : list A,
        l = l1 ++ h :: l2 /\ Perm t (l1 ++ l2).
(* begin hide *)
Proof.
  intros.
  unfold Perm in H.
  assert (AtLeast (fun x => x = h) 1 l).
    apply H. auto.
  apply AtLeast_1 in H0.
  destruct H0 as (x & l1 & l2 & H1 & H2); subst.
  exists l1, l2.
  split.
    reflexivity.
    {
      red. intros.
      destruct (H P n).
      destruct (H P (S n)).
      firstorder.
        specialize (H0 ltac:(auto)).
        specialize (H1 H0).
        inv H1.
          auto.
          apply AtLeast_cons' with h.
            apply AtLeast_cons_app. apply H2. auto.
          assert (AtLeast P n (h :: l1 ++ l2)).
            apply AtLeast_cons_app. auto.
            inv H1.
              auto.
              apply AtLeast_cons' with h.
                apply AtLeast_cons_app. apply H2. auto.
              assumption.
          assert (AtLeast P n (h :: t)).
            apply H1. apply AtLeast_cons_app. constructor. assumption.
            inv H5.
              auto.
              apply AtLeast_cons' with h. apply H3.
                apply AtLeast_app_comm. cbn. constructor.
                  assumption.
                  apply AtLeast_app_comm. assumption.
              assumption.
    }
Qed.
(* end hide *)

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; intros.
    destruct l2 as [| h2 t2].
      constructor.
      {
        unfold Perm in H. destruct (H (fun x => x = h2) 1).
        specialize (H1 ltac:(auto)). inv H1.
      }
    { unfold Perm in H.
      apply Perm_front_ex in H.
      destruct H as (l1 & l3 & H1 & H2). subst.
      rewrite Permutation_app_comm.
      cbn. constructor.
      rewrite Permutation_app_comm.
      apply IHt1.
      assumption.
    }
Qed.
(* end hide *)

#[global] Hint Constructors Exactly : core.

(* TODO *) Lemma AtLeast_Exactly :
  forall {A : Type} (l1 l2 : list A),
    (forall (P : A -> Prop) (n : nat),
      AtLeast P n l1 <-> AtLeast P n l2)
    <->
    (forall (P : A -> Prop) (n : nat),
      Exactly P n l1 <-> Exactly P n l2).
(* begin hide *)
Proof.
  split.
    split; intros.
      induction H0.
        destruct l2.
          auto.
          destruct (H (fun x => x = a) 1).
            specialize (H1 ltac:(auto)). inv H1.
Abort.
(* end hide *)

End AtLeast.

(** ** Permutacje, jeszcze dziwniej *)

From Typonomikon Require H2.
Require Import Equality.

Module PermWeird.

Import H2.

Inductive Elem {A : Type} (x : A) : list A -> Type :=
| Z : forall l : list A, Elem x (x :: l)
| S : forall {t : list A}, Elem x t -> forall h : A, Elem x (h :: t).

Arguments Z {A x} _.
Arguments S {A x t} _ _.

Definition Perm {A : Type} (l1 l2 : list A) : Type :=
  forall x : A, iso (Elem x l1) (Elem x l2).

(* begin hide *)
(*Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    red. intro. split with (coel := id) (coer := id).
      1-2: reflexivity.
    red. intro y. unfold Perm in *. destruct (IHPermutation y).
      esplit. Unshelve. all: cycle 4. 1-4: intro H'.
        inv H'.
          left.
          right. apply coel. assumption.
        inv H'.
          left.
          right. apply coer. assumption.
        dependent induction H'; cbn; congruence.
        dependent induction H'; cbn; congruence.
    red. intro z. esplit. Unshelve. all: cycle 3. 1-4: intro H'.
        inv H'.
          right. left.
          inv X.
            left.
            right. right. assumption.
        inv H'.
          right. left.
          inv X.
            left.
            right. right. assumption.
        do 2 (dependent induction H'; cbn; try congruence).
        do 2 (dependent induction H'; cbn; try congruence).
    intro H'. eapply iso_trans.
      apply IHPermutation1.
      apply IHPermutation2.
Qed.
 *)

(* Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  unfold Perm.
  induction l1 as [| h1 t1]; intros.
    destruct l2 as [| h2 t2].
      constructor.
      specialize (H h2). destruct H.
        clear -coer. specialize (coer ltac:(left)). inv coer.
    destruct l2 as [| h2 t2].
      specialize (H h1). destruct H.
        clear -coel. specialize (coel ltac:(left)). inv coel.
Admitted.
 *)
(* end hide *)

End PermWeird.

(** ** Permutacje za pomocą liczenia właściwości rozstrzygalnych *)

Module Count.

Definition perm {A : Type} (l1 l2 : list A) : Prop :=
  forall p : A -> bool, count p l1 = count p l2.

Lemma count_ex :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p l = 0 \/
    exists (x : A) (l1 l2 : list A),
      p x = true /\ l = l1 ++ x :: l2.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    left. reflexivity.
    destruct IHt.
      destruct (p h) eqn: Hph.
        right. exists h, [], t. split; trivial.
        left. assumption.
      destruct H as (x & l1 & l2 & eq1 & eq2); subst.
        destruct (p h) eqn: Hph.
          right. exists h, [], (l1 ++ x :: l2). split; trivial.
          right. exists x, (h :: l1), l2. cbn. split; trivial.
Qed.
(* end hide *)

Import Exchange.

Lemma Perm_perm :
  forall (A : Type) (l1 l2 : list A),
    Perm l1 l2 -> perm l1 l2.
(* begin hide *)
Proof.
  induction 1; cbn.
    red. reflexivity.
    destruct H as (x & y & r1 & r2 & eq1 & eq2); subst.
      unfold perm in *. intro. rewrite <- (IHPerm p).
      rewrite 2!count_app. cbn.
      destruct (p x), (p y); reflexivity.
Qed.
(* end hide *)

Lemma perm_Perm :
  forall (A : Type) (l1 l2 : list A),
    perm l1 l2 -> Perm l1 l2.
(* begin hide *)
Proof.
  intros. apply Permutation_Perm.
  apply Permutation_count_conv. exact H.
Qed.
(* end hide *)

End Count.

(** ** Znajdowanie permutacji przez selekcję *)

Module perms_select.

Fixpoint select {A : Type} (l : list A) : list (list A * list A) :=
match l with
| [] => [([], [])]
| h :: t => [([], l)] ++ map (fun '(a, b) => (h :: a, b)) (select t)
end.

Lemma select_app :
  forall {A : Type} {l1 l2 : list A},
    select (l1 ++ l2) =
      map (fun '(l, r) => (app l l2, r)) (select l1) ++
      map (fun '(l, r) => (app l1 l, r)) (select l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
Abort.
(* end hide *)

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| h :: t =>
    bind (fun ll =>
      map (fun '(l, r) => l ++ h :: r) (select ll)) (perms t)
end.

(* Compute select [1; 2; 3]. *)
(* Compute perms [1; 2; 3]. *)

Lemma Permutation_bind :
  forall {A B : Type} (f g : A -> list B),
    (forall x : A, Permutation (f x) (g x)) ->
      forall l : list A, Permutation (bind f l) (bind g l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    apply Permutation_app; auto.
Qed.
(* end hide *)

Lemma Permutation_select_app :
  forall {A : Type} {l1 l2 : list A},
    Permutation (select (l1 ++ l2)) (select (l2 ++ l1)).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    replace (l2 ++ h1 :: t1) with ((l2 ++ [h1]) ++ t1).
      rewrite <- IHt1.
Admitted.
(* end hide *)

Lemma map_select :
  forall {A B : Type} (f : A -> B) (l : list A),
    select (map f l)
      =
    map (fun '(L, R) => (map f L, map f R)) (select l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt, !map_map. do 2 f_equal.
Admitted.
(* end hide *)

Lemma Permutation_perms :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (perms l1) (perms l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    do 2 constructor.
    rewrite 2!bind_spec. apply Permutation_join, Permutation_map.
      assumption.
    rewrite !bind_bind. apply Permutation_bind. intro l'.
      rewrite !bind_spec, !map_map, <- !bind_spec. generalize (select l').
        induction l0 as [| h t]; cbn.
          reflexivity.
          apply Permutation_app.
            destruct h.
Admitted.
(* end hide *)

Lemma elem_perms :
  forall (A : Type) (l : list A),
    elem l (perms l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    rewrite bind_spec, elem_join.
      exists (map (fun '(l, r) => l ++ h :: r) (select t)). split.
        destruct t; constructor.
        apply elem_map_conv. exists t. split.
          reflexivity.
          assumption.
Qed.
(* end hide *)

Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
(* begin hide *)
Proof.
  intros. apply Permutation_perms in H.
  rewrite <- (Permutation_elem _ (perms l1) (perms l2)).
    apply elem_perms.
    assumption.
Qed.
(* end hide *)

End perms_select.

Module perms_ins.

(** ** Znajdowanie permutacji przez wstawianie *)

Fixpoint ins {A : Type} (x : A) (l : list A) : list (list A) :=
match l with
| [] => [[x]]
| h :: t => [x :: h :: t] ++ map (cons h) (ins x t)
end.

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| h :: t => bind (ins h) (perms t)
end.

Lemma len_ins :
  forall (A : Type) (x : A) (l : list A),
    length (ins x l) = S (length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_map, IHt. reflexivity.
Qed.
(* end hide *)

Fixpoint nsum (l : list nat) : nat :=
match l with
| [] => 0
| h :: t => h + nsum t
end.

Lemma len_join :
  forall (A : Type) (ll : list (list A)),
    length (join ll) = nsum (map length ll).
(* begin hide *)
Proof.
  induction ll as [| h t]; cbn.
    reflexivity.
    rewrite length_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma len_perms :
  forall (A : Type) (l : list A),
    length (perms l) = fact (length l).
(* begin hide *)
Proof.
  induction l as [| h t].
    cbn. reflexivity.
    cbn [perms]. Search length bind.
    rewrite bind_spec, len_join, map_map.
Abort.
(* end hide *)

Lemma map_ins :
  forall (A B : Type) (f : A -> B) (x : A) (l : list A),
    map (map f) (ins x l) = ins (f x) (map f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    f_equal. rewrite <- IHt, !map_map. cbn. reflexivity.
Qed.
(* end hide *)

Lemma ins_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    l1 = [] \/
    l2 = [] \/
      ins x (l1 ++ l2) =
      map (fun l => app l l2) (ins x l1) ++
      map (app l1) (ins x l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    left. reflexivity.
    induction l2 as [| h2 t2]; cbn.
      right. left. reflexivity.
      do 2 right. decompose [or] IHt2; subst; clear IHt2.
        inversion H.
Abort.
(* end hide *)

Lemma ins_snoc :
  forall (A : Type) (x y : A) (l : list A),
    ins x (snoc y l) =
    snoc (snoc x (snoc y l)) (map (snoc y) (ins x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    f_equal. rewrite IHt. rewrite map_snoc, !map_map.
      cbn. reflexivity.
Qed.
(* end hide *)

Lemma map_ext_eq :
  forall {A B : Type} {f g : A -> B} {l : list A},
    (forall x : A, f x = g x) ->
      map f l = map g l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intro.
    reflexivity.
    rewrite H, (IHt H). reflexivity.
Qed.
(* end hide *)

Lemma ins_rev :
  forall (A : Type) (x : A) (l : list A),
    ins x (rev l) = rev (map rev (ins x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite ins_snoc, IHt.
      rewrite map_rev, map_map, <- map_rev. f_equal.
      rewrite map_rev, map_map. cbn. f_equal.
Qed.
(* end hide *)

Lemma elem_ins :
  forall (A : Type) (x : A) (l : list A),
    elem (x :: l) (ins x l).
(* begin hide *)
Proof.
  destruct l; constructor.
Qed.
(* end hide *)

Lemma elem_perms :
  forall (A : Type) (l : list A),
    elem l (perms l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    constructor.
    rewrite bind_spec, elem_join. exists (ins h t). split.
      apply elem_ins.
      apply elem_map. assumption.
Qed.
(* end hide *)

Lemma Permutation_elem_ins :
  forall (A : Type) (x : A) (l1 l2 : list A),
    elem l2 (ins x l1) -> Permutation (x :: l1) l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn.
    inversion 1; subst.
      reflexivity.
      inversion H2.
    inversion 1; subst.
      reflexivity.
      rewrite elem_map_conv in H2. destruct H2 as (r & Heq & Hel).
        subst. rewrite perm_swap. constructor. apply IHt. assumption.
Qed.
(* end hide *)

Lemma Permutation_bind :
  forall (A B : Type) (f g : A -> list B) (l1 l2 : list A),
    (forall x : A, Permutation (f x) (g x)) ->
      Permutation l1 l2 ->
        Permutation (bind f l1) (bind g l2).
(* begin hide *)
Proof.
  induction 2; cbn.
    constructor.
    apply Permutation_app.
      apply H.
      assumption.
    induction l as [| h t]; cbn.
      rewrite 2!app_nil_r. rewrite Permutation_app_comm.
        apply Permutation_app; apply H.
      rewrite (Permutation_app_comm _ (f h)),
              (Permutation_app_comm _ (g h)).
        rewrite !app_assoc. apply Permutation_app.
          rewrite <- !app_assoc. assumption.
          apply H.
    assert (Permutation (bind f l) (bind f l')).
      rewrite !bind_spec. apply Permutation_join, Permutation_map.
        assumption.
      rewrite H0, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma count_join :
  forall (A : Type) (p : A -> bool) (l : list (list A)),
    count p (join l) = nsum (map (count p) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite count_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma nsum_app :
  forall l1 l2 : list nat,
    nsum (l1 ++ l2) = nsum l1 + nsum l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite IHt1, plus_assoc. reflexivity.
Qed.
(* end hide *)

Fixpoint deepcount
  {A : Type} (p : A -> bool) (l : list (list A)) : nat :=
match l with
| [] => 0
| h :: t => count p h + deepcount p t
end.

Lemma Permutation_bind_ins :
  forall {A : Type} (x y : A) (l : list A),
    Permutation (bind (ins x) (ins y l)) (bind (ins y) (ins x l)).
(* begin hide *)
Proof.
  induction l as [| h t].
    cbn. constructor.
    {
      change (ins x (h :: t)) with ([x :: h :: t] ++ map (cons h) (ins x t)).
      change (ins y (h :: t)) with ([y :: h :: t] ++ map (cons h) (ins y t)).
      rewrite !bind_app.
Admitted.
(* end hide *)

Lemma Permutation_perms :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (perms l1) (perms l2).
(* begin hide *)
Proof.
  induction 1; cbn.
    do 2 constructor.
    rewrite 2!bind_spec. apply Permutation_join, Permutation_map.
      assumption.
    rewrite !bind_bind. apply Permutation_bind.
      2: reflexivity.
      apply Permutation_bind_ins.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_perms' :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
(* begin hide *)
Proof.
  intros. rewrite <- (Permutation_elem _ (perms l1)).
    apply elem_perms.
    apply Permutation_perms. assumption.
Qed.
(* end hide *)

Lemma perms_Permutation :
  forall {A : Type} {l1 l2 : list A},
    elem l1 (perms l2) -> Permutation l1 l2.
(* begin hide *)
Proof.
  intros until l2. revert l1.
  induction l2 as [| h2 t2]; cbn; intros.
    inv H.
      constructor.
      inv H2.
Abort.
(* end hide *)

End perms_ins.

(** ** Znajdowanie permutacji przez cykle *)

Require Import FunctionalExtensionality.
From Typonomikon Require D4.

Module perms_cycles.

Import cycles.
Import D4.

Fixpoint perms {A : Type} (l : list A) : list (list A) :=
match l with
| [] => [[]]
| h :: t => join (map (fun t => cycles (cons h t)) (perms t))
end.

Compute cycles [1; 2].
Compute perms [3].
Compute perms [2; 3].
Compute cycles (map (cons 2) [[3]]).
Compute perms [1; 2; 3].
Compute perms [1; 2; 3; 4].

Fixpoint sum (l : list nat) : nat :=
match l with
| [] => 0
| h :: t => h + sum t
end.

Lemma len_join :
  forall {A : Type} (l : list (list A)),
    length (join l) = sum (map length l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite length_app, IHt. reflexivity.
Qed.
(* end hide *)

Lemma len_cycles_aux :
  forall {A : Type} (l : list A) (n : nat),
    length (cycles_aux n l) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma len_cycles :
  forall {A : Type} (l : list A),
    l <> [] -> length (cycles l) = length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intro.
    contradiction.
    rewrite len_cycles_aux. reflexivity.
Qed.
(* end hide *)

Lemma sum_map_S :
  forall l : list nat,
    sum (map S l) = length l + sum l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    f_equal. rewrite IHt, plus_comm, <- !plus_assoc.
      f_equal. apply plus_comm.
Qed.
(* end hide *)

Lemma sum_replicate :
  forall n m : nat,
    sum (replicate n m) = n * m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    intro. rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma length_perms :
  forall {A : Type} (l : list A),
    length (perms l) = fact (length l) /\
      map length (perms l) =
      replicate (length (perms l)) (length l).
(* begin hide *)
Proof.
  induction l as [| h t].
    cbn. split; reflexivity.
    destruct IHt as [IH1 IH2]. split.
      cbn. rewrite len_join, map_map. cbn.
        replace (fun x => S (length (cycles_aux (length x) (h :: x))))
           with (fun x => S (@length A x)).
          2: {
            apply functional_extensionality. intro.
            rewrite len_cycles_aux. reflexivity.
          }
          {
            rewrite <- map_map, IH2.
            rewrite sum_map_S, length_replicate, sum_replicate.
            rewrite IH1. lia.
          }
      cbn. rewrite len_join, map_map. cbn.
        replace (fun x => S (length (cycles_aux (length x) (h :: x))))
           with (fun x => S (@length A x)).
          2: {
            apply functional_extensionality. intro.
            rewrite len_cycles_aux. reflexivity.
          }
          {
            rewrite <- (map_map _ _ _ _ S). rewrite IH2.
            rewrite sum_map_S, length_replicate, sum_replicate.
            rewrite map_join, map_map. cbn.
Abort.
(* end hide *)

Lemma perms_spec :
  forall {A : Type} (l1 l2 : list A),
    elem l1 (perms l2) -> Permutation l1 l2.
(* begin hide *)
Proof.

Abort.
(* end hide *)

Lemma perms_spec :
  forall {A : Type} (l1 l2 : list A),
    Permutation l1 l2 -> elem l1 (perms l2).
(* begin hide *)
Proof.
  induction 1.
    cbn. constructor.
    cbn. apply elem_join. eexists. split.
      2: { apply elem_map. exact IHPermutation. }
      admit.
    cbn. rewrite map_join, !map_map. apply elem_join. eexists. split.
      admit.
      admit.
Abort.
(* end hide *)

End perms_cycles.

(** * Wut da fuk? (TODO) *)

Module Specs.

Import Count.

Import perms_select.

Lemma perm_perms :
  forall {A : Type} {l1 l2 : list A},
    perm l1 l2 -> elem l1 (perms l2).
(* begin hide *)
Proof.
  intros until l2. revert l1.
  induction l2 as [| h2 t2]; cbn; unfold perm; intros.
    specialize (H (fun _ => true)). destruct l1.
      constructor.
      inv H.
    destruct l1 as [| h1 t1].
      specialize (H (fun _ => true)). cbn in H. inv H.
      cbn in H. rewrite bind_spec, elem_join. eexists. split.
        2: {
          apply elem_map. apply IHt2. red. intro.
          specialize (H p). destruct (p h1) eqn: ph1, (p h2) eqn: ph2.
            inv H. reflexivity.
Abort.
(* end hide *)

End Specs.

(** * Zbiory *)

(** ** Zbiory jako zdeduplikowane permutacje *)

(* Module SetPermDedup. *)

Inductive SameSet {A : Type} : list A -> list A -> Prop :=
| SameSet_nil   : SameSet [] []
| SameSet_cons  :
    forall (h : A) (t1 t2 : list A), SameSet t1 t2 -> SameSet (h :: t1) (h :: t2)
| SameSet_swap  :
    forall (x y : A) (l : list A), SameSet (y :: x :: l) (x :: y :: l)
| SameSet_dedup :
    forall (h : A) (t : list A), SameSet (h :: t) (h :: h :: t)
| SameSet_trans :
    forall l1 l2 l3 : list A, SameSet l1 l2 -> SameSet l2 l3 -> SameSet l1 l3.

Lemma SameSet_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSet l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  induction 1; unfold SetEquiv in *; intro z.
    reflexivity.
    rewrite !elem_cons', IHSameSet. reflexivity.
    rewrite !elem_cons'. firstorder.
    rewrite !elem_cons'. firstorder.
    rewrite IHSameSet1, IHSameSet2. reflexivity.
Qed.
(* end hide *)

Lemma Permutation_SameSet :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> SameSet l1 l2.
(* begin hide *)
Proof.
  induction 1; econstructor; eassumption.
Qed.
(* end hide *)

(* End SetPermDedup. *)

(** ** Zbiory za pomocą [Exists] *)

Module SetExists.

Definition SameSetEx {A : Type} (l1 l2 : list A) : Prop :=
  forall P : A -> Prop, Exists P l1 <-> Exists P l2.

Lemma SameSetEx_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSetEx l1 l2 <-> SetEquiv l1 l2.
(* begin hide *)
Proof.
  unfold SameSetEx, SetEquiv.
  split; intros.
    specialize (H (fun y => x = y)). rewrite !Exists_spec in H.
      firstorder; specialize (H x); specialize (H0 x); cbn in *; firstorder congruence.
    rewrite !Exists_spec. firstorder.
Qed.
(* end hide *)

End SetExists.

(** ** Zbiory za pomocą transpozycji i deduplikacji *)

Module SetTranspositionDedup.

Inductive Transposition {A : Type} : list A -> list A -> Prop :=
| Transposition' :
    forall (x y : A) (l1 l2 l3 : list A),
      Transposition (l1 ++ x :: l2 ++ y :: l3) (l1 ++ y :: l2 ++ x :: l3).

Inductive Dedup {A : Type} : list A -> list A -> Prop :=
| Dedup' :
    forall (x : A) (l1 l2 l3 : list A),
      Dedup (l1 ++ x :: l2 ++ x :: l3) (l1 ++ x :: l2 ++ l3).

Inductive SameSetTD {A : Type} : list A -> list A -> Prop :=
| SameSetTD_refl   :
    forall l : list A, SameSetTD l l
| SameSetTD_transp :
    forall l1 l2 l3 : list A,
      Transposition l1 l2 -> SameSetTD l2 l3 -> SameSetTD l1 l3
| SameSetTD_dedup  :
    forall l1 l2 l3 : list A,
      Dedup l1 l2 -> SameSetTD l2 l3 -> SameSetTD l1 l3.

Lemma SameSetTD_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSetTD l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  unfold SetEquiv.
  induction 1; intro.
    apply SetEquiv_refl.
    inv H. rewrite <- IHSameSetTD, !elem_app, !elem_cons', !elem_app, !elem_cons'. firstorder.
    inv H. rewrite <- IHSameSetTD, !elem_app, !elem_cons', !elem_app, !elem_cons'. firstorder.
Qed.
(* end hide *)

End SetTranspositionDedup.

(** ** Zbiory za pomocą sąsiednich transpozycji i deduplikacji *)

Module SetAdjacentTranspositionDedup.

Inductive AdjacentTransposition {A : Type} : list A -> list A -> Prop :=
| AdjacentTransposition' :
    forall (x y : A) (l1 l2 : list A),
      AdjacentTransposition (l1 ++ x :: y :: l2) (l1 ++ y :: x :: l2).

Inductive AdjacentDedup {A : Type} : list A -> list A -> Prop :=
| AdjacentDedup' :
    forall (x : A) (l1 l2 : list A),
      AdjacentDedup (l1 ++ x :: x :: l2) (l1 ++ x :: l2).

Inductive SameSetATD {A : Type} : list A -> list A -> Prop :=
| SameSetATD_refl   :
    forall l : list A, SameSetATD l l
| SameSetATD_transp :
    forall l1 l2 l3 : list A,
      AdjacentTransposition l1 l2 -> SameSetATD l2 l3 -> SameSetATD l1 l3
| SameSetATD_dedup  :
    forall l1 l2 l3 : list A,
      AdjacentDedup l1 l2 -> SameSetATD l2 l3 -> SameSetATD l1 l3.

Lemma SameSetATD_trans :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD l1 l2 ->
      forall {l3 : list A}, SameSetATD l2 l3 -> SameSetATD l1 l3.
(* begin hide *)
Proof.
  induction 1; intros.
    assumption.
    econstructor.
      eassumption.
      apply IHSameSetATD. assumption.
    econstructor 3.
      eassumption.
      apply IHSameSetATD. assumption.
Qed.
(* end hide *)

Lemma SameSetATD_SetEquiv :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD l1 l2 -> SetEquiv l1 l2.
(* begin hide *)
Proof.
  unfold SetEquiv.
  induction 1; intro.
    apply SetEquiv_refl.
    inv H. rewrite <- IHSameSetATD, !elem_app, !elem_cons'. firstorder.
    inv H. rewrite <- IHSameSetATD, !elem_app, !elem_cons'. firstorder.
Qed.

Lemma AdjacentTransposition_cons :
  forall {A : Type} {t1 t2 : list A},
    AdjacentTransposition t1 t2 ->
      forall h : A, AdjacentTransposition (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  induction 1.
  intro h.
  rewrite <- !app_cons_l.
  constructor.
Qed.
(* end hide *)

Lemma AdjacentDedup_cons :
  forall {A : Type} {t1 t2 : list A},
    AdjacentDedup t1 t2 ->
      forall h : A, AdjacentDedup (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  destruct 1.
  intro h.
  rewrite <- !app_cons_l.
  constructor.
Qed.
(* end hide *)

Lemma SameSetATD_cons :
  forall {A : Type} {t1 t2 : list A},
    SameSetATD t1 t2 ->
      forall h : A, SameSetATD (h :: t1) (h :: t2).
(* begin hide *)
Proof.
  induction 1; intros h.
    constructor.
    apply (@SameSetATD_transp _ _ (h :: l2)).
      apply AdjacentTransposition_cons. assumption.
      apply IHSameSetATD.
    apply (@SameSetATD_dedup _ _ (h :: l2)).
      apply AdjacentDedup_cons. assumption.
      apply IHSameSetATD.
Qed.
(* end hide *)

Lemma SetEquiv_SameSetATD :
  forall {A : Type} {l1 l2 : list A},
    SetEquiv l1 l2 -> SameSetATD l1 l2.
(* begin hide *)
Proof.
  unfold SetEquiv.
  induction l1 as [| h1 t1];
  intros l2 H.
    admit.
    {
      assert (elem h1 l2).
        apply H. left.
      apply elem_spec in H0.
      destruct H0 as (l1 & l3 & H0); subst.
      admit.
    }
Restart.
  intros.
Admitted.
(* end hide *)

Inductive SameSetATD' {A : Type} (l1 : list A) : list A -> Prop :=
| SameSetATD'_refl   :
    SameSetATD' l1 l1
| SameSetATD'_transp :
    forall l2 l3 : list A,
      SameSetATD' l1 l2 -> AdjacentTransposition l2 l3 -> SameSetATD' l1 l3
| SameSetATD'_dedup  :
    forall l2 l3 : list A,
      SameSetATD' l1 l2 -> AdjacentDedup l2 l3 -> SameSetATD' l1 l3.

Lemma SameSetATD'_trans :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD' l1 l2 ->
      forall {l3 : list A}, SameSetATD' l2 l3 -> SameSetATD' l1 l3.
(* begin hide *)
Proof.
  intros until 2. revert l1 H.
  induction H0; intros.
    assumption.
    econstructor.
      apply IHSameSetATD'. assumption.
      assumption.
    econstructor 3.
      apply IHSameSetATD'. assumption.
      assumption.
Qed.
(* end hide *)

Lemma SameSetATD'_spec :
  forall {A : Type} {l1 l2 : list A},
    SameSetATD' l1 l2 <-> SameSetATD l1 l2.
(* begin hide *)
Proof.
  split.
    induction 1.
      constructor.
      apply (SameSetATD_trans IHSameSetATD'). econstructor.
        eassumption.
        constructor.
      apply (SameSetATD_trans IHSameSetATD'). econstructor 3.
        eassumption.
        constructor.
    induction 1.
      constructor.
      eapply SameSetATD'_trans.
        2: eassumption.
        econstructor.
          constructor.
          assumption.
      eapply SameSetATD'_trans.
        2: eassumption.
        econstructor 3.
          constructor.
          assumption.
Qed.
(* end hide *)

End SetAdjacentTranspositionDedup.