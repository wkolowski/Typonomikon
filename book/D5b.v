(** * D5b: Bardziej skomplikowane funkcje na listach [TODO] *)

From Typonomikon Require Export D5a.

(** * Sekcja mocno ad hoc *)

(** ** [pmap] *)

(** Zdefiniuj funkcję [pmap], która mapuje funkcję [f : A -> option B]
    po liście [l], ale odpakowuje wyniki zawinięte w [Some], a wyniki
    równe [None] usuwa.

    Przykład:
*)

(** [pmap (fun n : nat => if even n then None else Some (n + 42)) [1; 2; 3]]
    = [[43; 45]] *)

(* begin hide *)
Fixpoint pmap {A B : Type} (f : A -> option B) (l : list A) : list B :=
match l with
| [] => []
| h :: t =>
  match f h with
  | None => pmap f t
  | Some x => x :: pmap f t
  end
end.
(* end hide *)

Lemma isEmpty_pmap_false :
  forall (A B : Type) (f : A -> option B) (l : list A),
    isEmpty (pmap f l) = false -> isEmpty l = false.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    assumption.
    reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_pmap_true :
  forall (A B : Type) (f : A -> option B) (l : list A),
    isEmpty l = true -> isEmpty (pmap f l) = true.
(* begin hide *)
Proof.
  destruct l; cbn; intros.
    reflexivity.
    inversion H.
Qed.
(* end hide *)

Lemma length_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    length (pmap f l) <= length l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    apply Nat.le_0_l.
    destruct (f h); cbn.
      apply le_n_S. assumption.
      apply le_S. assumption.
Qed.
(* end hide *)

Lemma pmap_snoc :
  forall (A B : Type) (f : A -> option B) (x : A) (l : list A),
    pmap f (snoc x l) =
    match f x with
    | None => pmap f l
    | Some b => snoc b (pmap f l)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct (f x); reflexivity.
    destruct (f x), (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_app :
  forall (A B : Type) (f : A -> option B) (l1 l2 : list A),
    pmap f (l1 ++ l2) = pmap f l1 ++ pmap f l2.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_rev :
  forall (A B : Type) (f : A -> option B) (l : list A),
    pmap f (rev l) = rev (pmap f l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_snoc. destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_map :
  forall (A B C : Type) (f : A -> B) (g : B -> option C) (l : list A),
    pmap g (map f l) = pmap (fun x : A => g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (g (f h)); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_join :
  forall (A B : Type) (f : A -> option B) (l : list (list A)),
    pmap f (join l) = join (map (pmap f) l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_app. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma pmap_bind :
  forall (A B C : Type) (f : A -> list B) (g : B -> option C) (l : list A),
    pmap g (bind f l) = bind (fun x : A => pmap g (f x)) l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite pmap_app. rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma pmap_replicate :
  forall (A B : Type) (f : A -> option B) (n : nat) (x : A),
    pmap f (replicate n x) =
    match f x with
    | None => []
    | Some y => replicate n y
    end.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    destruct (f x); reflexivity.
    rewrite IHn'. destruct (f x); reflexivity.
Qed.
(* end hide *)

Definition isSome {A : Type} (x : option A) : bool :=
match x with
| None => false
| _ => true
end.

Lemma head_pmap :
  forall (A B : Type) (f : A -> option B) (l : list A),
    head (pmap f l) =
    match find isSome (map f l) with
    | None => None
    | Some x => x
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma pmap_zip :
  exists
    (A B C : Type)
    (fa : A -> option C) (fb : B -> option C)
    (la : list A) (lb : list B),
      pmap
        (fun '(a, b) =>
        match fa a, fb b with
        | Some a', Some b' => Some (a', b')
        | _, _ => None
        end)
        (zip la lb) <>
      zip (pmap fa la) (pmap fb lb).
(* begin hide *)
Proof.
  exists
    bool, bool, bool,
    (fun b : bool => if b then Some b else None),
    (fun b : bool => if b then None else Some b),
    [true; true; false], [true; false; false].
  cbn. inversion 1.
Qed.
(* end hide *)

Lemma any_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    any p (pmap f l) =
    any
      (fun x : A =>
      match f x with
      | Some b => p b
      | None => false
      end)
      l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma all_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    all p (pmap f l) =
    all
      (fun x : A =>
      match f x with
      | Some b => p b
      | None => true
      end)
      l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

Lemma find_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    find p (pmap f l) =
    let oa :=
      find (fun x : A => match f x with Some b => p b | _ => false end) l
    in
    match oa with
    | Some a => f a
    | None => None
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Heq; cbn.
      destruct (p b); cbn.
        symmetry. assumption.
        destruct (find _ t); cbn in *; assumption.
      destruct (find _ t); cbn in *; assumption.
Qed.
(* end hide *)

Lemma findLast_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    findLast p (pmap f l) =
    let oa :=
      findLast
        (fun x : A => match f x with Some b => p b | _ => false end) l
    in
    match oa with
    | Some a => f a
    | None => None
    end.
(* begin hide *)
Proof.
  intros. rewrite <- ?find_rev, <- pmap_rev, find_pmap. reflexivity.
Qed.
(* end hide *)

Lemma count_pmap :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    count p (pmap f l) =
    count
      (fun x : A =>
      match f x with
      | Some b => p b
      | None => false
      end)
      l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h); cbn; rewrite ?IHt; reflexivity.
Qed.
(* end hide *)

(* begin hide *)
(* TODO: higiena dla pmap_filter i jego aux *)
(* end hide *)

Definition aux {A B : Type} (p : B -> bool) (f : A -> option B)
  (dflt : bool) (x : A) : bool :=
match f x with
| Some b => p b
| None => dflt
end.

Lemma pmap_filter :
  forall (A B : Type) (p : B -> bool) (f : A -> option B) (l : list A),
    filter p (pmap f l) =
    pmap f (filter (aux p f false) l).
(* begin hide *)
Proof.
unfold aux.  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Hfh; cbn; rewrite ?IHt.
      destruct (p b); cbn; rewrite ?Hfh; reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma pmap_takeWhile :
  forall (A B : Type) (p : B -> bool) (f : A -> option B) (l : list A),
    takeWhile p (pmap f l) =
    pmap f
      (takeWhile
        (fun x : A => match f x with | Some b => p b | _ => true end)
        l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Hfh; cbn; rewrite ?Hfh, ?IHt.
      destruct (p b); cbn; rewrite ?Hfh; reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma pmap_dropWhile :
  forall (A B : Type) (p : B -> bool) (f : A -> option B) (l : list A),
    dropWhile p (pmap f l) =
    pmap f
      (dropWhile
        (fun x : A => match f x with | Some b => p b | _ => true end)
        l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (f h) eqn: Hfh; cbn; rewrite ?Hfh, ?IHt.
      destruct (p b); cbn; rewrite ?Hfh; reflexivity.
      reflexivity.
Qed.
(* end hide *)

Lemma pmap_span :
  forall (A B : Type) (f : A -> option B) (p : B -> bool) (l : list A),
    match
      span
        (fun x : A => match f x with None => false | Some b => p b end)
        l
    with
    | None => True
    | Some (b, x, e) =>
        exists y : B, f x = Some y /\
          span p (pmap f l) = Some (pmap f b, y, pmap f e)
    end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    trivial.
    destruct (f h) eqn: Heq.
      destruct (p b) eqn: Hpb; cbn; rewrite ?Hpb.
        exists b. split; trivial.
        destruct (span _ t); trivial.
          destruct p0, p0; cbn in *.
            destruct IHt as (y & IH1 & IH2).
              exists y. rewrite IH1, IH2, Heq. split; reflexivity.
      destruct (span _ t); trivial.
        destruct p0, p0, IHt as (y & IH1 & IH2).
          exists y. cbn. rewrite IH1, IH2, Heq. split; reflexivity.
Qed.
(* end hide *)

Lemma pmap_nth_findIndices :
  forall (A : Type) (p : A -> bool) (l : list A),
    pmap (fun n : nat => nth n l) (findIndices p l) =
    filter p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (p h); cbn; rewrite pmap_map, IHt; reflexivity.
Qed.
(* end hide *)

(** ** [mask] *)

(** Zdefiniuj funkcję [mask], który bierze funkcję [f : A -> A], listę wartości
    boolowskich [bs : list bool] oraz listę [l : list A] i aplikuje funkcję [f]
    do tych elementów listy [l], dla których odpowiadający bit w masce [bs] jest
    równy [true]. Jeżeli maska jest krótsza niż lista, to reszta listy "wystająca"
    za maskę powinna zostać niezmieniona.

    Przykład: *)

(** [mask S [true; false; true; false] [1; 2; 3; 4; 5; 6]] = [[2; 2; 4; 4; 5; 6]] *)

(* begin hide *)
Fixpoint mask {A : Type} (f : A -> A) (bs : list bool) (l : list A) : list A :=
match bs, l with
| [], _ => l
| _, [] => []
| b :: bs', h :: t => (if b then f h else h) :: mask f bs' t
end.
(* end hide *)

Lemma mask_nil :
  forall {A : Type} (f : A -> A) (bs : list bool),
    mask f bs [] = [].
(* begin hide *)
Proof.
  destruct bs; reflexivity.
Qed.
(* end hide *)

Lemma isEmpty_mask :
  forall {A : Type} (f : A -> A) (bs : list bool) (l : list A),
    isEmpty (mask f bs l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l, bs; cbn; reflexivity.
Qed.
(* end hide *)

Lemma length_mask :
  forall {A : Type} (f : A -> A) (bs : list bool) (l : list A),
    length (mask f bs l) = length l.
(* begin hide *)
Proof.
  induction bs as [| b bs']; cbn.
  - reflexivity.
  - destruct l as [| h t]; cbn; rewrite ?IHbs'; reflexivity.
Qed.
(* end hide *)

Lemma mask_app_r :
  forall {A : Type} (f : A -> A) (bs : list bool) (l1 l2 : list A),
    mask f bs (l1 ++ l2) = mask f bs l1 ++ mask f (drop (length l1) bs) l2.
(* begin hide *)
Proof.
  induction bs as [| b bs']; cbn.
  - reflexivity.
  - destruct l1 as [| h1 t1]; cbn; intro l2; rewrite ?IHbs'; reflexivity.
Qed.
(* end hide *)

Lemma mask_app_l :
  forall {A : Type} (f : A -> A) (bs1 bs2 : list bool) (l : list A),
    mask f (bs1 ++ bs2) l = mask f (replicate (length bs1) false ++ bs2) (mask f bs1 l).
(* begin hide *)
Proof.
  induction bs1 as [| b1 bs1']; cbn.
  - reflexivity.
  - destruct l as [| h t]; cbn; rewrite ?IHbs1'; reflexivity.
Qed.
(* end hide *)

Lemma mask_app_l' :
  forall {A : Type} (f : A -> A) (bs1 bs2 : list bool) (l : list A),
    mask f (bs1 ++ bs2) l
      =
    mask f bs1 (take (length bs1) l) ++ mask f bs2 (drop (length bs1) l).
(* begin hide *)
Proof.
  induction bs1 as [| b1 bs1']; cbn.
  - intros. rewrite take_0, drop_0; cbn. reflexivity.
  - destruct l as [| h t]; cbn.
    + rewrite mask_nil; reflexivity.
    + rewrite IHbs1'; reflexivity.
Qed.
(* end hide *)

Lemma mask_replicate_true :
  forall {A : Type} (f : A -> A) (n : nat) (l : list A),
    mask f (replicate n true) l = map f (take n l) ++ drop n l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
  - intro l2. rewrite take_0, drop_0; cbn. reflexivity.
  - destruct l as [| h t]; cbn; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma mask_replicate_false :
  forall {A : Type} (f : A -> A) (n : nat) (l : list A),
    mask f (replicate n false) l = l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
  - reflexivity.
  - destruct l as [| h t]; cbn; rewrite ?IHn'; reflexivity.
Qed.
(* end hide *)

Lemma take_mask :
  forall {A : Type} (n : nat) (f : A -> A) (bs : list bool) (l : list A),
    take n (mask f bs l) = mask f bs (take n l).
(* begin hide *)
Proof.
  intros A n f bs. revert n.
  induction bs as [| b bs']; cbn.
  - reflexivity.
  - destruct l as [| h t]; cbn.
    + reflexivity.
    + destruct n as [| n']; cbn.
      * reflexivity.
      * rewrite IHbs'. reflexivity.
Qed.
(* end hide *)

Lemma take_mask' :
  forall {A : Type} (n : nat) (f : A -> A) (bs : list bool) (l : list A),
    take n (mask f bs l) = mask f (take n bs) (take n l).
(* begin hide *)
Proof.
  intros A n f bs; revert n.
  induction bs as [| b bs']; cbn.
  - reflexivity.
  - destruct l as [| h t], n as [| n']; cbn; rewrite ?IHbs'; reflexivity.
Qed.
(* end hide *)

Lemma drop_mask :
  forall {A : Type} (n : nat) (f : A -> A) (bs : list bool) (l : list A),
    drop n (mask f bs l) = mask f (drop n bs) (drop n l).
(* begin hide *)
Proof.
  intros A n f bs; revert n.
  induction bs as [| b bs']; cbn.
  - reflexivity.
  - destruct l as [| h t], n as [| n']; cbn; rewrite ?mask_nil, ?IHbs'; reflexivity.
Qed.
(* end hide *)

Lemma nth_mask :
  forall {A : Type} (n : nat) (f : A -> A) (bs : list bool) (l : list A),
    nth n (mask f bs l)
      =
    match nth n bs with
    | None => nth n l
    | Some false => nth n l
    | Some true =>
      match nth n l with
      | None => None
      | Some x => Some (f x)
      end
    end.
(* begin hide *)
Proof.
  intros A n f bs; revert n.
  induction bs as [| b bs']; cbn.
  - reflexivity.
  - destruct l as [| h t], n as [| n'], b; cbn; rewrite ?IHbs'; try reflexivity.
    1-2: destruct (nth n' bs') as [[] |]; try reflexivity.
Qed.
(* end hide *)

Lemma mask_zipWith :
  forall {A : Type} (f : A -> A) (bs : list bool) (l : list A),
    mask f bs l = zipWith (fun (b : bool) (x : A) => if b then f x else x) bs l.
(* begin hide *)
Proof.
Abort.
(* end hide *)

(* begin hide *)
(*
snoc
rev
map
join
bind
iterate i iter
head
tail
uncons
last
init
unsnoc

cycle
splitAt
insert
replace
remove
zip
unzip
zipWith
unzipWith
*)
(* end hide *)

(** ** Też [mask], ale inaczej *)

(** Zaimplementuj funkcję [mask'], która działa podobnie do [mask], ale tym razem
    jeżeli lista wystaje za maskę, to jest przycinana do długości maski.

    Znajdź i udowodnij porządną specyfikację dla swojej funkcji. *)

(* begin hide *)
Fixpoint mask' {A : Type} (f : A -> A) (l : list A) (bs : list bool) : list A :=
match l, bs with
| [], _ => []
| _, [] => []
| h :: t, b :: bs' => (if b then f h else h) :: mask' f t bs'
end.
(* end hdie *)

Lemma mask'_zipWith :
  forall {A : Type} (f : A -> A) (l : list A) (bs : list bool),
    mask' f l bs = zipWith (fun (b : bool) (x : A) => if b then f x else x) bs l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intro.
  - destruct bs; reflexivity. (* TODO: zipWith_nil_r *)
  - destruct bs as [| b bs']; cbn.
    + reflexivity.
    + rewrite IHt. reflexivity.
Qed.
(* end hide *)

Lemma length_mask' :
  forall {A : Type} (f : A -> A) (l : list A) (bs : list bool),
    length (mask' f l bs) = min (length bs) (length l).
(* begin hide *)
Proof.
  intros. rewrite mask'_zipWith, zipWith_spec, length_map, length_zip. reflexivity.
Qed.
(* end hide *)

(** ** [imap], czyli mapowanie z indeksem *)

(* begin hide *)
Fixpoint imap {A B : Type} (f : nat -> A -> B) (l : list A) : list B :=
match l with
| [] => []
| h :: t => f 0 h :: imap (fun n a => f (S n) a) t
end.
(* end hide *)

Lemma imap_id :
  forall {A : Type} (l : list A),
    imap (fun _ x => x) l = l.
(* begin hide *)
Proof.
  now induction l as [| h t]; cbn; rewrite ?IHt.
Qed.
(* end hide *)

Lemma imap_imp :
  forall {A B C : Type} (f : nat -> A -> B) (g : nat -> B -> C) (l : list A),
    imap g (imap f l) = imap (fun n a => g n (f n a)) l.
(* begin hide *)
Proof.
  intros A B C f g l; revert f g.
  induction l as [| h t]; cbn; intros.
  - easy.
  - now rewrite (IHt (fun n a => f (S n) a) (fun n b => g (S n) b)).
Qed.
(* end hide *)

Lemma isEmpty_imap :
  forall (A B : Type) (f : nat -> A -> B) (l : list A),
    isEmpty (imap f l) = isEmpty l.
(* begin hide *)
Proof.
  now destruct l as [| h t]; cbn; intros.
Qed.
(* end hide *)

Lemma length_imap :
  forall (A B : Type) (f : nat -> A -> B) (l : list A),
    length (imap f l) = length l.
(* begin hide *)
Proof.
  intros A B f l; revert f.
  now induction l as [| h t]; cbn; intros; rewrite ?IHt.
Qed.
(* end hide *)

Lemma imap_snoc :
  forall (A B : Type) (f : nat -> A -> B) (x : A) (l : list A),
    imap f (snoc x l) = snoc (f (length l) x) (imap f l).
(* begin hide *)
Proof.
  intros A B f x l; revert f.
  now induction l as [| h t]; cbn; intros; rewrite ?IHt.
Qed.
(* end hide *)

(*
Lemma imap_app :
  forall (A B : Type) (f : nat -> A -> B) (l1 l2 : list A),
    imap f (l1 ++ l2) = imap f l1 ++ imap f l2.

Lemma imap_rev :
  forall (A B : Type) (f : nat -> A -> B) (l : list A),
    imap f (rev l) = rev (imap f l).

*)

Lemma imap_ext :
  forall (A B : Type) (f g : nat -> A -> B) (l : list A),
    (forall (n : nat) (a : A), f n a = g n a) ->
      imap f l = imap g l.
(* begin hide *)
Proof.
  intros A B f g l; revert f g.
  induction l as [| h t]; cbn; intros; [easy |].
  now erewrite H, IHt; firstorder.
Qed.
(* end hide *)

Lemma head_imap :
  forall (A B : Type) (f : nat -> A -> B) (l : list A),
    head (imap f l) =
    match l with
    | [] => None
    | h :: _ => Some (f 0 h)
    end.
(* begin hide *)
Proof.
  now destruct l as [| h t]; cbn.
Qed.
(* end hide *)

Lemma tail_imap :
  forall (A B : Type) (f : nat -> A -> B) (l : list A),
    tail (imap f l) =
    match l with
    | [] => None
    | _ :: t => Some (imap (fun n a => f (S n) a) t)
    end.
(* begin hide *)
Proof.
  now destruct l as [| h t]; cbn.
Qed.
(* end hide *)

Lemma init_imap :
  forall (A B : Type) (f : nat -> A -> B) (l : list A),
    init (imap f l) =
    match l with
    | [] => None
    | h :: t =>
      match init t with
      | None => Some []
      | Some i => Some (imap f (h :: i))
      end
    end.
(* begin hide *)
Proof.
  intros A B f l; revert f.
  induction l as [| h t]; cbn; intros; [easy |].
  rewrite IHt.
  destruct t as [| h' t']; cbn; [easy |].
  now destruct (init t').
Qed.
(* end hide *)

Lemma nth_imap_Some :
  forall (A B : Type) (f : nat -> A -> B) (l : list A) (n : nat) (x : A),
    nth n l = Some x -> nth n (imap f l) = Some (f n x).
(* begin hide *)
Proof.
  intros A B f l; revert f.
  induction l as [| h t]; cbn; intros f n x Heq; [now inversion Heq |].
  destruct n as [| n']; [now inversion Heq |].
  now apply (IHt (fun n a => f (S n) a)).
Qed.
(* end hide *)

Lemma nth_imap :
  forall (A B : Type) (f : nat -> A -> B) (l : list A) (n : nat),
    nth n (imap f l) =
    match nth n l with
    | None => None
    | Some x => Some (f n x)
    end.
(* begin hide *)
Proof.
  intros A B f l; revert f.
  induction l as [| h t]; cbn; intros f n; [easy |].
  destruct n as [| n']; [easy |].
  now apply (IHt (fun n a => f (S n) a)).
Qed.
(* end hide *)

Lemma take_imap :
  forall (A B : Type) (f : nat -> A -> B) (l : list A) (n : nat),
    take n (imap f l) = imap f (take n l).
(* begin hide *)
Proof.
  intros A B f l; revert f.
  induction l as [| h t]; cbn; intros; [easy |].
  now destruct n as [| n']; cbn; rewrite ?IHt.
Qed.
(* end hide *)

Lemma zip_imap :
  forall (A B A' B' : Type) (f : nat -> A -> A') (g : nat -> B -> B')
  (la : list A) (lb : list B),
    zip (imap f la) (imap g lb) =
    imap (fun n x => (f n (fst x), g n (snd x))) (zip la lb).
(* begin hide *)
Proof.
  intros A B A' B' f g la; revert f g.
  induction la as [| ha ta]; cbn; intros; [easy |].
  destruct lb as [| hb tb]; cbn; intros; [easy |].
  now rewrite (IHta (fun n a => f (S n) a) (fun n b => g (S n) b)).
Qed.
(* end hide *)

(** * Bardziej skomplikowane funkcje *)

(** ** [intersperse] *)

(** Zdefiniuj funkcję [intersperse], który wstawia element [x : A] między
    każde dwa elementy z listy [l : list A]. Zastanów się dobrze nad
    przypadkami bazowymi.

    Przykład:
*)

(** [intersperse 42 [1; 2; 3]] = [[1; 42; 2; 42; 3]] *)

(* begin hide *)
Function intersperse {A : Type} (x : A) (l : list A) : list A :=
match l with
| [] => []
| h :: t =>
  match intersperse x t with
  | [] => [h]
  | h' :: t' => h :: x :: h' :: t'
  end
end.
(* end hide *)

Lemma isEmpty_intersperse :
  forall (A : Type) (x : A) (l : list A),
    isEmpty (intersperse x l) = isEmpty l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma length_intersperse :
  forall (A : Type) (x : A) (l : list A),
    length (intersperse x l) = 2 * length l - 1.
(* begin hide *)
Proof.
  induction l as [| h [| h' t]]; cbn in *.
    1-2: reflexivity.
    destruct (intersperse x t); cbn in *.
      rewrite <- Nat.sub_0_r, Nat.add_0_r, <- ?plus_n_Sm in *.
        destruct t; inversion IHl. cbn. reflexivity.
      rewrite IHl. rewrite <- ?plus_n_Sm. rewrite <- Nat.sub_0_r.
        reflexivity.
Qed.
(* end hide *)

Lemma intersperse_snoc :
  forall (A : Type) (x y : A) (l : list A),
    intersperse x (snoc y l) =
    if isEmpty l then [y] else snoc y (snoc x (intersperse x l)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. destruct t; cbn.
      reflexivity.
      destruct (intersperse x t); cbn; reflexivity.
Qed.
(* end hide *)

Lemma intersperse_app :
  forall (A : Type) (x : A) (l1 l2 : list A),
    intersperse x (l1 ++ l2) =
    match l1, l2 with
    | [], _ => intersperse x l2
    | _, [] => intersperse x l1
    | h1 :: t1, h2 :: t2 =>
        intersperse x l1 ++ x :: intersperse x l2
    end.
(* begin hide *)
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. destruct t, l2; cbn.
      1,3: reflexivity.
      destruct (intersperse x l2); reflexivity.
      destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma intersperse_app_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    l1 <> [] -> l2 <> [] ->
      intersperse x (l1 ++ l2) = intersperse x l1 ++ x :: intersperse x l2.
(* begin hide *)
Proof.
  intros. rewrite intersperse_app. destruct l1.
    contradiction.
    destruct l2.
      contradiction.
      reflexivity.
Qed.
(* end hide *)

Lemma intersperse_rev :
  forall (A : Type) (x : A) (l : list A),
    intersperse x (rev l) = rev (intersperse x l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite intersperse_snoc. destruct (rev t) eqn: Heq.
      apply (f_equal rev) in Heq. rewrite rev_rev in Heq.
        cbn in Heq. rewrite Heq. cbn. reflexivity.
      rewrite IHt. destruct (intersperse x t); cbn.
        cbn in IHt. destruct (intersperse x l); inversion IHt.
          reflexivity.
Qed.
(* end hide *)

Lemma intersperse_map :
  forall (A B : Type) (f : A -> B) (l : list A) (a : A) (b : B),
    f a = b -> intersperse b (map f l) = map f (intersperse a l).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite (IHt _ _ H). destruct (intersperse a t); cbn.
      reflexivity.
      rewrite H. reflexivity.
Qed.
(* end hide *)

Lemma head_intersperse :
  forall (A : Type) (x : A) (l : list A),
    head (intersperse x l) = head l.
(* begin hide *)
Proof.
  destruct l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t); reflexivity.
Qed.
(* end hide *)

Lemma last_intersperse :
  forall (A : Type) (x : A) (l : list A),
    last (intersperse x l) = last l.
(* begin hide *)
Proof.
  intros. pose (H := intersperse_rev _ x (rev l)).
  rewrite rev_rev in H.
  rewrite H, last_rev, head_intersperse, head_rev.
  reflexivity.
Qed.
(* end hide *)

Lemma tail_intersperse :
  forall (A : Type) (x : A) (l : list A),
    tail (intersperse x l) =
    match tail l with
    | None => None
    | Some [] => Some []
    | Some (h :: t) => tail (intersperse x l)
    end.
(* begin hide *)
Proof.
  intros A x l. functional induction @intersperse A x l; cbn.
    reflexivity.
    destruct t; reflexivity.
    destruct t; cbn in *.
      inv e0.
      reflexivity.
Qed.
(* end hide *)

Lemma nth_intersperse_even :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    n < length l ->
      nth (2 * n) (intersperse x l) = nth n l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H.
    destruct n as [| n']; cbn.
      destruct (intersperse x t); reflexivity.
      destruct (intersperse x t).
        cbn. destruct t; cbn in *.
          reflexivity.
          apply Nat.succ_lt_mono in H. specialize (IHt _ H).
            destruct n'; cbn in *; inversion IHt.
              reflexivity.
        rewrite <- plus_n_Sm. cbn. rewrite <- IHt.
          cbn. reflexivity.
          apply Nat.succ_lt_mono. assumption.
Qed.
(* end hide *)

Lemma nth_intersperse_odd :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    0 < n -> n < length l ->
      nth (2 * n - 1) (intersperse x l) = Some x.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    destruct n; inversion H0.
    destruct (intersperse x t) eqn: Heq.
      destruct t; cbn in *.
        destruct n; cbn in *.
          inversion H.
          destruct n; cbn in *.
            inversion H0. inversion H2.
            inversion H0. inversion H2.
        destruct (intersperse x t); inversion Heq.
      destruct t; cbn in *.
        inversion Heq.
        destruct n as [| n']; cbn.
          inversion H.
          destruct n' as [| n'']; cbn.
            reflexivity.
            rewrite <- IHt with (S n'').
              cbn. rewrite <- ?plus_n_Sm, Nat.sub_0_r, ?Nat.add_0_r.
                cbn. reflexivity.
              apply le_n_S, Nat.le_0_l.
              apply Nat.succ_lt_mono. assumption.
Qed.
(* end hide *)

Lemma intersperse_take :
  forall (A : Type) (x : A) (l : list A) (n : nat),
    intersperse x (take n l) =
    take (2 * n - 1) (intersperse x l).
(* begin hide *)
Proof.
  intros A x l. functional induction @intersperse A x l; cbn; intros.
    reflexivity.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite <- plus_n_Sm. cbn. destruct t; cbn in *.
        reflexivity.
        destruct (intersperse x t); inv e0.
    destruct n as [| n']; cbn.
      reflexivity.
      rewrite <- plus_n_Sm, IHl0. destruct n' as [| n'']; cbn.
        rewrite take_0. reflexivity.
        rewrite <- plus_n_Sm, Nat.add_0_r. cbn. destruct t; cbn in *.
          inv e0.
          destruct (intersperse x t); inv e0; reflexivity.
Qed.
(* end hide *)

Lemma any_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    any p (intersperse x l) =
    orb (any p l) (andb (2 <=? length l) (p x)).
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn.
      destruct t; cbn in *.
        rewrite ?Bool.orb_false_r. reflexivity.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t) eqn: Heq'; inv Heq.
          destruct t; cbn in *.
            rewrite ?Bool.orb_false_r.
              destruct (p h), (p a), (p x); reflexivity.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (any p t);
              reflexivity.
          destruct t; cbn in *.
            inv Heq'.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (any p t);
              reflexivity.
Qed.
(* end hide *)

Lemma all_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    all p (intersperse x l) =
    all p l && ((length l <=? 1) || p x).
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn in *.
    reflexivity.
    destruct t; cbn in *.
      rewrite ?Bool.andb_true_r. reflexivity.
      rewrite e0 in *. cbn in *. destruct t; cbn in *.
        inversion e0.
        rewrite IHl0. rewrite Bool.andb_assoc. reflexivity.
    rewrite e0 in *. cbn in *. rewrite IHl0. destruct t; cbn.
      inversion e0.
      destruct t; cbn.
        rewrite ?Bool.andb_true_r.
          destruct (p h), (p x), (p a); reflexivity.
        destruct (p h), (p x), (p a), (p a0), (all p t); reflexivity.
Restart.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn.
      destruct t; cbn in *.
        rewrite ?Bool.andb_true_r. reflexivity.
        destruct (intersperse x t); inv Heq.
      destruct t; cbn in *.
        inv Heq.
        destruct (intersperse x t) eqn: Heq'; inv Heq.
          destruct t; cbn in *.
            rewrite ?Bool.andb_true_r.
              destruct (p h), (p a), (p x); reflexivity.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (all p t);
              reflexivity.
          destruct t; cbn in *.
            inv Heq'.
            rewrite IHt. destruct (p h), (p x), (p a), (p a0), (all p t);
              reflexivity.
Qed.
(* end hide *)

Lemma findIndex_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    findIndex p (intersperse x l) =
    if p x
    then
      match l with
      | [] => None
      | [h] => if p h then Some 0 else None
      | h :: t => if p h then Some 0 else Some 1
      end
    else
      match findIndex p l with
      | None => None
      | Some n => Some (2 * n)
      end.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn.
    destruct (p x); reflexivity.
    destruct (intersperse x t) eqn: Heq; cbn in *.
      destruct t; cbn in *.
        destruct (p h), (p x); reflexivity.
        destruct (intersperse x t); inversion Heq.
      destruct (p h), (p x), (p a) eqn: Hpa, t;
      cbn in *; try reflexivity; try inversion Heq.
        destruct (p a0); cbn.
          reflexivity.
          destruct (findIndex p t); inversion IHt.
        destruct (findIndex p l); cbn in *.
          destruct (intersperse x t); inversion Heq; subst.
            rewrite Hpa in *. destruct (findIndex p t).
              inversion IHt; cbn. f_equal. lia.
              inversion IHt.
            rewrite Hpa in *.
              destruct (findIndex p t); inversion IHt.
                f_equal. lia.
          destruct (intersperse x t); inversion Heq; subst;
          rewrite Hpa in *.
            destruct (findIndex p t); inversion IHt. reflexivity.
            destruct (findIndex p t); inversion IHt. reflexivity.
Qed.
(* end hide *)

Lemma count_intersperse :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    count p (intersperse x l) =
    count p l + if p x then length l - 1 else 0.
(* begin hide *)
Proof.
  intros. functional induction @intersperse A x l; cbn.
    destruct (p x); reflexivity.
    destruct t; cbn in *.
      rewrite <- IHl0, Nat.add_0_r. reflexivity.
      destruct (intersperse x t); inv e0.
    rewrite e0 in IHl0. cbn in IHl0.
      destruct (p x), (p h), (p h'); rewrite IHl0; try lia.
        1-4: destruct t; inv e0; cbn; destruct (p a); lia.
Qed.
(* end hide *)

Lemma filter_intersperse_false :
  forall (A : Type) (p : A -> bool) (x : A) (l : list A),
    p x = false -> filter p (intersperse x l) = filter p l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite <- (IHt H). destruct (intersperse x t); cbn in *.
      destruct (p h); reflexivity.
      destruct (p h), (p x), (p a); congruence.
Qed.
(* end hide *)

Lemma pmap_intersperse :
  forall (A B : Type) (f : A -> option B) (x : A) (l : list A),
    f x = None -> pmap f (intersperse x l) = pmap f l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (intersperse x t); cbn.
      rewrite <- (IHt H). cbn. reflexivity.
      rewrite H, <- (IHt H). destruct (f h); cbn; destruct (f a); reflexivity.
Qed.
(* end hide *)

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
      rewrite Nat.add_0_r. reflexivity.
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
      rewrite Nat.add_0_r. reflexivity.
      {
        rewrite IHt1.
        destruct (p h1) eqn: ph1, (p h2) eqn: ph2; cbn.
        all: try rewrite plus_n_Sm; reflexivity.
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

Compute groupBy Nat.eqb [0; 1; 2; 3; 0; 4; 5; 6; 0; 7; 8; 9; 0; 0].
Compute groupBy
  (fun n m => negb (Nat.eqb n m))
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
    intros. rewrite length_app, Nat.add_comm. reflexivity.
    destruct l1; cbn; intros.
      reflexivity.
      rewrite IHn'. reflexivity.
Restart.
  intros.
  rewrite insert_before_in_char, ?length_app, length_drop.
    rewrite length_take. apply Nat.min_case_strong; intros; lia.
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
          eapply Nat.le_trans with (n' + length t1).
            apply Nat.le_add_l.
            rewrite <- Nat.add_le_mono_l. apply le_S, le_n.
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
      rewrite Nat.add_0_r, insert_before_length_in_app. reflexivity.
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
    rewrite rev_app, Nat.sub_0_r, <- length_rev, insert_before_length.
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
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      inversion H.
      apply IHn', le_S_n. assumption.
Qed.
(* end hide *)

Lemma minus_wut' :
  forall n m : nat,
    n <= m -> n - (n - m) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct m as [| m']; cbn.
      inversion H.
      rewrite minus_wut.
        reflexivity.
        apply le_S_n. assumption.
Qed.
(* end hide *)

Lemma minus_wut'' :
  forall n m : nat,
    m <= n -> n - (n - m) = m.
(* begin hide *)
Proof.
  intros. lia.
Qed.
(* end hide *)

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
    rewrite insert_before_in_nil, app_nil_r, Nat.min_0_r. cbn. reflexivity.
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
      rewrite count_app, Nat.add_comm. cbn. rewrite Hph. cbn. reflexivity.
      rewrite Hph, IHt. reflexivity.
      rewrite count_app, Nat.add_comm. cbn. rewrite Hph. reflexivity.
      rewrite Hph, IHt. reflexivity.
Qed.
(* end hide *)

End insertBefore.