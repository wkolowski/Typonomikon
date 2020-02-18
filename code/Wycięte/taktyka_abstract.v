(*
(** Możemy jednak zjeść ciastko i mieć ciastko, a wszystko to za
    sprawą taktyki [abstract]. *)

(*    TODO: ta taktyka ostatnimi czasy coś nie za bardzo chce dział*)
(* begin hide *)
(* TODO: w najnowszym Coqu nie działa *)
(* end hide *)


Lemma filter_length'' :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l; cbn; try destruct (f a); cbn.
    constructor.
    
  transparent_abstract lia using lemma_name.
  transparent_abstract lia using lemma_name'. Show Proof.
Qed.

Print filter_length''.
(* ===> Proofterm o długości 13 linijek. *)

(** Taktyka [abstract t] działa tak jak [t], ale z tą różnicą, że ukrywa term
    wygenerowany przez [t] w zewnętrznym lemacie. Po zakończeniu dowodu możemy
    zakończyć go komendą [Qed exporting], co spowoduje zapisanie go w takiej
    skróconej postaci z odwołaniami do zewnętrznych lematów, albo standardowym
    [Qed], przez co term będzie wyglądał tak, jakbyśmy wcale nie użyli taktyki
    [abstract]. *)
*)