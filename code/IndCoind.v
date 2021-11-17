Inductive TreeXY (A X Y : Type) : Type :=
    | E : TreeXY A X Y
    | N : A -> X -> Y -> TreeXY A X Y.

Arguments E {A X Y}.
Arguments N {A X Y} _ _ _.

CoInductive TreeX (A X : Type) : Type :=
{
    Out : TreeXY A X (TreeX A X);
}.

Arguments Out {A X} _.

Inductive Tree (A : Type) : Type :=
    | In : TreeXY A (Tree A) (TreeX A (Tree A)) -> Tree A.

Arguments In {A} _.

(* CoFixpoint nums (n : nat) : TreeX nat (Tree nat) :=
{|
    Out := N n 
 *)

CoFixpoint mapX {A B : Type} (f : A -> B) (map : Tree A -> Tree B) (t : TreeX A (Tree A)) : TreeX B (Tree B) :=
{|
    Out :=
      match Out t with
          | E => E
          | N x l r => N (f x) (map l) (mapX f map r)
      end;
|}.

Fixpoint map {A B : Type} (f : A -> B) (t : Tree A) {struct t} : Tree B :=
match t with
    | In E => In E
    | In (N x l r) => In (N (f x) (map f l) (mapX f (map f) r))
end.

with mapX {A B : Type} (f : A -> B) (t' : TreeX A (Tree A)) : TreeX B (Tree B) :=
{|
    Out :=
      match Out t' with
          | E => E
          | N x l r => N (f x) (map f l) (mapX f r)
      end;
|}.
        in

Fixpoint map {A B : Type} (f : A -> B) (t : Tree A) {struct t} : Tree B :=
match t with
    | In E => In E
    | In (N x l r) =>
        let mapX :=
          cofix mapX (t' : TreeX A (Tree A)) : TreeX B (Tree B) :=
          {|
              Out :=
                match Out t' with
                    | E => E
                    | N x l r => N (f x) (map f l) (mapX r)
                end;
          |}
        in
          In (N (f x) (map f l) (mapX r))
end.

