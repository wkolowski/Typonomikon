(* Require Import F3.
 *)

CoInductive Tree (A : Type) : Type :=
{
    root  : A;
    trees : TreeStream A;
}

with TreeStream (A : Type) : Type :=
{
    hd : Tree A;
    tl : TreeStream A;
}.

Arguments root  {A} _.
Arguments trees {A} _.

Arguments hd {A} _.
Arguments tl {A} _.

CoFixpoint stmap {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
{|
    root  := f (root t);
    trees := smap f (trees t);
|}

with smap {A B : Type} (f : A -> B) (s : TreeStream A) : TreeStream B :=
{|
    hd := stmap f (hd s);
    tl := smap  f (tl s);
|}.

CoInductive TreeStreamSim {A : Type} (TS : Tree A -> Tree A -> Type) (s1 s2 : TreeStream A) : Type :=
{
    hds : TS (hd s1) (hd s2);
    tls : TreeStreamSim TS (tl s1) (tl s2);
}.

CoInductive TreeSim {A : Type} (t1 t2 : Tree A) : Type :=
{
    roots  : root t1 = root t2;
    treess : TreeStreamSim TreeSim (trees t1) (trees t2);
}.

Fail CoInductive TreeSim {A : Type} (t1 t2 : Tree A) : Type :=
{
    roots  : root t1 = root t2;
    treess : TreeStreamSim (trees t1) (trees t2);
}

with TreeStreamSim {A : Type} (s1 s2 : TreeStream A) : Type :=
{
    hds : TreeSim (hd s1) (hd s2);
    tls : TreeStreamSim (tl s1) (tl s2);
}.