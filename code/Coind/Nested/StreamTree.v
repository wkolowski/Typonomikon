From Typonomikon Require Import F3.

CoInductive StreamTree (A : Type) : Type :=
{
    root : A;
    trees : Stream (StreamTree A);
}.

Arguments root  {A} _.
Arguments trees {A} _.

(* Unset Guard Checking. *)
Fail CoFixpoint stmap {A B : Type} (f : A -> B) (t : StreamTree A) : StreamTree B :=
{|
    root := f (root t);
    trees := map (stmap f) (trees t);
|}.
Set Guard Checking.

Fail CoFixpoint stmap {A B : Type} (f : A -> B) (t : StreamTree A) : StreamTree B :=
{|
    root  := f (root t);
    trees :=
    {|
        hd := stmap f (hd (trees t));
        tl := trees (stmap f {| root := root t; trees := tl (trees t); |})
    |};
|}.

Fail CoFixpoint stmap {A B : Type} (f : A -> B) (t : StreamTree A) : StreamTree B :=
{|
    root  := f (root t);
    trees := smap f (trees t);
|}

with smap {A B : Type} (f : A -> B) (s : Stream (StreamTree A)) : Stream (StreamTree B) :=
{|
    hd := stmap f (hd s);
    tl := smap  f (tl s);
|}.