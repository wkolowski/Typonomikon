Fail Inductive Tree (A : Type) : Type :=
| E
| N (v : A) (ts : StreamTree A)

with CoInductive StreamTree (A : Type) : Type :=
{
  hd : Tree A;
  tl : StreamTree A;
}.