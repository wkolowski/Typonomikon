Inductive BS : Type :=
| L : BS
| R : BS
| l : BS -> BS
| r : BS -> BS.
(* | eqL : L   = l L
| eqM : l R = r L
| eqR : R   = r R *)

Inductive D : Type :=
| middle : D
| left   : D -> D
| right  : D -> D.

Inductive BS' : Type :=
| L' : BS'
| R' : BS'
| η  : D -> BS'.