Record t : Type :=
{
  a : bool;
  b : if a then bool else unit;
  c :
    match a, b with
    | true, true => nat
    | _   , _    => unit
    end;
}.