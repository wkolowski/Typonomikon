Inductive TernarySystem : Type :=
| A : TernarySystem
| B : TernarySystem
| C : TernarySystem
| mid : TernarySystem -> TernarySystem -> TernarySystem.

(**
  [TernarySystem] ma reprezentować punkty na trójkącie jednostkowym, ale
  tak naprawdę reprezentuje coś w stylu wektorów na tym trójkącie, bo nie
  mamy przemienności.

  W takim razie [A] to wektor z początku układu (cokolwiek nim jest) do [A],
  jednego z wierzchołków trójkąta, i podobnie dla [B] i [C].

  [mid A B] to wektor idący z [A] do punktu, który jest środkiem odcinka AB,
  zaś [mid B A] to też wektor do owego punkty, ale wychodzący z [B].

  [mid (mid A B) C] to wektor ze środka odcinka AB do środka odcinka (AB)C...
*)

