Fixpoint even (n : nat) : bool :=
match n with
| 0 => true
| S n' => odd n'
end

with odd (n : nat) : bool :=
match n with
| 0 => false
| S n' => even n'
end.