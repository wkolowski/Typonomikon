# Ściąga - konstruktywny rachunek zdań

| nazwa           | wymowa             | Coq         | jak udowodnić | jak użyć w dowodzie | inne przydatne taktyki |
| --------------- | ------------------ | ----------- | ------------- | ------------------- | ---------------------- |
| implikacja      | jeżeli `P` to `Q` <br> `P` implikuje `Q` | `P -> Q` | `intro` <br> `intros` <br> `intros H` | `apply H` <br> `apply H1 in H2` | `specialize (H1 H2)` |
| dysjunkcja      | `P` lub `Q` | `P \/ Q` <br> `or P Q` | `left` <br> `right` | `destruct H as [H1 \| H2]` | `decompose [ex or and] H` |
| koniunkcja      | `P` i `Q` <br> `P` oraz `Q` | `P /\ Q` <br> `and P Q` | `split` | `destruct H as [H1 H2]` | `destruct H as (H1 & H2 & H3)` (zagnieżdżona koniunkcja) |
| prawda          | prawda <br> zdanie zawsze prawdziwe  | `True` | `trivial` | bezużyteczna | `clear H` |
| fałsz           | fałsz <br> zdanie zawsze fałszywe | `False` | nie da się | `contradiction` | `assumption` <br> `exfalso` |
| negacja         | nie `P` <br> nieprawda, że `P` | `~ P` | `intro H` | `apply H` <br> `apply H1 in H2` | `unfold not` <br> `specialize (H1 H2)` |
| równoważność logiczna | `P` wtedy i tylko wtedy, gdy `Q` <br> `P` jest równoważne `Q` | `P <-> Q` <br> `iff P Q` | `split` | `destruct H as [H1 H2]` | `unfold iff` |

# Ściąga - konstruktywny rachunek predykatów

| nazwa           | wymowa             | Coq         | jak udowodnić | jak użyć w dowodzie | inne przydatne taktyki | 
| --------------- | ------------------ | ----------- | ------------- | ------------------- | ---------------------- |
| kwantyfikator uniwersalny | dla każdego `x` (typu `A`), (zachodzi) `P x` | `forall x : A, P x` | `intro` <br> `intros` <br> `intros H` | `apply H` <br> `apply H1 in H2` | `specialize (H1 H2)` |
| kwantyfikator egzystencjalny | istnieje takie `x` (typu `A`), że (zachodzi) `P x` <br> istnieje `x` (typu `A`) spełniające `P` | `exists x : A, P x` | `exists x` | `destruct H as [x Hx]` | `decompose [ex or and] H` |
| równość         | `x` jest równe `y` | `x = y` <br> `eq x y` | `reflexivity` | `rewrite H` <br> `rewrite <- H` <br> `rewrite H1 in H2` | `subst` <br> `congruence` <br> `injection` <br> `discriminate` |