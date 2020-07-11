# Ściąga - konstruktywny rachunek zdań

| polski          | wymowa             | Coq (nazwa) | jako cel | jako hipoteza | 
| --------------- | ------------------ | ----------- | -------- | -------- |
| implikacja      | jeżeli `P` to `Q` <br> `P` implikuje `Q` | `->` | `intro` <br> `intro H` <br> `intros` | `apply H` <br> `apply H1 in H2` <br> `specialize (H1 H2)` |
| koniunkcja      | `P` i `Q` <br> `P` oraz `Q` | `/\` <br> `and` | `split` | `destruct H as [H1 H2]` |
| dysjunkcja      | `P` lub `Q` | `\/` <br> `or` | `left` <br> `right` | `destruct H as [H1 | H2]` |
| równoważność logiczna | `P` wtedy i tylko wtedy, gdy `Q` | `<->` <br> `iff` | `split` | `destruct H as [H1 H2]` |
| prawda          | prawda <br> zdanie zawsze prawdziwe | true | `True` | `trivial` | `destruct H` |
| fałsz           | fałsz <br> zdanie zawsze fałszywe | false | `False` | nie da się | `contradiction` |

# Ściąga - konstruktywny rachunek predykatów

| polski          | wymowa             | Coq | jako cel | jako hipoteza |
| --------------- | ------------------ | --- | -------- | ------------- |
| kwantyfikator uniwersalny | dla każdego | `forall x : A, P x` | `intro` <br> `intros` | `apply H` <br> `apply H1 in H2` <br> `specialize (H1 H2)` |
| kwantyfikator egzystencjalny | istnieje | `exists x : A, P x` | `exists x` | `destruct H as [x Hx]` |
| równość         | `x` jest równe `y` | `x = y` <br> `eq` | `reflexivity` | `destruct H` <br> `rewrite H` <br> `rewrite H1 in H2` <br> `subst` |