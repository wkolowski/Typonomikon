# Ściąga - konstruktywny rachunek zdań

| polski (wymowa) | angielski (wymowa) | Coq (nazwa) | jako cel | jako hipoteza | 
| --------------- | ------------------ | ----------- | -------- | -------- |
| implikacja (jeżeli P to Q, P implikuje Q) | implication (if P then Q, P implies Q) | `->` | `intro`, `intro H`, `intros` | `apply H`, `apply H1 in H2`, `specialize (H1 H2)` |
| koniunkcja (P i Q, P oraz Q) | conjunction (P and Q) | `/\` (`and`) | `split` | `destruct H as [H1 H2]` |
| dysjunkcja (P lub Q) | disjunction (P or Q) | `\/` (`or`) | `left`, `right` | `destruct H as [H1 | H2]` |
| równoważność logiczna (P wtedy i tylko wtedy, gdy Q) | logical equivalence (P if and only if Q) | `<->` (`iff`) | `split` | `destruct H as [H1 H2]` |
| prawda, zdanie zawsze prawdziwe | true | `True` | `trivial` | `destruct H` |
| fałsz, zdanie zawsze fałszywe | false | `False` | nie da się | `contradiction` |