| Nazwa (Coq)             | Definicja                                          | Relacja dualna <br> `N x y :≡ ~ R x y`| Nazwa relacji dualnej  |
| ----------------------- | -------------------------------------------------- | ------------------------------------- | ---------------------- |
| **Unikalność**                                                               |                                       |                        |
| `left_unique`           | `∀ (a1 a2 : A) (b : B), R a1 b → R a2 b → a1 = a2` | `∀ (a1 a2 : A) (b : B), a1 ≠ a2 → N a1 b ∨ N a2 b` |           |
| `right_unique`          | `∀ (a : A) (b1 b2 : B), R a b1 → R a b2 → b1 = b2` |                                       |                        |
| **Totalność**                                                                |                                       |                        |
| `left_total`            | `∀ a : A, ∃ b : B, R a b`                          |                                       |                        |
| `right_total`           | `∀ b : B, ∃ a : A, R a b`                          |                                       |                        |
| **Zwrotność**                                                                |                                       |                        |
| `reflexive`             | `∀ x, R x x` <br> `∀ x y, x = y → R x y`           | `∀ x, N x y → x ≠ y`                  | `antireflexive`        |
| `antireflexive`         | `∀ x, ~ R x x`                                     | `∀ x, N x x`                          | `reflexive`            |
| `irreflexive`           | `∃ x, ~ R x x`                                     |                                       |                        |
| `not_antireflexive`     | `∃ x, R x x`                                       |                                       |                        |
| `coreflexive`           | `∀ x y, R x y → x = y`                             | `∀ x y, x ≠ y → N x y`                | ???                    |
| `left_quasireflexive`   | `∀ x y, R x y → R x x`                             | `∀ x y, N x x → N x y`                | L. kwaziantyzwrotna??? |
| `right_quasireflexive`  | `∀ x y, R x y → R y y`                             | `∀ x y, N y y → N x y`                | R. kwaziantyzwrotna??? |
| `quasireflexive`        | `∀ x y, R x y → R x x ∧ R y y`                     | `∀ x y, N x x ∨ N y y → N x y`        | Kwaziantyzwrotna???    |
| **Symetria**                                                                 |                                       |                        |
| `symmetric`             | `∀ x y, R x y → R y x`                             | `∀ x y, N y x → N x y`                | równoważne `symmetric` |
| `antisymmetric`         | `∀ x y, R x y → R y x → ⊥`                         | `∀ x y, N x y ∨ N y x`                | `total`                |
| `weakly_antisymmetric`  | `∀ x y, R x y → R y x → x = y`                     | `∀ x y, x ≠ y → N x y ∨ N y x`        | `weakly_trichotomous`  |
| `asymmetric`            | `∃ x y, R x y ∧ ~ R y x`                           |                                       |                        |
| `not_antisymmetric`     | `∃ x y, R x y ∧ R y x`                             |                                       |                        |
| **Przechodniość**                                                            |                                       |                        |
| `transitive`            | `∀ x y z, R x y → R y z → R x z`                   | `∀ x y z, N x z → N x y ∨ N y z`      | `cotransitive`         |
| `antitransitive`        | `∀ x y z, R x y → R y z → R x z → ⊥`               | `∀ x y z, True → N x y ∨ N y z ∨ N x z` <br> `∀ x y z, N x y ∨ N y z ∨ N x z` | ??? |
| `weakly_antitransitive` | `∀ x y z, R x y → R y z → R x z → x = y ∧ y = z`   | `∀ x y z, x ≠ y ∨ y ≠ z ∨ x ≠ z → N x y ∨ N y z ∨ N x z` | ??? |
| `cotransitive`          | `∀ x y z, R x z → R x y ∨ R y z`                   | `∀ x y z, N x y ∧ N y z → N x z`      | `transitive`           |
| `quasitransitive`       | `Transitive (AsymmetricPart R)`                    |                                       |                        |
| trans. of incomparab.   | `TODO`                                             |                                       |                        |
| `intransitive`          | `∃ x y z, R x y ∧ R y z ∧ ~ R x z`                 |                                       |                        |
| `circular`              | `∀ x y z, R x y → R y z → R z x`                   | `∀ x y z, N z x → N x y ∨ N y z`      | ???                    |
| `right_euclidean`       | `∀ x y z, R x y → R x z → R y z`                   | `∀ x y z, N y z → N x y ∨ N x z`      | ???                    |
| `left_euclidean`        | `∀ x y z, R y x → R z x → R y z`                   |                                       |                        |
| **Konfluencja**                                                              |                                       |                        |
| `diamond`               | `∀ x y z, R x y → R x z → ∃ w, R y w ∧ R z w`      |                                       |                        |
| `locally_confluent`     | `∀ x y z, R x y → R x z → ∃ w, R* y w ∧ R* z w`    |                                       |                        |
| `confluent`             | `∀ x y z, R* x y → R* x z → ∃ w, R* y w ∧ R* z w`  |                                       |                        |
| **Gęstość**                                                                  |                                       |                        |
| `dense`                 | `∀ x y, R x y → ∃ z, R x z ∧ R z y`                |                                       |                        |
| **Totalność**                                                                |                                       |                        |
| `total`                 | `∀ x y, R x y ∨ R y x`                             | `∀ x y, N x y ∧ N y x → ⊥`            | `antisymmetric`        |
| `weakly_total`          | `∀ x y, ~ R x y → R y x`                           | `∀ x y, N y x → ~ N x y`              | `antisymmetric`        |
| `trichotomous`          | `∀ x y, R x y ∨ x = y ∨ R y x`                     | `∀ x y, N x y ∧ x ≠ y ∧ N y x → ⊥` <br> `∀ x y, N x y → N y x → ~ ~ x = y` | b. słaba antysymetria? |
| `weakly_trichotomous`   | `∀ x y, x ≠ y → R x y ∨ R y x`                     | `∀ x y, N x y ∧ N y x → x = y`        | `weakly_antisymmetric` |
| `connected`             | `∀ x y, ~ R x y ∧ ~ R y x → x = y`                 | `∀ x y, x ≠ y → ~ N x y ∨ ~ N y x`    | słaba `R`-trychotomia  |
| **Ekstensjonalność**                                                         |                                       |                        |
| `weakly_extensional`    | `∀ x y, (∀ t, R t x <-> R t y) → x = y`            | `∀ x y, x ≠ y → ∃ t, R t x xor R t y` | koekstensjonalność?    |
| **Ufundowanie**                                                              |                                       |                        |
| `well_founded`          | `∀ x, Acc R x`                                     | `ill_founded`                         | `ill_founded`          |
| `ill_founded`           | `∃ x, Inaccessible R x`                            | `well_founded`                        | `well_founded`         |

Znaczki: ∀∃→∨∧≠⊤⊥≡