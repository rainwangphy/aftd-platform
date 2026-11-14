import AFTD.Prelude

/-!
# seven_triple_system_not_two_colorable

Topic: combinatorics   Node: 54c89a9df8e9

Provenance: helper lemma. Classical seven-point triple system; explicitly tested in experiment 26841.

For the seven displayed triples on seven points, every two-coloring of the points makes at least one triple monochromatic.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem seven_triple_system_not_two_colorable : let L : Fin 7 → Finset (Fin 7) := ![({0,1,2} : Finset (Fin 7)), {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}]; ∀ A : Finset (Fin 7), ∃ i : Fin 7, L i ⊆ A ∨ Disjoint (L i) A := by
  decide
