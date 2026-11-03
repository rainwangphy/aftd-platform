import AFTD.Prelude

/-!
# digraph_robust_pair_source16_graph

Topic: graphs   Node: ad06b200045b

Provenance: helper lemma. Finite pair-deletion obstruction for the four-cycle campaign; experiments 13432 and 13435.

The seven-regular cyclic tournament on fifteen vertices with one additional source pointing to all fifteen tournament vertices.
-/

def digraph_robust_pair_source16_graph : Digraph (Fin 16) where
  Adj u v := v ≠ 15 ∧ (u = 15 ∨ (u ≠ 15 ∧ 1 ≤ (v.val + 15 - u.val) % 15 ∧ (v.val + 15 - u.val) % 15 ≤ 7))
