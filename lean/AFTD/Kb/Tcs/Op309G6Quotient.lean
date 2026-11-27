import AFTD.Prelude

/-!
# op309_g6_quotient

Topic: graphs   Node: 0615cc035881

Provenance: helper lemma. step towards op309_girth6_source_forest_clique5_nonfive_example

The quotient graph on eight classes: vertices 0,1,2 are pairwise adjacent and adjacent to all of 3,4,5,6,7, and 3-4-5-6-7-3 is a five-cycle (K3 joined to C5).
-/

/-- The eight-vertex quotient graph K3 joined to the five-cycle 3-4-5-6-7-3, with concrete adjacency given by a pair list. -/
def op309_g6_quotient : SimpleGraph (Fin 8) := SimpleGraph.fromRel fun x y =>
  (x.val, y.val) ∈ ([(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (4,5), (5,6), (6,7), (3,7)] : List (ℕ × ℕ))
