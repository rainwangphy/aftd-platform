import AFTD.Prelude

/-!
# inst_decidableRel_pathGraph

Topic: quantum_mechanics   Node: 25f0b8fb1314

Provenance: helper lemma. step towards claw_free_tree_graph_state_mmi

Adjacency in the path graph `pathGraph n` is decidable.
-/

/-- Decidable adjacency for `SimpleGraph.pathGraph n`, from `pathGraph_adj`. -/
instance inst_decidableRel_pathGraph (n : ℕ) : DecidableRel (SimpleGraph.pathGraph n).Adj := fun _ _ => decidable_of_iff _ SimpleGraph.pathGraph_adj.symm
