import AFTD.Prelude
import AFTD.Kb.Physics.SeedTree1
import AFTD.Kb.Physics.ChainGraph

/-!
# chain_tree_1

Topic: quantum_mechanics   Node: 947d27d1c722

Provenance: formalization of a published result. Source: knowledgebase: OP-828

For any k, chain_tree_1 k is the graph formed by joining k copies of seed_tree_1 in a chain at vertex 9.
-/

/-- The k-unit chain tree T_k built from seed_tree_1 joined at marked vertex 9. -/
def chain_tree_1 (k : ℕ) : SimpleGraph (Fin k × Fin 16) := chain_graph seed_tree_1 ⟨9, by omega⟩ k
