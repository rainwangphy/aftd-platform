import AFTD.Prelude
import AFTD.Kb.Physics.SeedTree2
import AFTD.Kb.Physics.ChainGraph

/-!
# chain_tree_2

Topic: quantum_mechanics   Node: c137926de3ce

Provenance: formalization of a published result. Source: knowledgebase: OP-828

For any k, chain_tree_2 k is the graph formed by joining k copies of seed_tree_2 in a chain at vertex 1.
-/

/-- The k-unit chain tree T'_k built from seed_tree_2 joined at marked vertex 1. -/
def chain_tree_2 (k : ℕ) : SimpleGraph (Fin k × Fin 16) := chain_graph seed_tree_2 ⟨1, by omega⟩ k
