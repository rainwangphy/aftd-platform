import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeGraph

/-!
# maxcut_anchor_neutral_pivot_graph

Topic: equilibria   Node: 69c878b46dcb

Provenance: helper lemma. Experiments 16812 and 16814.

The known 91-vertex anchor graph with one extra edge from the first core vertex to a previously nonadjacent anchor of its displayed target color.
-/

def maxcut_anchor_neutral_pivot_graph : SimpleGraph (Fin 16 ⊕ (Fin 3 × Fin 25)) := SimpleGraph.fromRel (fun u v : (Fin 16 ⊕ (Fin 3 × Fin 25)) => maxcut_anchor_three_graph.Adj u v ∨ (u = (Sum.inl (0 : Fin 16) : (Fin 16 ⊕ (Fin 3 × Fin 25))) ∧ v = (Sum.inr ((2 : Fin 3), (24 : Fin 25)) : (Fin 16 ⊕ (Fin 3 × Fin 25)))))
