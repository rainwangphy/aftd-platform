import AFTD.Prelude
import AFTD.Kb.Tcs.ColorAvoidingSubgraph

/-!
# weakened_cycle_ramsey_property

Topic: combinatorics   Node: 3acbe90983b5

Provenance: formalization of a published result. Source: arXiv:2611.11187, Section 1 and Section 2.1

The weakened cycle Ramsey property weakened_cycle_ramsey_property t ℓ n holds if every t-edge-colouring of the complete graph K_n contains a cycle of length ℓ whose edges use at most t - 1 colours (that is, avoids at least one colour).
-/

/-- Property that every t-edge-colouring of K_n contains a cycle of length ℓ avoiding some colour. -/
def weakened_cycle_ramsey_property (t ℓ n : ℕ) : Prop := ∀ c : (SimpleGraph.completeGraph (Fin n)).edgeSet → Fin t,
    ∃ j : Fin t, SimpleGraph.IsContained (SimpleGraph.cycleGraph ℓ) (color_avoiding_subgraph (SimpleGraph.completeGraph (Fin n)) c j)
