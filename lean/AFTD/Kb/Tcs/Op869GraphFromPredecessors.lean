import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op869_graph_from_predecessors

Topic: online_algorithms   Node: 3a2f39d75bff

Provenance: helper lemma. arXiv:2610.41516, Sections 1 and 2; formal infrastructure for the adaptive online-coloring construction.

The simple graph on the ordered vertices Fin n whose edge from an earlier vertex a to a later vertex b exists exactly when a is in the predecessor set of b.
-/

def op869_graph_from_predecessors {n : ℕ} (P : Fin n → Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj a b := (a < b ∧ a ∈ P b) ∨ (b < a ∧ b ∈ P a)
  symm := by
    constructor
    intro a b h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := by
    constructor
    intro a
    simp
