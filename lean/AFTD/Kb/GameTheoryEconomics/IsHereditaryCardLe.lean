import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsHereditary

/-!
# is_hereditary_card_le

Topic: fair_division   Node: 286b7dbd3df7

Provenance: helper lemma. arXiv:2611.34488, Section 2

For any bound B : ℕ, the family of all finsets of cardinality at most B is hereditary.
-/

/-- Subsets of cardinality at most B form a hereditary family. -/
theorem is_hereditary_card_le {α : Type*} (B : ℕ) :
    is_hereditary {S : Finset α | S.card ≤ B} := by
  constructor
  · simp
  · intro S T hS hTS
    simp only [Set.mem_ofPred_eq] at hS ⊢
    exact le_trans (Finset.card_le_card hTS) hS
