import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# card_candidate_links_le_sq

Topic: online_algorithms   Node: 0ae18b71c3c9

Provenance: helper lemma. arXiv:2611.08570 Section 1.2.2 & Theorem 1.10

For every natural number n and every finite set L of pairs of integers (i, j) satisfying 0 ≤ i < j < n, the cardinality of L is at most n * n.
-/

/-- Every candidate link set L on an n-vertex cycle with 0 ≤ i < j < n has cardinality at most n^2. -/
theorem card_candidate_links_le_sq (n : ℕ) (L : Finset (ℤ × ℤ))
    (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < (n : ℤ)) :
    L.card ≤ n * n := by
  have h_sub : L ⊆ Finset.Ico (0 : ℤ) (n : ℤ) ×ˢ Finset.Ico (0 : ℤ) (n : ℤ) := by
    intro p hp
    have ⟨h1, h2, h3⟩ := hL p hp
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
    exact ⟨⟨h1, lt_trans h2 h3⟩, ⟨le_trans h1 (le_of_lt h2), h3⟩⟩
  have h_card := Finset.card_le_card h_sub
  simp only [Finset.card_product, Int.card_Ico, sub_zero, Int.toNat_natCast] at h_card
  exact h_card
