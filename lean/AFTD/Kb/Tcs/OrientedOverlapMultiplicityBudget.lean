import AFTD.Prelude

/-!
# oriented_overlap_multiplicity_budget

Topic: combinatorics   Node: 5f33b10a3031

Provenance: helper lemma. Finite arithmetic helper for the oriented small-overlap packing route to OP-110.

Summed multiplicities and charges cost at most three times overlap when multiplicity-two edges have at most one charge.
-/

private theorem in504_overlap_edge_budget (m c : ℕ)
    (hm : 2 ≤ m) (hc : c ≤ m) (h2 : m = 2 → c ≤ 1) :
    m + c ≤ 3 * (m - 1) := by
  by_cases h : m = 2
  · have := h2 h
    omega
  · omega

theorem oriented_overlap_multiplicity_budget
    (ι : Type) [DecidableEq ι] (S : Finset ι) (m c : ι → ℕ)
    (hm : ∀ e ∈ S, 2 ≤ m e)
    (hc : ∀ e ∈ S, c e ≤ m e)
    (h2 : ∀ e ∈ S, m e = 2 → c e ≤ 1) :
    (∑ e ∈ S, m e) + (∑ e ∈ S, c e) ≤ 3 * ∑ e ∈ S, (m e - 1) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  exact in504_overlap_edge_budget (m e) (c e) (hm e he) (hc e he) (h2 e he)
