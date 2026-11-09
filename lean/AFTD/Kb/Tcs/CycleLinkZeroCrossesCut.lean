import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_link_zero_crosses_cut

Topic: online_algorithms   Node: c16365ff53b1

Provenance: helper lemma. arXiv:2611.08570, Theorem 5.4

For integers v, a, b, n satisfying 0 < v < n and 1 ≤ a ≤ v ≤ b < n, the candidate link (0, v) crosses the cycle cut [a, b], that is, (a ≤ 0 ∧ 0 ≤ b) ↔ ¬(a ≤ v ∧ v ≤ b).
-/

/-- A link with endpoints 0 and v in [a, b] crosses the cycle cut [a, b]. -/
theorem cycle_link_zero_crosses_cut (v a b n : ℤ)
    (h_v : 0 < v ∧ v < n) (h_c : 1 ≤ a ∧ a ≤ v ∧ v ≤ b ∧ b < n) :
    ((a ≤ 0 ∧ 0 ≤ b) ↔ ¬(a ≤ v ∧ v ≤ b)) := by
  obtain ⟨ha, hav, hvb, -⟩ := h_c
  constructor
  · rintro ⟨ha0, -⟩
    linarith
  · intro h
    exact (h ⟨hav, hvb⟩).elim
