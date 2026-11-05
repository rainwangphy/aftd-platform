import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# integer_interval_subset_of_nonempty_inter_of_no_endpoints

Topic: data_structures   Node: 3a9e58d18c7c

Provenance: helper lemma. arXiv:2611.03620 Appendix B

If an integer interval [a, b] intersects [l, r] and contains neither endpoint l nor r, then [a, b] is contained in [l, r].
-/

/-- An integer interval intersecting another integer interval and containing neither of its endpoints is a subset. -/
theorem integer_interval_subset_of_nonempty_inter_of_no_endpoints
    (a b l r : ℤ) (_hab : a ≤ b) (_hlr : l ≤ r)
    (h_inter : ∃ x : ℤ, x ∈ Set.Icc a b ∧ x ∈ Set.Icc l r)
    (hl : l ∉ Set.Icc a b) (hr : r ∉ Set.Icc a b) :
    Set.Icc a b ⊆ Set.Icc l r := by
  intro y hy
  rw [Set.mem_Icc] at hy hl hr ⊢
  rcases h_inter with ⟨x, hxab, hxlr⟩
  rw [Set.mem_Icc] at hxab hxlr
  constructor <;> omega
