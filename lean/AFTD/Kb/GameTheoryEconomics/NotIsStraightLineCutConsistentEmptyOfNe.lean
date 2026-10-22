import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent
import AFTD.Kb.GameTheoryEconomics.StraightLine

/-!
# not_is_straight_line_cut_consistent_empty_of_ne

Topic: fair_division   Node: ccb36787c228

Provenance: helper lemma. arXiv:2610.27956 Section 1.1

For any two points p, q in ℝ × ℝ, any natural number k, and any allocation α : (ℝ × ℝ) → Fin k, if α p ≠ α q, then the two-element finite set {p, q} is not consistent with the empty finite set of straight lines ∅ under α: ¬ is_straight_line_cut_consistent {p, q} ∅ α.
-/

/-- Two points assigned to different agents cannot be consistently allocated using zero straight-line cuts. -/
theorem not_is_straight_line_cut_consistent_empty_of_ne (p q : ℝ × ℝ) {k : ℕ}
    (α : (ℝ × ℝ) → Fin k) (hα : α p ≠ α q) :
    ¬ is_straight_line_cut_consistent {p, q} ∅ α := by
  intro ⟨s, _, h2⟩
  have hp : p ∈ ({p, q} : Finset (ℝ × ℝ)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (ℝ × ℝ)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  exact hα (h2 p hp q hq fun ℓ hℓ => (Finset.notMem_empty ℓ hℓ).elim)
