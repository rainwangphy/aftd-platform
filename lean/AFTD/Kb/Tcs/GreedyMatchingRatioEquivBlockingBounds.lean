import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentBlockingBoundLe
import AFTD.Kb.Tcs.SegmentBlockingBoundGe
import AFTD.Kb.Tcs.IsHereditarySegmentProperty
import AFTD.Kb.Tcs.PointsInGeneralPosition
import AFTD.Kb.Tcs.GreedyMatching
import AFTD.Kb.Tcs.GreedyMatchingFractionGeOfBlockingLe
import AFTD.Kb.Tcs.GreedyMatchingFractionLeOfBlockingGe

/-!
# greedy_matching_ratio_equiv_blocking_bounds

Topic: online_algorithms   Node: 2fa0c1dc3e47

Provenance: formalization of a published result. Source: arXiv:2610.23130 Theorem 1.2

Theorem 1.2 (arXiv:2610.23130): Let P be a hereditary segment crossing property. (1) If the blocking number β_P(ℓ) ≤ p (every family of ℓ segments satisfying P blocks at most p points in general position), then on every input of points in general position on which Greedy creates ℓ segments, Greedy matches at least a 2ℓ / (2ℓ + p) fraction of the input points. (2) If β_P(ℓ) ≥ p (there exists a family of ℓ disjoint segments satisfying P blocking at least p points in general position), then there exists an input on which Greedy creates ℓ segments and matches at most a 2ℓ / (2ℓ + p) fraction of the input points.
-/

/-- Theorem 1.2: Equivalence between segment blocking numbers and Greedy competitive ratios. -/
theorem greedy_matching_ratio_equiv_blocking_bounds
    (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (hP : IsHereditarySegmentProperty P) (ℓ p : ℕ) :
    (segment_blocking_bound_le P ℓ p →
      ∀ pts : List (ℝ × ℝ), pts.Nodup → points_in_general_position (pts.toFinset : Set (ℝ × ℝ)) →
        (greedyMatching P pts).1.card = ℓ →
        (2 * (ℓ : ℝ)) / (2 * (ℓ : ℝ) + (p : ℝ)) ≤ (2 * (ℓ : ℝ)) / (pts.length : ℝ)) ∧
    (segment_blocking_bound_ge P ℓ p →
      ∃ pts : List (ℝ × ℝ), pts.Nodup ∧ points_in_general_position (pts.toFinset : Set (ℝ × ℝ)) ∧
        (greedyMatching P pts).1.card = ℓ ∧
        (2 * (ℓ : ℝ)) / (pts.length : ℝ) ≤ (2 * (ℓ : ℝ)) / (2 * (ℓ : ℝ) + (p : ℝ))) := by
  constructor
  · intro hβ pts h_nodup h_gen h_card
    exact greedy_matching_fraction_ge_of_blocking_le P hP ℓ p hβ pts h_nodup h_gen h_card
  · intro hβ
    exact greedy_matching_fraction_le_of_blocking_ge P hP ℓ p hβ
