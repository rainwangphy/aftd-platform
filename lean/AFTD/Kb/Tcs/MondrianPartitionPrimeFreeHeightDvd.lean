import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPartitionIsolatedHeightResidue
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectHeight

/-!
# mondrian_partition_prime_free_height_dvd

Topic: combinatorics   Node: b7fd25a360c0

Provenance: helper lemma. Helper for OP-280 and the periodic residue approach to arXiv:2610.19193, Section 1.

When d divides the square side, every common divisor of the heights of all other tiles with width indivisible by d also divides the height of a given tile whose width is indivisible by d.
-/

theorem mondrian_partition_prime_free_height_dvd (n d m : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P) (hdn : d ∣ n)
    (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P) (hrd : ¬ d ∣ mondrian_rect_width r)
    (hall : ∀ s ∈ P, s ≠ r → ¬ d ∣ mondrian_rect_width s → m ∣ mondrian_rect_height s) :
    m ∣ mondrian_rect_height r := by
  by_contra hrm
  have hothers : ∀ s ∈ P, s ≠ r → d ∣ mondrian_rect_width s ∨ m ∣ mondrian_rect_height s := by
    intro s hs hsr
    by_cases hw : d ∣ mondrian_rect_width s
    · exact Or.inl hw
    · exact Or.inr (hall s hs hsr hw)
  exact hrd (mondrian_partition_isolated_height_residue n d m P hP hdn r hr hrm hothers)
