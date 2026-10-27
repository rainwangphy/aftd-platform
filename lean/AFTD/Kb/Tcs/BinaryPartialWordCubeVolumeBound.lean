import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCubePacking

/-!
# binary_partial_word_cube_volume_bound

Topic: combinatorics   Node: 625911eed8c5

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

The sum of 2 to the negative support sizes of pairwise conflicting finite partial words is at most one.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_volume_bound {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v) :
    ∑ i, (1 : ℚ) / 2 ^ (s i).card ≤ 1 := by
  have hpack := binary_partial_word_cube_packing s b hconflict
  have he (i : I) : (2 : ℚ) ^ (Fintype.card V - (s i).card) =
      2 ^ Fintype.card V * (1 / 2 ^ (s i).card) := by
    rw [pow_sub₀ _ (by norm_num) (card_le_univ _)]
    simp only [one_div]
  simp_rw [he] at hpack
  rw [← mul_sum] at hpack
  have hp : (0 : ℚ) < 2 ^ Fintype.card V := by positivity
  nlinarith
