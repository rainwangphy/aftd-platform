import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BitwordNecklaceAdjacent
import AFTD.Kb.Tcs.BitwordIsRotation
import AFTD.Kb.Tcs.BitwordRotate

/-!
# brgc_necklace_order_not_consecutive_adjacent_six

Topic: combinatorics   Node: 0225bd51cbf4

Provenance: helper lemma. arXiv:2610.24758 (Optimal single-track Gray codes from Gray-ordered necklaces), Conjecture 1 and the remark after it; the paper names n = 9, 15, 21; n = 6 is the smallest failure (exp 1938)

Primality cannot be dropped from the adjacency conjecture: at n = 6 the consecutive necklaces 001001 and 011011 of D_6 (both periodic) are not adjacent in Q_6. This is the smallest n where it fails.
-/

instance brgc_necklace_order_not_consecutive_adjacent_six_dec_rot (n x y : ℕ) :
    Decidable (bitword_is_rotation n x y) := by
  unfold bitword_is_rotation
  infer_instance

instance brgc_necklace_order_not_consecutive_adjacent_six_dec_first_rank (n t : ℕ) :
    Decidable (brgc_necklace_first_rank n t) := by
  unfold brgc_necklace_first_rank
  infer_instance

instance brgc_necklace_order_not_consecutive_adjacent_six_dec_adj (n x y : ℕ) :
    Decidable (bitword_necklace_adjacent n x y) := by
  unfold bitword_necklace_adjacent
  infer_instance

theorem brgc_necklace_order_not_consecutive_adjacent_six :
    ¬ ∀ t t' : ℕ, brgc_necklace_first_rank 6 t → brgc_necklace_first_rank 6 t' → t < t' →
      (∀ s, t < s → s < t' → ¬ brgc_necklace_first_rank 6 s) →
      bitword_necklace_adjacent 6 (brgc_word t) (brgc_word t') := by
  intro H
  have h1 : brgc_necklace_first_rank 6 14 := by decide
  have h2 : brgc_necklace_first_rank 6 18 := by decide
  have h3 : 14 < 18 := by omega
  have h4 : ∀ s, 14 < s → s < 18 → ¬ brgc_necklace_first_rank 6 s := by
    intro s hs1 hs2
    interval_cases s
    · decide
    · decide
    · decide
  have h5 : ¬ bitword_necklace_adjacent 6 (brgc_word 14) (brgc_word 18) := by decide
  exact h5 (H 14 18 h1 h2 h3 h4)
