import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinTableauxCount
import AFTD.Kb.Tcs.LatinDoubleThreeTailCountBase
import AFTD.Kb.Tcs.LatinDoubleThreeTailCountStep
import AFTD.Kb.Tcs.LatinDoubleThreeTailFourExtensions
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinTopRowAvailability

/-!
# latin_double_three_tail_count_formula

Topic: combinatorics   Node: c208b6d32a3c

Provenance: original. Related work: The explicitly open Conjecture 6.3 of https://arxiv.org/html/2610.29291v1. This is the paper's conjecture, not a theorem it proves and not a conjecture originating here. The pointwise four-extension and column-profile proof route was proposed here in experiments 4100, 4103 and 4106.

The open formula in arXiv:2610.29291 Conjecture 6.3: the number of Latin tableaux of shape (k,k-1,...,4,3,3) is 9 times 4 to the power k-3 for every k at least 5.
-/

theorem latin_double_three_tail_count_formula (k : ℕ) (hk : 5 ≤ k) : latin_tableaux_count (latin_double_three_tail_shape k) = 9 * 4^(k-3) := by
  induction' hk with k hk ih
  · rw [latin_double_three_tail_count_base]
    norm_num
  · have hk_le : 5 ≤ k := hk
    rw [latin_double_three_tail_count_step k hk_le]
    have h_four : ∀ T ∈ latin_tableaux (latin_double_three_tail_shape k),
        (latin_top_row_availability (latin_double_three_tail_shape k) T (k + 1)).permanent = 4 :=
      latin_double_three_tail_four_extensions k hk_le
    rw [Finset.sum_congr rfl h_four]
    rw [Finset.sum_const, nsmul_eq_mul]
    change latin_tableaux_count (latin_double_three_tail_shape k) * 4 = 9 * 4 ^ (k + 1 - 3)
    rw [ih]
    have h_exp : k + 1 - 3 = (k - 3) + 1 := by omega
    rw [h_exp, pow_succ]
    ring
