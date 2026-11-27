import AFTD.Prelude
import AFTD.Kb.Tcs.PrimeConvolutionChoi
import AFTD.Kb.Tcs.TwoLevelEnvironment
import AFTD.Kb.Tcs.MatrixIsSeparable
import AFTD.Kb.Tcs.MatrixIsSeparablePosSemidef
import AFTD.Kb.Tcs.PrimeConvolutionChoiPptIffThreshold
import AFTD.Kb.Tcs.MatrixIsSeparablePartialTransposeIff

/-!
# prime_convolution_separable_imp_threshold

Topic: quantum   Node: 3ee2159970b3

Provenance: helper lemma. OP-2466: the necessity half of the entry (entanglement breaking implies the threshold), from separable ⇒ PPT and the PPT boundary.

Let d be a prime with d ≥ 5, r ∈ ZMod d with r ≠ 0, r ≠ 1 and 2r ≠ 1 (r is not the inverse of 2), and p, t real numbers in [0, 1]. If prime_convolution_choi d r (two_level_environment d p t) is separable then t ≤ 1/(1 + d·√(p(1 − p))).
-/

theorem prime_convolution_separable_imp_threshold :
    ∀ d : ℕ, d.Prime → 5 ≤ d → ∀ r : ZMod d, r ≠ 0 → r ≠ 1 → 2 * r ≠ 1 →
      ∀ p t : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ t → t ≤ 1 →
        matrix_is_separable d d (prime_convolution_choi d r (two_level_environment d p t)) →
          t ≤ 1 / (1 + d * Real.sqrt (p * (1 - p))) := by
  intro d hd h5 r hr0 hr1 hr2 p t hp0 hp1 ht0 ht1 hsep
  have h := (matrix_is_separable_partial_transpose_iff d d _).mp hsep
  exact (prime_convolution_choi_ppt_iff_threshold d hd h5 r hr0 hr1 hr2 p t hp0 hp1 ht0 ht1).mp
    (matrix_is_separable_pos_semidef d d _ h)
