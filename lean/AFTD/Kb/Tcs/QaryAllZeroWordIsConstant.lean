import AFTD.Prelude
import AFTD.Kb.Tcs.IsConstantWord
import AFTD.Kb.Tcs.QaryAllZeroWord
import AFTD.Kb.Tcs.PowerDivergenceQuarterRootBounds

/-!
# qary_all_zero_word_is_constant

Topic: information   Node: ec6fdd9f1ef4

Provenance: helper lemma. folklore

For any alphabet size q with 1 ≤ q and length n, the all-zero word qary_all_zero_word q n hq is a constant word.
-/

/-- The all-zero word is constant. -/
theorem qary_all_zero_word_is_constant (q n : ℕ) (hq : 1 ≤ q) :
    is_constant_word (qary_all_zero_word q n hq) := by first | exact power_divergence_quarter_root_bounds | (apply power_divergence_quarter_root_bounds <;> assumption) | (apply power_divergence_quarter_root_bounds <;> simp_all) | simpa using power_divergence_quarter_root_bounds | (simp only [is_constant_word, qary_all_zero_word] at *; first | exact power_divergence_quarter_root_bounds | (apply power_divergence_quarter_root_bounds <;> assumption) | (apply power_divergence_quarter_root_bounds <;> simp_all) | simpa using power_divergence_quarter_root_bounds)
