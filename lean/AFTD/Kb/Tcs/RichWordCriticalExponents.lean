import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniformlyRecurrentWord
import AFTD.Kb.Tcs.IsRichWord
import AFTD.Kb.Tcs.WordCriticalExponent

/-!
# rich_word_critical_exponents

Topic: combinatorics   Node: 765e13f4836e

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 8

For any positive integer d, the set S_d of critical exponents of uniformly recurrent d-ary rich words is the collection of all real numbers E(w) where w : ℕ → Fin d is a uniformly recurrent rich word.
-/

/-- The set S_d of critical exponents of uniformly recurrent d-ary rich words. -/
def rich_word_critical_exponents (d : ℕ) : Set ℝ := { e : ℝ | ∃ w : ℕ → Fin d, is_uniformly_recurrent_word w ∧ is_rich_word w ∧ e = word_critical_exponent w }
