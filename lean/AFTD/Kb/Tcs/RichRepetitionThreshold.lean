import AFTD.Prelude
import AFTD.Kb.Tcs.RichWordCriticalExponents

/-!
# rich_repetition_threshold

Topic: combinatorics   Node: d403caeb906f

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 1, Sec. 8

The repetition threshold RT(C_d) for d-ary rich words is the infimum of the set S_d of critical exponents of uniformly recurrent d-ary rich words.
-/

/-- The repetition threshold for d-ary rich words is the infimum of S_d. -/
noncomputable def rich_repetition_threshold (d : ℕ) : ℝ := sInf (rich_word_critical_exponents d)
