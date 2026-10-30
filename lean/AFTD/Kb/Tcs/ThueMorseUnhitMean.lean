import AFTD.Prelude
import AFTD.Kb.Tcs.ThueMorseMinFactorCoveragesFinset

/-!
# thue_morse_unhit_mean

Topic: combinatorics   Node: de1034d28f9c

Provenance: helper lemma. step towards thue_morse_random_attractor_lattice_gumbel

The expected number of unhit inclusion-minimal factor coverages of t_n under a uniformly random k-tuple of positions: the sum over C in H_min(t_n) of (1 - |C|/2^n)^k.
-/

/-- The expected number of inclusion-minimal factor coverages of t_n left unhit by a uniform random k-tuple of positions. -/
noncomputable def thue_morse_unhit_mean (n k : ℕ) : ℝ := ∑ C ∈ thue_morse_min_factor_coverages_finset n,
      ((1 : ℝ) - (C.card : ℝ) / (2 : ℝ) ^ n) ^ k
