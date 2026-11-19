import AFTD.Prelude
import AFTD.Kb.Physics.Op2046Prob

/-!
# op2046_crossover_prob

Topic: quantum_mechanics   Node: a23ba2ed4dc4

Provenance: helper lemma. OP-2046; Gaussian Wishart definition in arXiv:2406.03335, Section 1.

The majorization probability at m equal to the natural-number floor of c n and h equal to the natural-number floor of t n^(1/3), with negative arguments truncated at zero.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

noncomputable def op2046_crossover_prob (n : ℕ) (c t : ℝ) : ℝ :=
  op2046_prob n ⌊c * n⌋₊ ⌊t * Real.rpow n (1 / 3 : ℝ)⌋₊
