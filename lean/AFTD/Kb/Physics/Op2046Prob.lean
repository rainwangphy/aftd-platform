import AFTD.Prelude
import AFTD.Kb.Physics.Op2046Matrix
import AFTD.Kb.Physics.Op2046Spectrum
import AFTD.Kb.Physics.Op2046Majorizes

/-!
# op2046_prob

Topic: quantum_mechanics   Node: 3bfd20a14e8d

Provenance: helper lemma. OP-2046; Gaussian Wishart definition in arXiv:2406.03335, Section 1.

The probability that the first trace-normalized Gram spectrum majorizes the second, for independent complex standard Gaussian n by m and n by m+h matrices. Every real and imaginary coordinate is independent normal with mean zero and variance one half; outcomes with either trace zero are excluded.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

noncomputable def op2046_prob (n m h : ℕ) : ℝ :=
  let μ : Measure ((Fin n × Fin m × Fin 2) → ℝ) :=
    Measure.pi (fun _ => gaussianReal 0 (1 / 2))
  let ν : Measure ((Fin n × Fin (m+h) × Fin 2) → ℝ) :=
    Measure.pi (fun _ => gaussianReal 0 (1 / 2))
  ((μ.prod ν) {z | op2046_majorizes n (op2046_spectrum n m z.1)
    (op2046_spectrum n (m+h) z.2)}).toReal
