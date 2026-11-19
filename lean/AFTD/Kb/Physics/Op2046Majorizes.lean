import AFTD.Prelude

/-!
# op2046_majorizes

Topic: quantum_mechanics   Node: 6dae3b1f82cc

Provenance: helper lemma. OP-2046; Gaussian Wishart definition in arXiv:2406.03335, Section 1.

For two real vectors with positive sums, every subset sum of the second normalized vector is bounded by some same-cardinality subset sum of the first normalized vector. Equivalently, the first normalized vector majorizes the second.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

noncomputable def op2046_majorizes (n : ℕ) (x y : Fin n → ℝ) : Prop :=
  0 < (∑ i, x i) ∧ 0 < (∑ i, y i) ∧
  ∀ T : Finset (Fin n), ∃ S : Finset (Fin n), S.card = T.card ∧
    (∑ i ∈ T, y i) / (∑ i, y i) ≤ (∑ i ∈ S, x i) / (∑ i, x i)
