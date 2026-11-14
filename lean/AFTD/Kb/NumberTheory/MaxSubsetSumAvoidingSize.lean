import AFTD.Prelude
import AFTD.Kb.NumberTheory.SubsetSumAvoiders

/-!
# max_subset_sum_avoiding_size

Topic: elementary_number_theory   Node: 54d93557a199

Provenance: formalization of a published result. Source: arXiv:2611.17205 Forbidden subset sums in a linear range: an inverse theorem and the Erdős-Graham irregularity problem, Section 1.1

For positive integers $M$ and $n$, $F(M, n)$ is the maximum cardinality of a subset of $\{1, \dots, M\}$ that avoids subset sum $n$.
-/

/-- The maximum cardinality of a subset of {1, ..., M} avoiding subset sum n. -/
noncomputable def max_subset_sum_avoiding_size (M n : ℕ) : ℕ := Finset.sup (subset_sum_avoiders M n) Finset.card
