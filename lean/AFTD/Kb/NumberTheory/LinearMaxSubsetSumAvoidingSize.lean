import AFTD.Prelude
import AFTD.Kb.NumberTheory.MaxSubsetSumAvoidingSize

/-!
# linear_max_subset_sum_avoiding_size

Topic: elementary_number_theory   Node: f1a871c440ab

Provenance: formalization of a published result. Source: arXiv:2611.17205 Forbidden subset sums in a linear range: an inverse theorem and the Erdős-Graham irregularity problem, Section 1.1

For a real number $c > 0$ and integer $n \ge 1$, $f_c(n)$ is the maximum cardinality of a subset of $\{1, \dots, \lfloor cn \rfloor\}$ avoiding subset sum $n$.
-/

/-- The maximum size f_c(n) of a subset of {1, ..., floor(cn)} avoiding subset sum n. -/
noncomputable def linear_max_subset_sum_avoiding_size (c : ℝ) (n : ℕ) : ℕ := max_subset_sum_avoiding_size ⌊c * (n : ℝ)⌋₊ n
