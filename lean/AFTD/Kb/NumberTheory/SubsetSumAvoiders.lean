import AFTD.Prelude
import AFTD.Kb.NumberTheory.AvoidsSubsetSum

/-!
# subset_sum_avoiders

Topic: elementary_number_theory   Node: 5124a02ade53

Provenance: formalization of a published result. Source: arXiv:2611.17205 Forbidden subset sums in a linear range: an inverse theorem and the Erdős-Graham irregularity problem, Section 1.1

The collection of all subsets of $\{1, \dots, M\}$ that avoid subset sum $n$.
-/

/-- The collection of all subsets of {1, ..., M} that avoid subset sum n. -/
noncomputable def subset_sum_avoiders (M n : ℕ) : Finset (Finset ℕ) := @Finset.filter (Finset ℕ) (fun A => avoids_subset_sum A n) (Classical.decPred _) (Finset.Icc 1 M).powerset
