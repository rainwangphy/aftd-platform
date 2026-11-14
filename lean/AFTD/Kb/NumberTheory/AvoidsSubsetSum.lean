import AFTD.Prelude

/-!
# avoids_subset_sum

Topic: elementary_number_theory   Node: 49a8c0685e92

Provenance: formalization of a published result. Source: arXiv:2611.17205 Forbidden subset sums in a linear range: an inverse theorem and the Erdős-Graham irregularity problem, Section 1.1

A finite set of natural numbers $A$ avoids a target integer $n$ if no subset of $A$ has sum equal to $n$, meaning every subset of $A$ summing to $n$ is empty.
-/

/-- A finite set of natural numbers avoids n if no subset sums to n. -/
def avoids_subset_sum (A : Finset ℕ) (n : ℕ) : Prop := ∀ B ⊆ A, B.sum id = n → B = ∅
