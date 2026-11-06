import AFTD.Prelude

/-!
# sumset_sum_vectors_finset

Topic: combinatorics   Node: 94a2719d6f53

Provenance: original. Related work: arXiv:2611.07303, Section 1 (line 138)

For natural numbers h and k, the finite set sumset_sum_vectors_finset h k is the finset of all vectors x : Fin k → ℤ with components in {0, ..., h} such that ∑ i, x i = (h : ℤ).
-/

/-- The finite set of sum vectors X_{h,k}: vectors in (Fin k → ℤ) with entries in [0, h] summing to h. -/
def sumset_sum_vectors_finset (h k : ℕ) : Finset (Fin k → ℤ) := (Fintype.piFinset fun _ : Fin k => (Finset.range (h + 1)).image (fun (n : ℕ) => (n : ℤ))).filter fun x => ∑ i, x i = (h : ℤ)
