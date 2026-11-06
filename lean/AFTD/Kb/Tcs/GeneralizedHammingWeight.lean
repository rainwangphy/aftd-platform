import AFTD.Prelude

/-!
# generalizedHammingWeight

Topic: information   Node: 1deaaae08f30

Provenance: formalization of a published result. Source: Wei 1991, 'Generalized Hamming weights for linear codes', IEEE Trans. Inform. Theory; arXiv:2611.08203 Section 2.1

For a field K and a finite index set I with [Fintype I], the r-th generalized Hamming weight generalizedHammingWeight C r of a linear code C (a K-subspace of I → K) is the infimum in ℕ of the cardinalities of the supports of all r-dimensional K-subspaces D ≤ C, where the support of D is the set of indices i : I with f i ≠ 0 for some f ∈ D.
-/

/-- The r-th generalized Hamming weight of a linear code C in K^I over a finite index set I. -/
noncomputable def generalizedHammingWeight {I K : Type*} [Fintype I] [Field K] (C : Subspace K (I → K)) (r : ℕ) : ℕ := sInf { (@Finset.filter _ (fun i => ∃ f ∈ (D : Set (I → K)), f i ≠ 0) (fun _ => Classical.propDecidable _) Finset.univ).card | (D : Subspace K (I → K)) (_ : D ≤ C) (_ : Module.finrank K D = r) }
