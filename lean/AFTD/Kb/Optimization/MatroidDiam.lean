import AFTD.Prelude

/-!
# matroid_diam

Topic: submodular   Node: c8eceb1c6d02

Provenance: formalization of a published result. Source: arXiv:2611.27934, Section 2

For a matroid M on a type α, the diameter matroid_diam M is defined as the supremum in ℕ of the set of cardinalities (A \ B).ncard over all pairs of subsets A, B : Set α such that both A and B are bases of M (M.IsBase A and M.IsBase B).
-/

/-- The diameter of a matroid M: the supremum in ℕ of (A \ B).ncard over all pairs of bases A, B of M. -/
noncomputable def matroid_diam {α : Type*} (M : Matroid α) : ℕ := sSup { (A \ B).ncard | (A : Set α) (B : Set α) (_ : M.IsBase A) (_ : M.IsBase B) }
