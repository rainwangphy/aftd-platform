import AFTD.Prelude

/-!
# permutahedron_slack_matrix

Topic: integer_programming   Node: d21164067b53

Provenance: formalization of a published result. Source: arXiv:2610.04498 Eq. 18

For a natural number n, the slack matrix of the standard permutahedron on n elements is the real matrix whose rows are indexed by nonempty proper subsets S of Fin n and whose columns are indexed by permutations σ of Fin n, whose entry at (S, σ) is (∑ i ∈ S, ((σ i).val + 1 : ℝ)) - (Nat.choose (S.card + 1) 2 : ℝ).
-/

/-- The slack matrix of the standard permutahedron on n elements. -/
def permutahedron_slack_matrix (n : ℕ) : Matrix {S : Finset (Fin n) // S.Nonempty ∧ S ≠ Finset.univ} (Equiv.Perm (Fin n)) ℝ := fun S σ => (∑ i ∈ S.val, ((σ i).val + 1 : ℝ)) - (Nat.choose (S.val.card + 1) 2 : ℝ)
