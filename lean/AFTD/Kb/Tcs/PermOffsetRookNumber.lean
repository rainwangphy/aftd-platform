import AFTD.Prelude

/-!
# perm_offset_rook_number

Topic: combinatorics   Node: 0d69823b415e

Provenance: formalization of a published result. Source: arXiv:2610.23958 Definition 2.2 and Equation (2)

Given a natural number n, a finite subset S ⊆ ℤ, and k ∈ ℕ, perm_offset_rook_number n S k is the number of k-element subsets R of cells (i, j) ∈ Fin n × Fin n satisfying ∃ s ∈ S, (n : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) - s, such that no two distinct elements of R share a row or a column (∀ c1 c2 ∈ R, c1 ≠ c2 → c1.1 ≠ c2.1 ∧ c1.2 ≠ c2.2).
-/

/-- The k-th rook number r_k(n, S): number of k-element nonattacking placements on the forbidden board of cells (i, j) with n dividing j - i - s for some s in S. -/
def perm_offset_rook_number (n : ℕ) (S : Finset ℤ) (k : ℕ) : ℕ :=
  open Classical in
  (((Finset.univ : Finset (Fin n × Fin n)).filter (fun c =>
    ∃ s ∈ S, (n : ℤ) ∣ ((c.2 : ℕ) : ℤ) - ((c.1 : ℕ) : ℤ) - s)).powersetCard k).filter (fun R =>
    ∀ c1 ∈ R, ∀ c2 ∈ R, c1 ≠ c2 → c1.1 ≠ c2.1 ∧ c1.2 ≠ c2.2) |>.card
