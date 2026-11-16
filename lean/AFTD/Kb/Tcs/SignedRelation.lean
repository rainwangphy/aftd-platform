import AFTD.Prelude
import AFTD.Kb.Tcs.TriangularNumber
import AFTD.Kb.Tcs.DualCertP

/-!
# signed_relation

Topic: combinatorics   Node: fcc47bbbcdce

Provenance: formalization of a published result. Source: arXiv:2611.17360 Definition 3.1

For a dimension n : ℕ, an index j : ℕ, and a vector x : Fin n → ℝ, signed_relation n j x is the real number (∑ t ∈ Finset.range p, coord (j + t)) - coord (j - 1) - ∑ k ∈ Finset.range (p - 1), coord (n - triangular_number k), where m = n - j + 1, p = dual_cert_p m, and coord i is defined as x ⟨i - 1, by omega⟩ if 1 ≤ i ≤ n and 0 otherwise.
-/

/-- The j-th signed linear relation on a vector x : Fin n → ℝ. -/
def signed_relation (n : ℕ) (j : ℕ) (x : Fin n → ℝ) : ℝ :=
  let m := n - j + 1
  let p := dual_cert_p m
  let coord : ℕ → ℝ := fun i => if h : 0 < i ∧ i ≤ n then x ⟨i - 1, by omega⟩ else 0
  (∑ t ∈ Finset.range p, coord (j + t)) - coord (j - 1) - ∑ k ∈ Finset.range (p - 1), coord (n - triangular_number k)
