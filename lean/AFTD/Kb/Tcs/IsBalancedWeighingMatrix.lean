import AFTD.Prelude

/-!
# is_balanced_weighing_matrix

Topic: combinatorics   Node: b4767d4e4623

Provenance: formalization of a published result. Source: arXiv:2611.17855, Section 2.1

A square matrix W of order v with entries in {-1, 0, 1} is a balanced weighing matrix with parameters (k, λ) if W Wᵀ = k I_v and |W| |W|ᵀ = (k - λ) I_v + λ J_v.
-/

/-- Predicate for a balanced weighing matrix of order v with parameters (k, λ). -/
def is_balanced_weighing_matrix (v : ℕ) (W : Matrix (Fin v) (Fin v) ℤ) (k lam : ℕ) : Prop :=
  (∀ i j, W i j ∈ ({-1, 0, 1} : Set ℤ)) ∧
  W * W.transpose = (k : ℤ) • (1 : Matrix (Fin v) (Fin v) ℤ) ∧
  (W.map (|·|)) * (W.map (|·|)).transpose =
    ((k : ℤ) - (lam : ℤ)) • (1 : Matrix (Fin v) (Fin v) ℤ) +
      (lam : ℤ) • (Matrix.of fun (_ _ : Fin v) => (1 : ℤ))
