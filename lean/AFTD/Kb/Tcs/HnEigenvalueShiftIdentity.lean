import AFTD.Prelude

/-!
# hn_eigenvalue_shift_identity

Topic: graphs   Node: c42b2f6d1319

Provenance: helper lemma. arXiv:2610.18636 Theorem 5 proof

For any natural number n and real numbers l1, l2, l3, if l1 + l2 + l3 = n and Lam = 2 * (n : ℝ) - l1, then (n : ℝ) + l3 = Lam - l2.
-/

/-- Eigenvalue shift identity n + l3 = Lam - l2 from the eigenvalue sum. -/
theorem hn_eigenvalue_shift_identity (n : ℕ) (l1 l2 l3 : ℝ)
    (hsum : l1 + l2 + l3 = (n : ℝ)) :
    let Lam := 2 * (n : ℝ) - l1
    (n : ℝ) + l3 = Lam - l2 := by
  intro Lam
  linarith
