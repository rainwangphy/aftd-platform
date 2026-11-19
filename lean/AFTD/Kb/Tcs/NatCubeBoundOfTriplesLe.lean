import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# nat_cube_bound_of_triples_le

Topic: information   Node: 6687db50fa50

Provenance: helper lemma. arXiv:2611.21275, Proposition 18

For natural numbers n and r with 3 ≤ n, if n * (n - 1) * (n - 2) ≤ r ^ 3 - 2, then n ≤ r + 1.
-/

/-- If n ≥ 3 and n(n - 1)(n - 2) ≤ r^3 - 2, then n ≤ r + 1. -/
theorem nat_cube_bound_of_triples_le {n r : ℕ} (hn : 3 ≤ n) (h : n * (n - 1) * (n - 2) ≤ r ^ 3 - 2) : n ≤ r + 1 := by
  by_contra hcon
  push Not at hcon
  have h1 : r + 2 ≤ n := by omega
  have h2 : r + 1 ≤ n - 1 := by omega
  have h3 : r ≤ n - 2 := by omega
  have hprod : (r + 2) * (r + 1) * r ≤ n * (n - 1) * (n - 2) := by
    calc (r + 2) * (r + 1) * r ≤ n * (n - 1) * r := by
          exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (le_refl r)
      _ ≤ n * (n - 1) * (n - 2) := by
          exact Nat.mul_le_mul (le_refl (n * (n - 1))) h3
  have hcube : (r + 2) * (r + 1) * r ≤ r ^ 3 :=
    le_trans (le_trans hprod h) (Nat.sub_le _ _)
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    have hn1 : 0 < n := by omega
    have hn2 : 0 < n - 1 := by omega
    have hn3 : 0 < n - 2 := by omega
    have hpos : 0 < n * (n - 1) * (n - 2) := by positivity
    omega
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  have hgt : r ^ 3 < (r + 2) * (r + 1) * r := by nlinarith
  omega
