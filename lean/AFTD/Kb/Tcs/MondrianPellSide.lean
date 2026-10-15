import AFTD.Prelude

/-!
# mondrian_pell_side

Topic: combinatorics   Node: 1cc09f2e0ef4

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Theorem 1.1.

The side lengths n₀ = 315, n₁ = 106785, n_{j+2} = 340 n_{j+1} − n_j.
-/

/-- Side lengths `n₀ = 315`, `n₁ = 106785`, `n_{j+2} = 340 n_{j+1} - n_j`. -/
def mondrian_pell_side : ℕ → ℕ
  | 0 => 315
  | 1 => 106785
  | (j + 2) => 340 * mondrian_pell_side (j + 1) - mondrian_pell_side j
