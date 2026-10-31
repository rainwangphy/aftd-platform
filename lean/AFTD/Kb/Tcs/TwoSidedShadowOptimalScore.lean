import AFTD.Prelude

/-!
# two_sided_shadow_optimal_score

Topic: quantum   Node: 17df10724bac

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:378

The optimal score s_k for a k-qubit Clifford unitary in the two-sided locally randomized classical shadow architecture, defined as a natural number: if k % 2 = 1 then (3 * 5^k + 3^k - 6) / 4 else (3 * 5^k - 3^k + 2) / 4 using natural number arithmetic.
-/

/-- The optimal integer score s_k for a k-qubit Clifford unitary in the two-sided locally randomized classical shadow architecture. -/
def two_sided_shadow_optimal_score (k : ℕ) : ℕ := if k % 2 = 1 then (3 * 5 ^ k + 3 ^ k - 6) / 4
  else (3 * 5 ^ k - 3 ^ k + 2) / 4
