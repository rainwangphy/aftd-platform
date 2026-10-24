import AFTD.Prelude

/-!
# cycle_rook_poly

Topic: combinatorics   Node: a0021a72206d

Provenance: formalization of a published result. Source: arXiv:2610.23958 Proposition 5.1

The rook polynomial Q_m(x) of an m-cycle, defined for m >= 1 as the sum over k from 0 to floor(m/2) of (m / (m - k)) * choose(m - k, k) * x^k in ℚ[x].
-/

/-- The rook polynomial Q_m(X) of an m-cycle. -/
noncomputable def cycle_rook_poly (m : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (m / 2 + 1),
    Polynomial.C (((m : ℚ) / ((m : ℚ) - (k : ℚ))) * (Nat.choose (m - k) k : ℚ)) * Polynomial.X ^ k
