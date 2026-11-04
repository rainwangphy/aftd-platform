import AFTD.Prelude

/-!
# hyperbinaryLengthPoly

Topic: elementary_number_theory   Node: af18cacb8378

Provenance: formalization of a published result. Source: scout/2611-01243-halving-partitions-and-hyperbinary-expansions.md:353

The hyperbinary length polynomial H_m(z) satisfies H_0(z) = 1, H_{2m+1}(z) = z H_m(z), and H_{2m}(z) = H_m(z) + z^2 H_{m-1}(z) for m ≥ 1.
-/

/-- The hyperbinary length polynomial H_m(z). -/
noncomputable def hyperbinaryLengthPoly : ℕ → Polynomial ℤ
| 0 => 1
| n + 1 =>
  if h : (n + 1) % 2 = 1 then
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
    Polynomial.X * hyperbinaryLengthPoly ((n + 1) / 2)
  else
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
    have : (n + 1) / 2 - 1 < n + 1 := by omega
    hyperbinaryLengthPoly ((n + 1) / 2) + Polynomial.X ^ 2 * hyperbinaryLengthPoly ((n + 1) / 2 - 1)
termination_by n => n
