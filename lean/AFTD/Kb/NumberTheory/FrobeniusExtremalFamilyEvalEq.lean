import AFTD.Prelude

/-!
# frobenius_extremal_family_eval_eq

Topic: elementary_number_theory   Node: b7a8c2fc4d19

Provenance: helper lemma. scout/2610-32219-a-sharp-upper-bound-for-the-frobenius-number.md:461

For n ≥ 3 and any natural number q, the identity q * ((n - 2) * q + 1) - q - ((n - 2) * q + 1) = ((n - 2) * q + 1) * q - (n - 1) * q - 1 holds in the natural numbers.
-/

/-- Algebraic simplification of the two-generator Frobenius formula for S_{n,q}. -/
theorem frobenius_extremal_family_eval_eq (n q : ℕ) (hn : 3 ≤ n) : q * ((n - 2) * q + 1) - q - ((n - 2) * q + 1) = ((n - 2) * q + 1) * q - (n - 1) * q - 1 := by
  rw [Nat.sub_sub, Nat.sub_sub]
  rw [mul_comm q ((n - 2) * q + 1)]
  congr 1
  have h : n - 1 = (n - 2) + 1 := by omega
  rw [h]
  ring
