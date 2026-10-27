import AFTD.Prelude

/-!
# frobenius_extremal_family_coprime

Topic: elementary_number_theory   Node: 7abd79d55389

Provenance: helper lemma. scout/2610-32219-a-sharp-upper-bound-for-the-frobenius-number.md:456

For any natural numbers n and q, the numbers q and (n - 2) * q + 1 are coprime.
-/

/-- The generators q and (n - 2) * q + 1 are coprime. -/
theorem frobenius_extremal_family_coprime (n q : ℕ) : Nat.Coprime q ((n - 2) * q + 1) := by
  simpa [Nat.add_comm] using
    (Nat.coprime_add_mul_right_right q 1 (n - 2)).mpr (Nat.coprime_one_right q)
