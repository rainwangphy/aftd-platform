import AFTD.Prelude
import AFTD.Kb.NumberTheory.FrobeniusExtremalFamily
import AFTD.Kb.NumberTheory.FrobeniusExtremalFamilyCoprime
import AFTD.Kb.NumberTheory.FrobeniusExtremalFamilyClosureEq
import AFTD.Kb.NumberTheory.FrobeniusExtremalFamilyEvalEq

/-!
# frobenius_extremal_family_frobenius_number

Topic: elementary_number_theory   Node: bd461dd1c5e9

Provenance: formalization of a published result. Source: scout/2610-32219-a-sharp-upper-bound-for-the-frobenius-number.md:450

For any integers n ≥ 3 and q ≥ 2, the Frobenius number of the extremal family `frobenius_extremal_family n q` is equal to ((n - 2) * q + 1) * q - (n - 1) * q - 1.
-/

/-- Sharpness of the Frobenius upper bound: the Frobenius number of S_{n,q} is ((n - 2) * q + 1) * q - (n - 1) * q - 1. -/
theorem frobenius_extremal_family_frobenius_number (n q : ℕ) (hn : 3 ≤ n) (hq : 2 ≤ q) : FrobeniusNumber (((n - 2) * q + 1) * q - (n - 1) * q - 1) (frobenius_extremal_family n q) := by
  have h_closure : AddSubmonoid.closure (frobenius_extremal_family n q) = AddSubmonoid.closure {q, (n - 2) * q + 1} :=
    frobenius_extremal_family_closure_eq n q (by omega)
  have h_eval : q * ((n - 2) * q + 1) - q - ((n - 2) * q + 1) = ((n - 2) * q + 1) * q - (n - 1) * q - 1 :=
    frobenius_extremal_family_eval_eq n q hn
  rw [FrobeniusNumber]
  rw [h_closure]
  rw [← h_eval]
  change FrobeniusNumber (q * ((n - 2) * q + 1) - q - ((n - 2) * q + 1)) {q, (n - 2) * q + 1}
  apply frobeniusNumber_pair
  · exact frobenius_extremal_family_coprime n q
  · exact hq
  · have h1 : 1 ≤ n - 2 := by omega
    have h2 : 1 * q ≤ (n - 2) * q := Nat.mul_le_mul_right q h1
    omega
