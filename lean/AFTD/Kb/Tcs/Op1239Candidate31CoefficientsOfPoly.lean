import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate31
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel
import AFTD.Kb.Tcs.PetrialNullityPolyCoeffEqPetrialCoeff
import AFTD.Kb.Tcs.PetrialCoeff
import AFTD.Kb.Tcs.PetrialNullityPoly

/-!
# op_1239_candidate31_coefficients_of_poly

Topic: combinatorics   Node: bc49a8135055

Provenance: helper lemma. Coefficient extraction for OP-1239.

If the nullity polynomial of op_1239_candidate31 is the displayed degree-seven polynomial, then its partial Petrial coefficients in ranks 24, 25 and 26 are 64, 8416 and 1274976.
-/

local instance  aftdLocal_eac057252a426a40_0 : DecidableRel op_1239_candidate31.Adj := by
  unfold op_1239_candidate31
  infer_instance

theorem op_1239_candidate31_coefficients_of_poly (hp : petrial_nullity_poly op_1239_candidate31 = (560820429 : Polynomial ℕ) + 876263103 * Polynomial.X ^ 1 + 530790732 * Polynomial.X ^ 2 + 156016800 * Polynomial.X ^ 3 + 22309128 * Polynomial.X ^ 4 + 1274976 * Polynomial.X ^ 5 + 8416 * Polynomial.X ^ 6 + 64 * Polynomial.X ^ 7) :
    petrial_coeff op_1239_candidate31 24 = 64 ∧
    petrial_coeff op_1239_candidate31 25 = 8416 ∧
    petrial_coeff op_1239_candidate31 26 = 1274976 := by
  have h24 : (petrial_nullity_poly op_1239_candidate31).coeff 7 = petrial_coeff op_1239_candidate31 24 := by
    simpa using (petrial_nullity_poly_coeff_eq_petrial_coeff op_1239_candidate31 (k := 24) (by decide))
  have h25 : (petrial_nullity_poly op_1239_candidate31).coeff 6 = petrial_coeff op_1239_candidate31 25 := by
    simpa using (petrial_nullity_poly_coeff_eq_petrial_coeff op_1239_candidate31 (k := 25) (by decide))
  have h26 : (petrial_nullity_poly op_1239_candidate31).coeff 5 = petrial_coeff op_1239_candidate31 26 := by
    simpa using (petrial_nullity_poly_coeff_eq_petrial_coeff op_1239_candidate31 (k := 26) (by decide))
  rw [← h24, ← h25, ← h26, hp]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_natCast_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X]
