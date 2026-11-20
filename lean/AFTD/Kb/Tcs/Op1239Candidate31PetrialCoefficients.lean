import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate31
import AFTD.Kb.Tcs.PetrialCoeff
import AFTD.Kb.Tcs.PetrialNullityPolyCoeffEqPetrialCoeff
import AFTD.Kb.Tcs.PetrialNullityPolyLeafRec
import AFTD.Kb.Tcs.PetrialNullityPolyMulOfCut
import AFTD.Kb.Tcs.Op1239Candidate31NullityPolyConditional
import AFTD.Kb.Tcs.PetrialNullityPolyEmptyFinset
import AFTD.Kb.Tcs.PetrialNullityPolyCardOneFinset
import AFTD.Kb.Tcs.PetrialNullityPolyDisjointFinsetUnion
import AFTD.Kb.Tcs.PetrialNullityPolyLeafFinset
import AFTD.Kb.Tcs.PetrialNullityPolyIso
import AFTD.Kb.Tcs.Op1239Candidate31CoefficientsOfPoly
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel
import AFTD.Kb.Tcs.Op1239Candidate31Tree
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.G

/-!
# op_1239_candidate31_petrial_coefficients

Topic: combinatorics   Node: 7a189c33a46b

Provenance: helper lemma. OP-1239, arXiv:2611.07503, Problem 16; candidate from experiments 28663 and 28669.

The partial Petrial coefficients of op_1239_candidate31 in ranks 24, 25 and 26 are respectively 64, 8416 and 1274976.
-/

lemma op_1239_candidate31_petrial_coefficients_mem_vs71 :
    ∀ x : Fin 31, x ∈ Op1239Cert31.vs71 := by
  decide

def op_1239_candidate31_petrial_coefficients_iso_cert :
    (SimpleGraph.induce (Op1239Cert31.vs71 : Set (Fin 31)) op_1239_candidate31) ≃g op_1239_candidate31 where
  toFun := Subtype.val
  invFun x := ⟨x, op_1239_candidate31_petrial_coefficients_mem_vs71 x⟩
  left_inv x := Subtype.ext rfl
  right_inv x := rfl
  map_rel_iff' := by intros; rfl

lemma op_1239_candidate31_petrial_coefficients_poly_eq_candidate :
    petrial_nullity_poly (SimpleGraph.induce (Op1239Cert31.vs71 : Set (Fin 31)) op_1239_candidate31) =
    petrial_nullity_poly op_1239_candidate31 :=
  petrial_nullity_poly_iso _ _ op_1239_candidate31_petrial_coefficients_iso_cert

lemma op_1239_candidate31_petrial_coefficients_poly :
    petrial_nullity_poly op_1239_candidate31 =
      560820429 + 876263103 * Polynomial.X ^ 1 + 530790732 * Polynomial.X ^ 2 + 156016800 * Polynomial.X ^ 3 +
              22309128 * Polynomial.X ^ 4 +
            1274976 * Polynomial.X ^ 5 +
          8416 * Polynomial.X ^ 6 +
        64 * Polynomial.X ^ 7 := by
  rw [← op_1239_candidate31_petrial_coefficients_poly_eq_candidate]
  exact op_1239_candidate31_nullity_poly_conditional
    (petrial_nullity_poly_empty_finset op_1239_candidate31)
    (petrial_nullity_poly_card_one_finset op_1239_candidate31)
    (petrial_nullity_poly_disjoint_finset_union op_1239_candidate31)
    (fun s v u hv hu => petrial_nullity_poly_leaf_finset op_1239_candidate31 s v u hv hu)

lemma op_1239_candidate31_petrial_coefficients_congr {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (d1 d2 : DecidableRel G.Adj) (k : ℕ) :
    @petrial_coeff V _ _ G d1 k = @petrial_coeff V _ _ G d2 k := by
  cases Subsingleton.elim d1 d2
  rfl

theorem op_1239_candidate31_petrial_coefficients : letI : DecidableRel op_1239_candidate31.Adj := Classical.decRel _; petrial_coeff op_1239_candidate31 24 = 64 ∧ petrial_coeff op_1239_candidate31 25 = 8416 ∧ petrial_coeff op_1239_candidate31 26 = 1274976 := by
  have h24 := op_1239_candidate31_petrial_coefficients_congr op_1239_candidate31 (Classical.decRel _) inferInstance 24
  have h25 := op_1239_candidate31_petrial_coefficients_congr op_1239_candidate31 (Classical.decRel _) inferInstance 25
  have h26 := op_1239_candidate31_petrial_coefficients_congr op_1239_candidate31 (Classical.decRel _) inferInstance 26
  rw [h24, h25, h26]
  exact op_1239_candidate31_coefficients_of_poly op_1239_candidate31_petrial_coefficients_poly
