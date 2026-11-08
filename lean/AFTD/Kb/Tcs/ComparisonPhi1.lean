import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonFeature1
import AFTD.Kb.Tcs.ComparisonSign
import AFTD.Kb.Tcs.ComparisonEdge

/-!
# comparison_phi1

Topic: quantum   Node: d8ecc50d4a32

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The real linear evaluation vector phi_1(x) : comparison_feature1 n → ℝ of a strict order x (a permutation of Fin n giving the ranks): its value at the constant coordinate `none` is 1 and its value at `some e` is the comparison sign d_e(x).
-/

/-- The real linear evaluation vector phi_1(x) : comparison_feature1 n → ℝ of a strict order x (a permutation of Fin n giving the ranks): its value at the constant coordinate `none` is 1 and its value at `some e` is the comparison sign d_e(x). -/
def comparison_phi1 {n : ℕ} (x : Equiv.Perm (Fin n)) : comparison_feature1 n → ℝ
  | none => 1
  | some e => comparison_sign x e
