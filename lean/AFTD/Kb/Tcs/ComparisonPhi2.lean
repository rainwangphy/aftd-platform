import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonFeature2
import AFTD.Kb.Tcs.ComparisonPhi1
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.Tcs.ComparisonSign

/-!
# comparison_phi2

Topic: quantum   Node: fd05571e8f09

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The real quadratic evaluation vector phi_2(x) : comparison_feature2 n → ℝ of a strict order x (a permutation of Fin n giving the ranks): at `Sum.inl i` it is phi_1(x) i (so 1 at the constant coordinate and d_e(x) at a linear one), and at the quadratic coordinate of a two-element edge set {e, f} it is the product d_e(x) * d_f(x).
-/

/-- The real quadratic evaluation vector phi_2(x) : comparison_feature2 n → ℝ of a strict order x (a permutation of Fin n giving the ranks): at `Sum.inl i` it is phi_1(x) i (so 1 at the constant coordinate and d_e(x) at a linear one), and at the quadratic coordinate of a two-element edge set {e, f} it is the product d_e(x) * d_f(x). -/
def comparison_phi2 {n : ℕ} (x : Equiv.Perm (Fin n)) : comparison_feature2 n → ℝ
  | Sum.inl i => comparison_phi1 x i
  | Sum.inr s => ∏ e ∈ s.1, comparison_sign x e
