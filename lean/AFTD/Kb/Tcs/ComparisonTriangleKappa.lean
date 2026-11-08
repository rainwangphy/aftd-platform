import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonFeature2
import AFTD.Kb.Tcs.ComparisonTriangle
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# comparison_triangle_kappa

Topic: quantum   Node: 7ffd793723a9

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The real triangle relation vector kappa_abc : comparison_feature2 n → ℝ of a triangle a < b < c: kappa_abc = e_(ab,ac) - e_(ab,bc) + e_(ac,bc) - e_0, i.e. it is 1 at the quadratic coordinate of the edge set {ab, ac}, -1 at that of {ab, bc}, 1 at that of {ac, bc}, -1 at the constant coordinate, and 0 elsewhere.
-/

/-- The real triangle relation vector kappa_abc : comparison_feature2 n → ℝ of a triangle a < b < c: kappa_abc = e_(ab,ac) - e_(ab,bc) + e_(ac,bc) - e_0, i.e. it is 1 at the quadratic coordinate of the edge set {ab, ac}, -1 at that of {ab, bc}, 1 at that of {ac, bc}, -1 at the constant coordinate, and 0 elsewhere. -/
def comparison_triangle_kappa {n : ℕ} (t : comparison_triangle n) : comparison_feature2 n → ℝ :=
  let ab : comparison_edge n := ⟨(t.1.1, t.1.2.1), t.2.1⟩
  let ac : comparison_edge n := ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
  let bc : comparison_edge n := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
  have hab_ac : ab ≠ ac := fun h => (ne_of_lt t.2.2) (congrArg (fun p : comparison_edge n => p.1.2) h)
  have hab_bc : ab ≠ bc := fun h => (ne_of_lt t.2.1) (congrArg (fun p : comparison_edge n => p.1.1) h)
  have hac_bc : ac ≠ bc := fun h => (ne_of_lt t.2.1) (congrArg (fun p : comparison_edge n => p.1.1) h)
  let iabac : comparison_feature2 n := Sum.inr ⟨{ab, ac}, Finset.card_pair hab_ac⟩
  let iabbc : comparison_feature2 n := Sum.inr ⟨{ab, bc}, Finset.card_pair hab_bc⟩
  let iacbc : comparison_feature2 n := Sum.inr ⟨{ac, bc}, Finset.card_pair hac_bc⟩
  let i0 : comparison_feature2 n := Sum.inl none
  fun i => ((if i = iabac then 1 else 0) - (if i = iabbc then 1 else 0)
    + (if i = iacbc then 1 else 0) - (if i = i0 then 1 else 0) : ℝ)
