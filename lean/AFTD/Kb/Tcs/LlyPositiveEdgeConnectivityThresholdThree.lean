import AFTD.Prelude
import AFTD.Kb.Tcs.LlyPositiveEdgeConnectivityThreshold
import AFTD.Kb.Tcs.GraphLlyCurvaturePosOfThree
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphEdgeConnectivity

/-!
# lly_positive_edge_connectivity_threshold_three

Topic: graphs   Node: b7e8a82730a7

Provenance: original. Related work: Partial result on OP-165 (arXiv:2610.10559, after Theorem 1.4): the threshold ⌈2n/3 − 1⌉ = 1 is not attained at n = 3.

c(3) = 0: every connected graph on 3 vertices has positive Lin–Lu–Yau curvature on every edge, whatever its edge-connectivity.
-/

theorem lly_positive_edge_connectivity_threshold_three :
    lly_positive_edge_connectivity_threshold 3 = 0 := by
  unfold lly_positive_edge_connectivity_threshold
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  intro G _ hG _ x y hxy
  have hall : ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b → ∀ w, w = a ∨ w = b ∨ w = c := by decide
  have hne : x ≠ y := G.ne_of_adj hxy
  fin_cases x <;> fin_cases y
  all_goals first
    | exact absurd rfl hne
    | exact graph_lly_curvature_pos_of_three G hG _ _ 0 hxy (by decide) (by decide)
        (hall _ _ _ (by decide) (by decide) (by decide))
    | exact graph_lly_curvature_pos_of_three G hG _ _ 1 hxy (by decide) (by decide)
        (hall _ _ _ (by decide) (by decide) (by decide))
    | exact graph_lly_curvature_pos_of_three G hG _ _ 2 hxy (by decide) (by decide)
        (hall _ _ _ (by decide) (by decide) (by decide))
