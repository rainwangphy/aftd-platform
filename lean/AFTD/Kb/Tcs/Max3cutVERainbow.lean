import AFTD.Prelude
import AFTD.Kb.Tcs.Max3cutVE

/-!
# max3cut_v_e_rainbow

Topic: approximation   Node: d87ee9e0ff9f

Provenance: helper lemma. arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

The maximum cut value of the E-gadget on the rainbow primary coloring ![0, 1, 2] is 18.
-/

/-- V_E on the rainbow primary coloring (0,1,2) is 18. -/
theorem max3cut_v_e_rainbow : max3cut_v_e ![0, 1, 2] = 18 := by
  set_option maxRecDepth 50000 in
  rfl
