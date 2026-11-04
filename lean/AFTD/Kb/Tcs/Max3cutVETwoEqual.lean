import AFTD.Prelude
import AFTD.Kb.Tcs.Max3cutVE
import AFTD.Kb.Tcs.Max3cutGadgetCutValues
import AFTD.Kb.Tcs.Max3cutS
import AFTD.Kb.Tcs.Max3cutVN

/-!
# max3cut_v_e_two_equal

Topic: approximation   Node: 4cca209714a6

Provenance: helper lemma. arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

The maximum cut value of the E-gadget on the primary coloring ![0, 0, 1] is 16.
-/

/-- V_E on the primary coloring (0,0,1) is 16. -/
theorem max3cut_v_e_two_equal : max3cut_v_e ![0, 0, 1] = 16 := by
  rw [(max3cut_gadget_cut_values ![0, 0, 1]).1]
  decide
