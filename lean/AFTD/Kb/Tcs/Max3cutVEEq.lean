import AFTD.Prelude
import AFTD.Kb.Tcs.Max3cutVE
import AFTD.Kb.Tcs.Max3cutS
import AFTD.Kb.Tcs.Max3cutVEZero
import AFTD.Kb.Tcs.Max3cutVERainbow
import AFTD.Kb.Tcs.Max3cutVETwoEqual
import AFTD.Kb.Tcs.Max3cutVN
import AFTD.Kb.Tcs.Max3cutGadgetCutValues

/-!
# max3cut_v_e_eq

Topic: approximation   Node: 14c7cdd0e405

Provenance: helper lemma. arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

For every primary coloring x : Fin 3 → ZMod 3, the maximum cut value of the E-gadget is max3cut_v_e x = if max3cut_s x = 0 then 18 else 16.
-/

/-- Cut value of the E-gadget for all primary colorings. -/
theorem max3cut_v_e_eq (x : Fin 3 → ZMod 3) :
    max3cut_v_e x = if max3cut_s x = 0 then 18 else 16 := by
  exact (max3cut_gadget_cut_values x).1
