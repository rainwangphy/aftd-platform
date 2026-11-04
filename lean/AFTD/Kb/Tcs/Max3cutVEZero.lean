import AFTD.Prelude
import AFTD.Kb.Tcs.Max3cutVE

/-!
# max3cut_v_e_zero

Topic: approximation   Node: 832689e4a48d

Provenance: helper lemma. arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

The maximum cut value of the E-gadget on the constant zero primary coloring fun _ => 0 is 18.
-/

/-- V_E on the monochromatic primary coloring (0,0,0) is 18. -/
theorem max3cut_v_e_zero : max3cut_v_e (fun _ => 0) = 18 := by decide +kernel
