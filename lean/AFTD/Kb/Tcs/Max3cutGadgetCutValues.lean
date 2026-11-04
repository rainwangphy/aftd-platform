import AFTD.Prelude
import AFTD.Kb.Tcs.Max3cutVE
import AFTD.Kb.Tcs.Max3cutVN
import AFTD.Kb.Tcs.Max3cutS
import AFTD.Kb.Tcs.Max3cutVNEq

/-!
# max3cut_gadget_cut_values

Topic: approximation   Node: 3c5b3c4b1dfe

Provenance: formalization of a published result. Source: arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

For every primary coloring x : Fin 3 → ZMod 3, the maximum cut value of the E-gadget is max3cut_v_e x = if max3cut_s x = 0 then 18 else 16, and the maximum cut weight of the N-gadget is max3cut_v_n x = if max3cut_s x ≠ 0 then 11 else 9.
-/

/-- Cut values of the E-gadget and N-gadget for Max-3-Cut (Lemma 3.1). -/
theorem max3cut_gadget_cut_values (x : Fin 3 → ZMod 3) :
    (max3cut_v_e x = if max3cut_s x = 0 then 18 else 16) ∧
    (max3cut_v_n x = if max3cut_s x ≠ 0 then 11 else 9) := by
  constructor
  · revert x
    decide +kernel
  · exact max3cut_v_n_eq x
