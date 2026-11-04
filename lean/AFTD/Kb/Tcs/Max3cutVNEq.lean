import AFTD.Prelude
import AFTD.Kb.Tcs.Max3cutVN
import AFTD.Kb.Tcs.Max3cutS

/-!
# max3cut_v_n_eq

Topic: approximation   Node: 01986ba78f7c

Provenance: helper lemma. arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

For every primary coloring x : Fin 3 → ZMod 3, the maximum cut weight of the N-gadget is V_N(x) = 11 if s(x) ≠ 0 and 9 otherwise.
-/

/-- Cut value of the N-gadget for all primary colorings. -/
theorem max3cut_v_n_eq (x : Fin 3 → ZMod 3) :
    max3cut_v_n x = if max3cut_s x ≠ 0 then 11 else 9 := by
  revert x
  decide
