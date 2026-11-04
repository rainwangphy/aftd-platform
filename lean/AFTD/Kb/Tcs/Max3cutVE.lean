import AFTD.Prelude
import AFTD.Kb.Tcs.Max3cutECut

/-!
# max3cut_v_e

Topic: approximation   Node: c736ec46d0ab

Provenance: formalization of a published result. Source: arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

The maximum cut value V_E(x) in the E-gadget for primary coloring x : Fin 3 → ZMod 3, defined as the supremum of max3cut_e_cut x a over all auxiliary 3-colorings a : Fin 6 → ZMod 3.
-/

/-- The maximum cut value V_E(x) of the E-gadget. -/
def max3cut_v_e (x : Fin 3 → ZMod 3) : ℕ := Finset.univ.sup (fun a => max3cut_e_cut x a)
