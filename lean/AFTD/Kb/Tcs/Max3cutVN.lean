import AFTD.Prelude
import AFTD.Kb.Tcs.Max3cutNCut

/-!
# max3cut_v_n

Topic: approximation   Node: f9ecea874531

Provenance: formalization of a published result. Source: arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

The maximum cut weight V_N(x) in the N-gadget for primary coloring x : Fin 3 → ZMod 3, maximized over all 3 colorings q : ZMod 3 of the auxiliary vertex.
-/

/-- The maximum cut weight V_N(x) of the N-gadget. -/
def max3cut_v_n (x : Fin 3 → ZMod 3) : ℕ := Finset.univ.sup (fun q => max3cut_n_cut x q)
