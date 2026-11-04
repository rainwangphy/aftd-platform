import AFTD.Prelude

/-!
# max3cut_s

Topic: approximation   Node: 456b70628166

Provenance: formalization of a published result. Source: arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

The sum s(x) = x 0 + x 1 + x 2 in ZMod 3 of the colors of the three primary vertices for a color tuple x : Fin 3 → ZMod 3.
-/

/-- The sum s(x) = x_0 + x_1 + x_2 mod 3 for a primary coloring x. -/
def max3cut_s (x : Fin 3 → ZMod 3) : ZMod 3 := x 0 + x 1 + x 2
