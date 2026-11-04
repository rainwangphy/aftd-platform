import AFTD.Prelude

/-!
# max3cut_e_cut

Topic: approximation   Node: 91c9b0755951

Provenance: formalization of a published result. Source: arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

The cut weight in the 18-edge E-gadget for primary coloring x : Fin 3 → ZMod 3 and auxiliary coloring a : Fin 6 → ZMod 3, defined as the sum of the number of pairs (p, v) in the list [(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 4), (2, 5)] with x p ≠ a v, and the number of pairs (u, v) in the list [(0, 5), (0, 3), (1, 2), (1, 4), (2, 5), (3, 4)] with a u ≠ a v.
-/

/-- The cut weight in the 18-edge E-gadget for colorings x and a. -/
def max3cut_e_cut (x : Fin 3 → ZMod 3) (a : Fin 6 → ZMod 3) : ℕ :=
  (([(0, 0), (0, 1), (0, 2), (0, 3),
     (1, 2), (1, 3), (1, 4), (1, 5),
     (2, 0), (2, 1), (2, 4), (2, 5)] : List (Fin 3 × Fin 6)).filter fun (p, v) => x p ≠ a v).length +
  (([(0, 5), (0, 3), (1, 2), (1, 4), (2, 5), (3, 4)] : List (Fin 6 × Fin 6)).filter fun (u, v) => a u ≠ a v).length
