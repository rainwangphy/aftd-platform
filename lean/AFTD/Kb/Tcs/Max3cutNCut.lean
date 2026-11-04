import AFTD.Prelude

/-!
# max3cut_n_cut

Topic: approximation   Node: 139e19ae9f7b

Provenance: formalization of a published result. Source: arXiv:2611.01402 Lemma 3.1 -- Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k

The cut weight in the N-gadget with primary coloring x : Fin 3 → ZMod 3 and auxiliary coloring q : ZMod 3, consisting of a unit-weight triangle on the three primaries and edges of weight 3 from q to each primary vertex.
-/

/-- The cut weight in the N-gadget for colorings x and q. -/
def max3cut_n_cut (x : Fin 3 → ZMod 3) (q : ZMod 3) : ℕ :=
  (if x 0 ≠ x 1 then 1 else 0) +
  (if x 1 ≠ x 2 then 1 else 0) +
  (if x 2 ≠ x 0 then 1 else 0) +
  3 * (Finset.univ.filter fun p : Fin 3 => x p ≠ q).card
