import AFTD.Prelude

/-!
# good_slopes_product_fiber_set

Topic: elementary_number_theory   Node: 8f05e1eaa33a

Provenance: helper lemma. CRT fiber construction for the modulus 105 reduction in OP-1027.

The set of projected point pairs over Z obtained by fixing the Y-coordinate of y + a x.
-/

noncomputable def good_slopes_product_fiber_set {X Y Z : Type*} [Fintype X] [DecidableEq X] [CommRing Y] [DecidableEq Y] [CommRing Z] [DecidableEq Z] (xY yY : X → Y) (xZ yZ : X → Z) (a : Y) (t : Y) : Finset (Z × Z) := by
  classical
  exact (Finset.univ.filter fun x : X => yY x + a*xY x = t).image (fun x => (xZ x, yZ x))
