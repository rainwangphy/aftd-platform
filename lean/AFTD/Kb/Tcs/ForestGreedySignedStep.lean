import AFTD.Prelude

/-!
# forest_greedy_signed_step

Topic: online_algorithms   Node: 78debfb50f01

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

The new discrepancy of the first endpoint of a greedy edge is x+1 when x<y, x-1 when x>y, and uses the fair coin to choose between these values on a tie.
-/

def forest_greedy_signed_step (x y : ℤ) (coin : Bool) : ℤ := if x < y then x + 1 else if y < x then x - 1 else if coin then x + 1 else x - 1
