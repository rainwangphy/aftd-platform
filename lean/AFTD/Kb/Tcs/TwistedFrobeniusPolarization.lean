import AFTD.Prelude
import AFTD.Kb.Tcs.TwistedFrobeniusMap

/-!
# twisted_frobenius_polarization

Topic: combinatorics   Node: adc6299fb511

Provenance: formalization of a published result. Source: scout/2611-17378-a-19-5-lower-bound-for-the-four-dimensional-erd-h-o-s-box-p.md:128

The polarization $P(x,y) = Q(x+y) + Q(x) + Q(y)$ of the twisted Frobenius map.
-/

/-- The bilinear polarization P(x,y) = Q(x+y) + Q(x) + Q(y) of the twisted Frobenius map. -/
def twisted_frobenius_polarization (q : ℕ) {K : Type*} [Field K] (x y : K) : K := twisted_frobenius_map q (x + y) + twisted_frobenius_map q x + twisted_frobenius_map q y
