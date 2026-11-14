import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# descending_band_set

Topic: information   Node: 709590ba824d

Provenance: original. Related work: knowledgebase, OP-1702

For an integer d and positive integers r ≤ L, the descending band set A_{r,L} is the union over j from 0 to r-1 of the integer intervals [jd, jd + L - j - 1].
-/

/-- The descending band set A_{r,L} = ⋃_{j=0}^{r-1} {jd, ..., jd + L - j - 1} -/
def descending_band_set (d : ℤ) (r L : ℕ) : Finset ℤ := (Finset.range r).biUnion fun j => Finset.Ico (j * d) (j * d + (L - j : ℤ))
