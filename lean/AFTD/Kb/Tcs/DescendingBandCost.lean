import AFTD.Prelude
import AFTD.Kb.Tcs.DescendingBandSet

/-!
# descending_band_cost

Topic: information   Node: fae311bf2a21

Provenance: original. Related work: knowledgebase, OP-1702

For integers $d \in \mathbb{Z}$ and $r, L \in \mathbb{N}$, the descending band cost `descending_band_cost d r L` is the infimum over all integer shifts $t \in \mathbb{Z}$ of the average absolute distance from elements of the descending band set $A = A_{d,r,L}$ to $t$, namely $\frac{1}{|A|} \sum_{a \in A} |a - t|$.
-/

/-- Optimal integer shift centering cost C_{r,L} of descending band set A_{r,L} -/
noncomputable def descending_band_cost (d : ℤ) (r L : ℕ) : ℝ := let A := descending_band_set d r L; ⨅ t : ℤ, (1 / (A.card : ℝ)) * ∑ a ∈ A, |(a : ℝ) - (t : ℝ)|
