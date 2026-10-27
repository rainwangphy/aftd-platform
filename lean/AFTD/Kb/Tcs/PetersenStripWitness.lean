import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenStripVertex

/-!
# petersen_strip_witness

Topic: graphs   Node: 454b5b0c5108

Provenance: helper lemma. step towards petersen_strip_small_boundary_quadratic_extremum

Explicit finite vertex set witness achieving the quadratic bound k^2/2 + 1 with external boundary at most 2k + 1 in the generalized Petersen strip.
-/

/-- Explicit finite vertex set witness achieving the quadratic bound k^2/2 + 1 with external boundary at most 2k + 1 in the generalized Petersen strip. -/
def petersen_strip_witness (k : ℕ) : Finset PetersenStripVertex :=
  let m := k / 2
  let R := if k % 2 == 0 then m else m + 1
  let U : Finset ℤ := (Finset.range R).biUnion fun r => (Finset.range m).image fun j => ((r * k + j : ℕ) : ℤ)
  let extra : ℤ := (R : ℤ) * (k : ℤ) + (m : ℤ) - 1
  let V : Finset ℤ := insert extra U
  U.image PetersenStripVertex.u ∪ V.image PetersenStripVertex.v
