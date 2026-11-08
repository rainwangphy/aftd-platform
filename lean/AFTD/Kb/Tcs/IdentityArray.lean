import AFTD.Prelude
import AFTD.Kb.Tcs.Arr

/-!
# identity_array

Topic: combinatorics   Node: 3e62045ff268

Provenance: formalization of a published result. Source: arXiv:2611.05397, Section 2.2, Definition 1: Ranking and Unranking Permutations in Heap's Order

The identity array of order $m$ is the identity function on $\mathrm{Fin}\,m$.
-/

/-- The identity array of order m. -/
def identity_array (m : ℕ) : Arr m := id
