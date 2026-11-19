import AFTD.Prelude
import AFTD.Kb.Tcs.DistinctTriples
import AFTD.Kb.Tcs.ThreePointRatio

/-!
# is_permutation_robust

Topic: information   Node: 71df8bb84ec3

Provenance: formalization of a published result. Source: arXiv:2611.21275, Definition 16

A finite subset s of a field F is permutation-robust if the map assigning each ordered triple of distinct elements in s to its three-point ratio is injective.
-/

/-- A subset of a field is permutation-robust if the three-point ratio map is injective on the set of ordered triples of distinct elements. -/
def is_permutation_robust {F : Type*} [Field F] [DecidableEq F] (s : Finset F) : Prop := (distinct_triples s : Set (F × F × F)).InjOn (fun (a, b, c) => three_point_ratio a b c)
