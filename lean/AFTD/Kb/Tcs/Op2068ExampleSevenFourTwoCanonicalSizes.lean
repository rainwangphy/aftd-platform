import AFTD.Prelude
import AFTD.Kb.Tcs.CanonicalTIntersectingFamily
import AFTD.Kb.Tcs.IsTIntersectingFamily

/-!
# op_2068_example_seven_four_two_canonical_sizes

Topic: combinatorics   Node: 249ef2a49edf

Provenance: formalization of a published result. Source: arXiv:2611.25346 Example 1.5

For parameters (n,k,t)=(7,4,2), the canonical families canonical_t_intersecting_family 7 4 2 0, canonical_t_intersecting_family 7 4 2 1, and canonical_t_intersecting_family 7 4 2 2 have cardinalities 16, 17, and 15 respectively, and canonical_t_intersecting_family 7 4 2 1 satisfies is_t_intersecting_family 2.
-/

/-- For parameters (n,k,t)=(7,4,2), the canonical families S_0, S_1, and S_2 have sizes 16, 17, and 15 respectively. -/
theorem op_2068_example_seven_four_two_canonical_sizes :
    (canonical_t_intersecting_family 7 4 2 0).card = 16 ∧
    (canonical_t_intersecting_family 7 4 2 1).card = 17 ∧
    (canonical_t_intersecting_family 7 4 2 2).card = 15 ∧
    is_t_intersecting_family 2 (canonical_t_intersecting_family 7 4 2 1) := by
  unfold is_t_intersecting_family
  decide
