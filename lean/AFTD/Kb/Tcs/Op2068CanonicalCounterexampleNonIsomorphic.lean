import AFTD.Prelude
import AFTD.Kb.Tcs.CanonicalTIntersectingFamily
import AFTD.Kb.Tcs.IsTIntersectingFamily
import AFTD.Kb.Tcs.ArePermIsomorphicFamilies

/-!
# op_2068_canonical_counterexample_non_isomorphic

Topic: combinatorics   Node: 83be1985c44b

Provenance: formalization of a published result. Source: arXiv:2611.25346 Sec. 3

For parameters (n,k,t)=(5,3,2), both canonical families canonical_t_intersecting_family 5 3 2 0 and canonical_t_intersecting_family 5 3 2 1 have cardinality 4, both satisfy is_t_intersecting_family 2, and they are not isomorphic under are_perm_isomorphic_families 5.
-/

/-- For parameters (n,k,t)=(5,3,2), both canonical families S_0 and S_1 have size 4 and are 2-intersecting, but are not isomorphic. -/
theorem op_2068_canonical_counterexample_non_isomorphic :
    (canonical_t_intersecting_family 5 3 2 0).card = 4 ∧
    (canonical_t_intersecting_family 5 3 2 1).card = 4 ∧
    is_t_intersecting_family 2 (canonical_t_intersecting_family 5 3 2 0) ∧
    is_t_intersecting_family 2 (canonical_t_intersecting_family 5 3 2 1) ∧
    ¬ are_perm_isomorphic_families 5
      (canonical_t_intersecting_family 5 3 2 0)
      (canonical_t_intersecting_family 5 3 2 1) := ⟨by decide, by decide, by
      unfold is_t_intersecting_family
      decide, by
      unfold is_t_intersecting_family
      decide, by
      unfold are_perm_isomorphic_families
      decide⟩
