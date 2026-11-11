import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForced

/-!
# univ_is_zero_forcing_set

Topic: graphs   Node: 103582ce06f8

Provenance: helper lemma. arXiv:2611.11352 Section 1

The full set of vertices of any graph G is a zero forcing set.
-/

/-- Sanity lemma: the universal set is always a zero forcing set. -/
theorem univ_is_zero_forcing_set {V : Type*} (G : SimpleGraph V) :
    is_zero_forcing_set G Set.univ := by
  intro v
  exact ZeroForced.init v (Set.mem_univ v)
