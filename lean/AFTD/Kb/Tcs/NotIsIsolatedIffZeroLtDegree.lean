import AFTD.Prelude

/-!
# not_isIsolated_iff_zero_lt_degree

Topic: graphs   Node: f534c9695347

Provenance: helper lemma. step towards weighted_dominating_occupancy_at_one_le_two_thirds

A vertex in a simple graph is not isolated if and only if its degree is strictly positive.
-/

open Classical in
/-- A vertex in a simple graph is not isolated if and only if its degree is strictly positive. -/
theorem not_isIsolated_iff_zero_lt_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (w : V) :
    ¬ G.IsIsolated w ↔ 0 < G.degree w := by
  simp [SimpleGraph.degree_pos]
