import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRealListColorable

/-!
# simple_graph_real_list_chromatic_number

Topic: combinatorics   Node: e235948a3586

Provenance: formalization of a published result. Source: arXiv:2611.18384 Section 2.2

The list chromatic number of a simple graph H with respect to real lists is the least integer k such that H is k-list-colorable from real lists.
-/

/-- The list chromatic number of a simple graph with respect to real lists. -/
noncomputable def simple_graph_real_list_chromatic_number {V : Type*} (H : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | simple_graph_is_real_list_colorable H k}
