import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered

/-!
# simple_graph_has_well_covered_powers

Topic: graphs   Node: c635f7d03256

Provenance: formalization of a published result. Source: arXiv:2611.03956 Def 2.2

A finite simple graph G has the well-covered powers property if for every integer d ≥ 1, the d-th graph power G^d is well-covered.
-/

/-- A finite simple graph has the well-covered powers property if every positive power G^d is well-covered. -/
def simple_graph_has_well_covered_powers {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop := ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d)
