import AFTD.Prelude
import AFTD.Kb.Tcs.GraphConfigIsAlmostStacked

/-!
# graph_config_is_almost_stacked_single

Topic: graphs   Node: 18ebe7eef0b1

Provenance: helper lemma. arXiv:2610.09650 Def 3.1

A configuration with all pebbles on a single vertex is almost stacked.
-/

/-- A configuration with all pebbles on a single vertex is almost stacked. -/
theorem graph_config_is_almost_stacked_single {V : Type*} [DecidableEq V] (v : V) (m : ℕ) :
    graph_config_is_almost_stacked (Pi.single v m) := by
  refine ⟨v, fun w hw => ?_⟩
  rw [Pi.single_eq_of_ne hw]
  exact Nat.zero_le 1
