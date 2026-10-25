import AFTD.Prelude
import AFTD.Kb.Tcs.HasStrongOrientationOfDiameterLe
import AFTD.Kb.Tcs.DigraphReachWithin
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# cycle_graph_eight_strong_orientation_diameter_le_seven

Topic: graphs   Node: 32be7f6e231c

Provenance: helper lemma. sanity lemma for has_strong_orientation_of_diameter_le (OP-119)

Sanity (non-vacuity): the 8-cycle, a bridgeless graph of diameter 4, has a strong orientation of directed diameter at most 7, namely the cyclic orientation.
-/

def cycle_graph_eight_strong_orientation_diameter_le_seven_digraph : Digraph (Fin 8) where
  Adj u v := v - u = 1

instance cycle_graph_eight_strong_orientation_diameter_le_seven_adj_decidable :
    DecidableRel cycle_graph_eight_strong_orientation_diameter_le_seven_digraph.Adj := by
  intro u v
  dsimp [cycle_graph_eight_strong_orientation_diameter_le_seven_digraph]
  infer_instance

instance cycle_graph_eight_strong_orientation_diameter_le_seven_reach_decidable
    (k : ℕ) (u v : Fin 8) :
    Decidable (digraph_reach_within cycle_graph_eight_strong_orientation_diameter_le_seven_digraph k u v) := by
  induction k generalizing u v with
  | zero =>
    change Decidable (u = v)
    infer_instance
  | succ k ih =>
    change Decidable (digraph_reach_within cycle_graph_eight_strong_orientation_diameter_le_seven_digraph k u v ∨
      ∃ w, cycle_graph_eight_strong_orientation_diameter_le_seven_digraph.Adj u w ∧
        digraph_reach_within cycle_graph_eight_strong_orientation_diameter_le_seven_digraph k w v)
    have : ∀ w, Decidable (cycle_graph_eight_strong_orientation_diameter_le_seven_digraph.Adj u w ∧
      digraph_reach_within cycle_graph_eight_strong_orientation_diameter_le_seven_digraph k w v) := fun w => by
      have : Decidable (cycle_graph_eight_strong_orientation_diameter_le_seven_digraph.Adj u w) := inferInstance
      have : Decidable (digraph_reach_within cycle_graph_eight_strong_orientation_diameter_le_seven_digraph k w v) := ih w v
      infer_instance
    infer_instance

theorem cycle_graph_eight_strong_orientation_diameter_le_seven :
    has_strong_orientation_of_diameter_le (SimpleGraph.cycleGraph 8) 7 := by
  use cycle_graph_eight_strong_orientation_diameter_le_seven_digraph
  refine ⟨by dsimp [is_graph_orientation]; decide, by decide⟩
