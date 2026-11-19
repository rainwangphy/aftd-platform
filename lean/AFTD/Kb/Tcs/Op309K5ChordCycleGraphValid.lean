import AFTD.Prelude
import AFTD.Kb.Tcs.Op309K5ChordCycleGraph

/-!
# op309_k5_chord_cycle_graph_valid

Topic: graphs   Node: dc2b35bb0b93

Provenance: helper lemma. Finite obstruction to extending the chord-conflict construction of https://arxiv.org/abs/2611.24297 beyond outerplanar graphs; experiments 34597 and 34600.

The ten-vertex chord-conflict example is a connected simple cubic graph.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

local instance op309_k5_chord_cycle_graph_decidable : DecidableRel op309_k5_chord_cycle_graph.Adj := fun u v =>
  inferInstanceAs (Decidable
    (((u.val, v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,9),(0,3),(1,5),(2,7),(4,8),(6,9)] : List (ℕ × ℕ))) ∨
     ((v.val, u.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,9),(0,3),(1,5),(2,7),(4,8),(6,9)] : List (ℕ × ℕ)))))

theorem op309_k5_chord_cycle_graph_valid : op309_k5_chord_cycle_graph.Connected ∧ op309_k5_chord_cycle_graph.maxDegree = 3 := by
  constructor <;> decide
