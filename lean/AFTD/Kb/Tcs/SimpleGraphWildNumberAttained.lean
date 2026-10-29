import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeCardEdgeFinset
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphIsColorConnectingEdgeSet
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting

/-!
# simple_graph_wild_number_attained

Topic: graphs   Node: 8e6427305323

Provenance: helper lemma. Structural necessity and certificate-soundness helpers for the OP-306 campaign; arXiv:2610.22142, Sections 3.3.1 and 3.3.2. These make the optimal block-partition route an equivalence at every odd order; no new exact wild-number case or bound is asserted.

For any finite connected edge-colored graph, some finite color-connecting edge set has cardinality exactly its wild number.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem simple_graph_wild_number_attained {V α : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (γ : G.edgeSet → α) (hG : G.Connected) :
    ∃ W : Finset (Sym2 V), W.card = simple_graph_wild_number G γ ∧
      simple_graph_is_color_connecting G γ ↑W := by
  classical
  have he : simple_graph_is_color_connecting G γ (↑G.edgeFinset : Set (Sym2 V)) := by
    rw [SimpleGraph.coe_edgeFinset]
    exact simple_graph_is_color_connecting_edge_set G γ hG
  exact Nat.sInf_mem (show {j | ∃ W : Finset (Sym2 V), W.card = j ∧ simple_graph_is_color_connecting G γ ↑W}.Nonempty from
    ⟨G.edgeFinset.card,G.edgeFinset,rfl,he⟩)
