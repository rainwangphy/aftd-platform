import AFTD.Prelude
import AFTD.Kb.Tcs.Op874ProducerPredecessorDemandForcesFourthEdge

/-!
# op874_triangle_predecessor_off_palette_impossible

Topic: graphs   Node: 536516496c2d

Provenance: helper lemma. Explicit triangle obstruction to an OP-874 graph-transfer plan, experiments 35401 and 35414.

The displayed triangle palette and interface constraints cannot simultaneously provide the proposed off-palette predecessor demand. It is the triangle specialization of the necessary four-edge-window condition.
-/

theorem op874_triangle_predecessor_off_palette_impossible
    (a b c f up un hn hm : Fin 4)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hf : f ≠ a ∧ f ≠ b ∧ f ≠ c)
    (hq : up ≠ un ∧ up ≠ b ∧ up ≠ c ∧ un ≠ b ∧ un ≠ c)
    (hnext : hn ≠ hm ∧ hn ≠ c ∧ hn ≠ a ∧ hm ≠ c ∧ hm ≠ a)
    (hin : f ≠ un) (hout : up ≠ hn ∧ up ≠ hm) : False := by
  have h := op874_producer_predecessor_demand_forces_fourth_edge a b c a f up un hn hm
    habc habc.2.1.symm hf hq hnext hin hout
  exact hf.1 h.symm
