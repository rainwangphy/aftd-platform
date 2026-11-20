import AFTD.Prelude

/-!
# op874_producer_predecessor_demand_forces_fourth_edge

Topic: graphs   Node: 8e1a25ee9fd6

Provenance: helper lemma. Palette analysis of the OP-874 single-defect graph-transfer plan, tested by experiments 35401 and 35404.

For four colors, the displayed two-vertex palette and interface constraints force the fourth successive factor-edge color d to equal f, the color absent from the preceding three edges. In the producer-cycle construction these constraints are necessary to obtain the proposed off-palette predecessor demand.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem op874_producer_predecessor_demand_forces_fourth_edge
    (a b c d f up un hn hm : Fin 4)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hcd : c ≠ d)
    (hf : f ≠ a ∧ f ≠ b ∧ f ≠ c)
    (hq : up ≠ un ∧ up ≠ b ∧ up ≠ c ∧ un ≠ b ∧ un ≠ c)
    (hnext : hn ≠ hm ∧ hn ≠ c ∧ hn ≠ d ∧ hm ≠ c ∧ hm ≠ d)
    (hin : f ≠ un) (hout : up ≠ hn ∧ up ≠ hm) : d = f := by
  fin_cases a <;> fin_cases b <;> simp_all <;>
    fin_cases c <;> simp_all <;> fin_cases f <;> simp_all <;>
    fin_cases up <;> simp_all <;> fin_cases un <;> simp_all <;>
    fin_cases d <;> simp_all <;> fin_cases hn <;> simp_all <;>
    fin_cases hm <;> simp_all
