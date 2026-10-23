import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPoValues

/-!
# efx_po_bv_nat

Topic: fair_division   Node: 9211287e787b

Provenance: helper lemma. step towards efx_pareto_incompatible_pos_additive

Agent i's value for agent j's bundle in the 4-agent 8-good instance, as a natural number: the sum over the eight goods of i's value for the good if j owns it, and 0 otherwise.
-/

/-- Agent i's value for agent j's bundle, as a natural number (the eight-term `if` sum over `efx_po_values`). -/
def efx_po_bv_nat (σ : Fin 8 → Fin 4) (i j : Fin 4) : ℕ :=
  (if σ 0 = j then efx_po_values i 0 else 0) + (if σ 1 = j then efx_po_values i 1 else 0)
  + (if σ 2 = j then efx_po_values i 2 else 0) + (if σ 3 = j then efx_po_values i 3 else 0)
  + (if σ 4 = j then efx_po_values i 4 else 0) + (if σ 5 = j then efx_po_values i 5 else 0)
  + (if σ 6 = j then efx_po_values i 6 else 0) + (if σ 7 = j then efx_po_values i 7 else 0)
