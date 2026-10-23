import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPoValues

/-!
# efx_po_values_pos

Topic: fair_division   Node: b2a3c6c1552c

Provenance: helper lemma. arXiv:2610.29201 Theorem 1

In the 4-agent 8-good instance efx_po_values, every agent values every good strictly positively.
-/

/-- Every good has strictly positive integer value to every agent in the counterexample instance. -/
lemma efx_po_values_pos : ∀ (i : Fin 4) (g : Fin 8), 0 < efx_po_values i g := by
  decide
