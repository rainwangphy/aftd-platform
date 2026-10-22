import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPoValues

/-!
# efx_po_val_real

Topic: fair_division   Node: 0fa3487e77e8

Provenance: formalization of a published result. Source: arXiv:2610.29201 Theorem 1

The real-valued valuations for the 4-agent, 8-good instance, obtained by casting the integer valuations efx_po_values to real numbers.
-/

/-- The real-valued valuations of the 4-agent, 8-good counterexample instance. -/
def efx_po_val_real : Fin 4 → Fin 8 → ℝ :=
  fun i g => (efx_po_values i g : ℝ)
