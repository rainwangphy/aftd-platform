import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAnchorFamilyValues

/-!
# efx_anchor_family_perturbed_values

Topic: fair_division   Node: b3552e423eec

Provenance: helper lemma. Nondegenerate arbitrary-size OP-7 Pareto obstruction, binary perturbation and experiment 11514.

Multiply all anchor-family valuations by 2 to the number of goods and add the agent-specific binary perturbation.
-/

def efx_anchor_family_perturbed_values (r s : ℕ)
  (p : Fin 4 → Fin ((7+(r+r+r))+s) → ℕ) : Fin 4 → Fin ((7+(r+r+r))+s) → ℕ := fun i g => 2 ^ ((7+(r+r+r))+s) * efx_anchor_family_values r s i g + 2 ^ p i g
