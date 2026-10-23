import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPoBvNat
import AFTD.Kb.GameTheoryEconomics.EfxPoValues

/-!
# efx_po_efx_nat

Topic: fair_division   Node: c0e0d65ee467

Provenance: helper lemma. step towards efx_pareto_incompatible_pos_additive

EFX in the 4-agent 8-good instance, stated over natural numbers: for all distinct agents i and j and every good g owned by j, i's natural-number value for j's bundle is at most her value for her own bundle plus her value for g.
-/

abbrev efx_po_efx_nat (σ : Fin 8 → Fin 4) : Prop :=
  ∀ i j : Fin 4, i ≠ j → ∀ g : Fin 8, σ g = j →
    efx_po_bv_nat σ i j ≤ efx_po_bv_nat σ i i + efx_po_values i g
