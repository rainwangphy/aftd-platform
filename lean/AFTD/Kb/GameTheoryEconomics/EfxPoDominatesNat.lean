import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPoBvNat

/-!
# efx_po_dominates_nat

Topic: fair_division   Node: a46952001f02

Provenance: helper lemma. step towards efx_pareto_incompatible_pos_additive

Pareto domination in the 4-agent 8-good instance, stated over natural numbers: every agent weakly prefers τ, and some agent strictly prefers τ.
-/

abbrev efx_po_dominates_nat (τ σ : Fin 8 → Fin 4) : Prop :=
  (∀ i : Fin 4, efx_po_bv_nat σ i i ≤ efx_po_bv_nat τ i i) ∧
    ∃ i : Fin 4, efx_po_bv_nat σ i i < efx_po_bv_nat τ i i
