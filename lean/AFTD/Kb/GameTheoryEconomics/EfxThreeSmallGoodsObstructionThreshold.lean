import AFTD.Prelude

/-!
# efx_three_small_goods_obstruction_threshold

Topic: fair_division   Node: e2e1ed0b45b8

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

The four current utility thresholds (883,1992,800,800), attained by the starting EFX allocation of the first ten goods in the explicit three-small-goods instance.
-/

open Function Finset

def efx_three_small_goods_obstruction_threshold : Fin 4 → ℕ :=![883,1992,800,800]
