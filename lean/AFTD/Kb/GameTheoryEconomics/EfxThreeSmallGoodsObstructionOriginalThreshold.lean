import AFTD.Prelude

/-!
# efx_three_small_goods_obstruction_original_threshold

Topic: fair_division   Node: 3498e3dce05d

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

The four original old-only utilities (800,1600,800,800), attained by assigning the first eight goods in adjacent pairs to the four agents in order.
-/

open Function Finset

def efx_three_small_goods_obstruction_original_threshold : Fin 4 → ℕ :=![800,1600,800,800]
