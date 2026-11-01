import AFTD.Prelude

/-!
# efx_three_small_goods_obstruction_partial_coarse

Topic: fair_division   Node: e7ca0388506d

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

Assign the first eight old goods in four intact adjacent pairs to agents q(0),...,q(3), and the two retained bonuses to q(4),q(5). Mergers are permitted.
-/

open Function Finset

def efx_three_small_goods_obstruction_partial_coarse (q : Fin 6 → Fin 4) : Fin 10 → Fin 4 :=![q 0,q 0,q 1,q 1,q 2,q 2,q 3,q 3,q 4,q 5]
