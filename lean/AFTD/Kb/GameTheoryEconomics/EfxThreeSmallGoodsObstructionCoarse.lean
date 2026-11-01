import AFTD.Prelude

/-!
# efx_three_small_goods_obstruction_coarse

Topic: fair_division   Node: bb5a2a223f32

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

An allocation of the eleven goods obtained by assigning each of the four old adjacent pairs intact to arbitrary agents p(0),...,p(3), and each of goods 8,9,10 to p(4),p(5),p(6). Mergers of old bundles are permitted.
-/

open Function Finset

def efx_three_small_goods_obstruction_coarse (p : Fin 7 → Fin 4) : Fin 11 → Fin 4 :=![p 0,p 0,p 1,p 1,p 2,p 2,p 3,p 3,p 4,p 5,p 6]
