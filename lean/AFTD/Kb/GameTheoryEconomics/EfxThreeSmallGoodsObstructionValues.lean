import AFTD.Prelude

/-!
# efx_three_small_goods_obstruction_values

Topic: fair_division   Node: 90f46a653988

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

The explicit positive four-agent eleven-good natural-valued matrix from experiment 11269, with four old adjacent pairs among goods 0 through 7 and three additional goods 8,9,10. Rows are (400,400,293,293,449,450,285,285,83,115,2), (588,588,800,800,572,572,1012,1012,4,392,4), (284,284,374,374,400,400,392,392,34,2,164), and (350,351,285,285,277,277,400,400,2,83,115).
-/

open Function Finset

def efx_three_small_goods_obstruction_values : Fin 4 → Fin 11 → ℕ :=![![400,400,293,293,449,450,285,285,83,115,2],
    ![588,588,800,800,572,572,1012,1012,4,392,4],
    ![284,284,374,374,400,400,392,392,34,2,164],
    ![350,351,285,285,277,277,400,400,2,83,115]]
