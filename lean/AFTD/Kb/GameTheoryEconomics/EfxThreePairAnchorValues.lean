import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairValues

/-!
# efx_three_pair_anchor_values

Topic: fair_division   Node: e89a6727a14f

Provenance: helper lemma. Common-anchor lift of the OP-7 all-source three-split barrier; experiment 11720 and an unproved anchor-count projection.

Keep the original nine goods and add 4r common anchors worth 100 each.
-/

def efx_three_pair_anchor_values (r : ℕ) (i : Fin 4) (g : Fin (9 + 4*r)) : ℕ := if h : g.val < 9 then efx_allsource_three_pair_values i ⟨g.val, h⟩ else 100
