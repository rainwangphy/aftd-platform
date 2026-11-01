import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitValues
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitValue
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitBaseline
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitSanity

/-!
# efx_no_self_three_split_no_self_champion

Topic: fair_division   Node: 05b1a8b8039d

Provenance: helper lemma. Positive equal-triple no-self-champion obstruction to the OP-7 two-bundle exchange route, experiments 11462–11471.

No owner self-champions even under inclusion-minimality: every subset of her old triple plus charity that she prefers is strongly envied by some agent.
-/

theorem efx_no_self_three_split_no_self_champion (i : Fin 4) (T : Finset (Fin 13))
  (hT : T ⊆ insert 12 (efx_no_self_three_split_old i))
  (hprefer : efx_no_self_three_split_baseline i < efx_no_self_three_split_value i T) :
  ∃ (j : Fin 4) (g : Fin 13), g ∈ T ∧
    efx_no_self_three_split_baseline j < efx_no_self_three_split_value j (T.erase g) := by
  revert i T
  decide
