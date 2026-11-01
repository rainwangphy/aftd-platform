import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairValues

/-!
# efx_allsource_three_pair_no_self

Topic: fair_division   Node: 802d80a0ef29

Provenance: helper lemma. Four-agent envy-free one-charity three-split barrier for OP-7; SMT experiment 11699 and independent enumeration 11701. Both are evidence, not Lean proofs.

The original envy-free state has no self champion for the charity good.
-/

theorem efx_allsource_three_pair_no_self (i : Fin 4) (T : Finset (Fin 9))
  (hT : T ⊆ insert 8 ({![0,2,4,6] i, ![1,3,5,7] i} : Finset (Fin 9)))
  (hprefer : 10 < ∑ g ∈ T, efx_allsource_three_pair_values i g) :
  ∃ (j : Fin 4) (g : Fin 9), g ∈ T ∧ 10 <
    ∑ h ∈ T.erase g, efx_allsource_three_pair_values j h := by
  revert i T
  decide +kernel
