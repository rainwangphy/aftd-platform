import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickGameIsSpe
import AFTD.Kb.GameTheoryEconomics.PickGameRootAllocation
import AFTD.Kb.GameTheoryEconomics.BlockSnakeSeqTwo
import AFTD.Kb.GameTheoryEconomics.IsNelPd
import AFTD.Kb.GameTheoryEconomics.IsEf1Pd
import AFTD.Kb.GameTheoryEconomics.PickingReverseCrossoutExists
import AFTD.Kb.GameTheoryEconomics.BlockSnakeReverseCrossoutNelEf1
import AFTD.Kb.GameTheoryEconomics.PickingTwoAgentSpeEqReverseCrossout
import AFTD.Kb.GameTheoryEconomics.PickingReverseCrossoutAllocation
import AFTD.Kb.GameTheoryEconomics.PickingReverseCrossoutValid

/-!
# block_snake_two_agent_spe_nel_ef1

Topic: fair_division   Node: 09e3b3f22a3c

Provenance: original. Related work: arXiv:2611.09685, Section 7, question on strategic picking and compensatory fairness (OP-1323); this statement specifies the block-snake sequence and strictly positive additive utility.

For any two agents with positive additive values that are distinct across the items for each agent, every subgame-perfect continuation profile of the two-agent block-snake picking game on 2k+1 objects has a root allocation satisfying both NEL and EF1 in pairwise dominance for the item rankings induced by those values. A continuation profile specifies an allocation of the remaining objects after every distinct-item history and, at every such history, specifies an optimal available next pick given the continuations after all alternatives.
-/

theorem block_snake_two_agent_spe_nel_ef1 (k : ℕ) (u : Fin 2 → Fin (2*k+1) → ℝ)
    (hu : ∀ i x, 0 < u i x)
    (hd : ∀ i x y, x ≠ y → u i x ≠ u i y)
    (F : List (Fin (2*k+1)) → Finset (Fin (2*k+1)))
    (hF : pick_game_is_spe u (block_snake_seq_two k) F) :
    is_nel_pd (fun i x y => u i x ≤ u i y) (pick_game_root_allocation F) ∧
    is_ef1_pd (fun i x y => u i x ≤ u i y) (pick_game_root_allocation F) := by
  have hlen : (block_snake_seq_two k).length = 2*k+1 := by
    simp [block_snake_seq_two]
  obtain ⟨π, hπ⟩ := picking_reverse_crossout_exists (2*k+1) u (block_snake_seq_two k) hlen
  have heq := picking_two_agent_spe_eq_reverse_crossout (2*k+1) u (block_snake_seq_two k) π F hu hd hπ hF
  have hmain := block_snake_reverse_crossout_nel_ef1 k u π hπ
  rw [← heq]
  exact hmain
