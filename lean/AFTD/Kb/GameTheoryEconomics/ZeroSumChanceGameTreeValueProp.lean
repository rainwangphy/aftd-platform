import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceSelect
import AFTD.Kb.GameTheoryEconomics.ZeroSumChancePlayer
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceInstInhabitedGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeValue
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeDStrategy

/-!
# ZeroSumChance.GameTree.value_prop

Topic: equilibria   Node: 2c2cbf543398

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.GameTree.value_prop`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Soundness of `DStrategy`**: the backward-induction value is a lower bound on the outcome A achieves by following `DStrategy`, regardless of how B plays. Formally: for every B-strategy `SB` and game tree `t`, `t.value ≤ t.outcome DStrategy SB`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- **Soundness of `DStrategy`**: the backward-induction value is a lower bound on the outcome A achieves by following `DStrategy`, regardless of how B plays. Formally: for every B-strategy `SB` and game tree `t`, `t.value ≤ t.outcome DStrategy SB`. -/
theorem ZeroSumChance.GameTree.value_prop (SB : Strategy) {t : GameTree} : t.value ≤ t.outcome DStrategy SB := by
  induction t with
  | Leaf r =>
    simp [outcome, value]
  | Pnode p L R HL HR =>
    match p with
    | Player.A =>
      rw [value, outcome, DStrategy]
      split_ifs with h
      · -- DStrategy picked R (L.value < R.value); goal: max L.value R.value ≤ outcome … R
        exact (max_le (le_of_lt h |>.trans HR) HR)
      · -- DStrategy picked L (¬ L.value < R.value, i.e. R.value ≤ L.value)
        -- goal: max L.value R.value ≤ outcome … L
        exact (max_le HL (not_lt.mp h |>.trans HL))
    | Player.B =>
      rw [value, outcome]
      cases SB L R
      · -- B chose L
        exact min_le_left L.value R.value |>.trans HL
      · -- B chose R
        exact min_le_right L.value R.value |>.trans HR
  | Nnode prob L R HL HR =>
    rw [outcome, value]
    have hpL : (prob : ℚ) * L.value ≤ prob * outcome DStrategy SB L :=
      mul_le_mul_of_nonneg_left HL prob.2.1
    have hpR : (1 - prob) * R.value ≤ (1 - prob) * outcome DStrategy SB R :=
      mul_le_mul_of_nonneg_left HR (by linarith [prob.2.2])
    linarith
