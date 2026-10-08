import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeChanceProbabilitiesSumToOne
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree

/-!
# StochasticGameTree.fairCoin_probs_sum_to_one

Topic: equilibria   Node: 2c68226ea7d4

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.fairCoin_probs_sum_to_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StochasticGameTree.fairCoin_probs_sum_to_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
theorem StochasticGameTree.fairCoin_probs_sum_to_one :
    ChanceProbabilitiesSumToOne (1 / 2)
      (List.cons
        (1 / 2, StochasticGameTree.Leaf (fun i : Fin 2 => if i = 0 then 0 else 1))
        List.nil) := by
  norm_num [ChanceProbabilitiesSumToOne]
