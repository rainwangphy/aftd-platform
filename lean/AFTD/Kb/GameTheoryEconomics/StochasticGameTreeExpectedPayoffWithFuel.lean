import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree

/-!
# StochasticGameTree.expectedPayoffWithFuel

Topic: equilibria   Node: 2e287568afb3

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.expectedPayoffWithFuel`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fuel-bounded expected payoff under a pure strategy. If fuel runs out, the default payoff is zero; `expectedPayoff` below supplies tree-size fuel.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open StochasticGameTree in
variable {N : Type*} in
/-- Fuel-bounded expected payoff under a pure strategy. If fuel runs out, the default payoff is zero; `expectedPayoff` below supplies tree-size fuel. -/
noncomputable def StochasticGameTree.expectedPayoffWithFuel (fuel : ℕ) (σ : Strategy N)
    (g : StochasticGameTree N) (i : N) : ℚ :=
  match fuel with
  | 0 => 0
  | n + 1 =>
      match g with
      | Leaf p => p i
      | Player m h t => expectedPayoffWithFuel n σ (σ m h t).val i
      | Chance p h t =>
          p * expectedPayoffWithFuel n σ h i +
            (t.map (fun child => child.1 * expectedPayoffWithFuel n σ child.2 i)).sum
