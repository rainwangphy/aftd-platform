import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeExpectedPayoffWithFuel
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree

/-!
# StochasticGameTree.expectedPayoff

Topic: equilibria   Node: bbad91c05d23

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.expectedPayoff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected payoff with enough fuel for every branch of the finite tree.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open StochasticGameTree in
variable {N : Type*} in
/-- Expected payoff with enough fuel for every branch of the finite tree. -/
noncomputable def StochasticGameTree.expectedPayoff (σ : Strategy N) (g : StochasticGameTree N) (i : N) :
    ℚ :=
  expectedPayoffWithFuel (sizeOf g) σ g i
