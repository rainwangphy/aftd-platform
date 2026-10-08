import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree

/-!
# StochasticGameTree.ChanceProbabilitiesSumToOne

Topic: equilibria   Node: e260a179caad

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.ChanceProbabilitiesSumToOne`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Local probability mass check at a chance node.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- Local probability mass check at a chance node. -/
def StochasticGameTree.ChanceProbabilitiesSumToOne (headProb : ℚ) (tail : List (ℚ × StochasticGameTree N)) :
    Prop :=
  headProb + (tail.map Prod.fst).sum = 1
