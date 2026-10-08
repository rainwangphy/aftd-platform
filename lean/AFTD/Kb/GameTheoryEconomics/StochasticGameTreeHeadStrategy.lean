import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode

/-!
# StochasticGameTree.headStrategy

Topic: equilibria   Node: 48eef87264a9

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.headStrategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The trivial head-selecting strategy, useful for examples that have no strategically relevant player choice.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open StochasticGameTree in
variable {N : Type*} in
/-- The trivial head-selecting strategy, useful for examples that have no strategically relevant player choice. -/
def StochasticGameTree.headStrategy : Strategy N :=
  fun _ h _ => ⟨h, List.mem_cons_self⟩
