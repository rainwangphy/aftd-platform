import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGamePayoffVector
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsEfficient
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameCoalitionPayoff

/-!
# CoalitionalGame.Core

Topic: general_equilibrium   Node: e26116845164

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.Core`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Core.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The core of a coalitional game: payoff vectors where no coalition can improve upon its allocation. [MSZ 17.2] An element `x` of the core satisfies: - Efficiency: `∑ᵢ xᵢ = v(N)` - Coalition stability: `∑_{i ∈ S} xᵢ ≥ v(S)` for all `S`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- The core of a coalitional game: payoff vectors where no coalition can improve upon its allocation. [MSZ 17.2] An element `x` of the core satisfies: - Efficiency: `∑ᵢ xᵢ = v(N)` - Coalition stability: `∑_{i ∈ S} xᵢ ≥ v(S)` for all `S` -/
def CoalitionalGame.Core : Set (PayoffVector N ℝ) :=
  { x | G.IsEfficient x ∧ ∀ S : Finset N, coalitionPayoff x S ≥ G.v S }
