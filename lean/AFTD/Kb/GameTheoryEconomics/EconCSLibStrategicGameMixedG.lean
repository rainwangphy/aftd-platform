import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.mixed_g

Topic: equilibria   Node: aa58df8edd4e

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.mixed_g`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Multilinear payoff functional on raw weight vectors `m : ∀ i, G.strategy i → ℝ`. Same as `evaluate_at_mixed` but with arbitrary (not necessarily probability-normalized) weights; used inside continuity arguments.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Function in
set_option linter.unusedSectionVars false in
variable {N : Type*} in
variable (G : EconCSLib.StrategicGame N ℝ) in
variable [Fintype N] [DecidableEq N] in
variable [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)] in
variable [∀ i, Inhabited (G.strategy i)] in
/-- Multilinear payoff functional on raw weight vectors `m : ∀ i, G.strategy i → ℝ`. Same as `evaluate_at_mixed` but with arbitrary (not necessarily probability-normalized) weights; used inside continuity arguments. -/
noncomputable def EconCSLib.StrategicGame.mixed_g (i : N) (m : ∀ i, G.strategy i → ℝ) : ℝ :=
  ∑ s : G.Profile, (∏ j : N, m j (s j)) * G.payoff s i
