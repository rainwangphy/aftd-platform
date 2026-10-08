import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameEvaluateAtMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedG
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.evaluate_at_mixed_eq_mixed_g

Topic: equilibria   Node: 8ae46caf1ed4

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.evaluate_at_mixed_eq_mixed_g`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`evaluate_at_mixed` is the restriction of `mixed_g` to simplex weights.
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
/-- `evaluate_at_mixed` is the restriction of `mixed_g` to simplex weights. -/
theorem EconCSLib.StrategicGame.evaluate_at_mixed_eq_mixed_g (i : N) (σ : MixedS G) :
    evaluate_at_mixed G i σ = mixed_g G i (fun j => (σ j).val) := by
  simp [evaluate_at_mixed, mixed_g]
