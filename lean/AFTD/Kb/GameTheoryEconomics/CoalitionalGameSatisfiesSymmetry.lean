import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameAreSymmetric

/-!
# CoalitionalGame.SatisfiesSymmetry

Topic: general_equilibrium   Node: 6b2a0de9c10a

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.SatisfiesSymmetry`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/ShapleyValue.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A solution concept satisfies symmetry. [MSZ 18.4]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- A solution concept satisfies symmetry. [MSZ 18.4] -/
def CoalitionalGame.SatisfiesSymmetry (φ : CoalitionalGame N ℝ → N → ℝ) : Prop :=
  ∀ (G : CoalitionalGame N ℝ) (i j : N), G.AreSymmetric i j → φ G i = φ G j
