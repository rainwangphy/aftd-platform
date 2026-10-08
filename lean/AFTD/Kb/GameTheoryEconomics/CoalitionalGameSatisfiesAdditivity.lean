import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.SatisfiesAdditivity

Topic: general_equilibrium   Node: 1deaf6abe99a

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.SatisfiesAdditivity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/ShapleyValue.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A solution concept satisfies additivity. [MSZ 18.8]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- A solution concept satisfies additivity. [MSZ 18.8] -/
def CoalitionalGame.SatisfiesAdditivity (φ : CoalitionalGame N ℝ → N → ℝ) : Prop :=
  ∀ (G H : CoalitionalGame N ℝ) (i : N),
    φ ⟨fun S => G.v S + H.v S, by simp [G.empty_zero, H.empty_zero]⟩ i = φ G i + φ H i
