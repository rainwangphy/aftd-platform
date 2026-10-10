import AFTD.Prelude

/-!
# ClassicalMechanics.WaveVector

Topic: classical_mechanics   Node: 2828012e2f93

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.WaveVector`. Lean proof by Zhi Kai Pong, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/WaveEquation/HarmonicWave.lean (Copyright (c) 2025 Zhi Kai Pong. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The wavevector which indicates a direction and has magnitude `2π/λ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The wavevector which indicates a direction and has magnitude `2π/λ`. -/
abbrev ClassicalMechanics.WaveVector (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)
