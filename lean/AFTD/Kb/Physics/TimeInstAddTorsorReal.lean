import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal

/-!
# Time.instAddTorsorReal

Topic: classical_mechanics   Node: 0b3c9e227c29

Provenance: formalization of a published result. Source: Physlib, `Time.instAddTorsorReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.instAddTorsorReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
noncomputable instance Time.instAddTorsorReal : AddTorsor ℝ Time where
  zero_vadd t := by ext; simp
  add_vadd dt₁ dt₂ t := by ext; simp [add_assoc]
  vsub_vadd' t₁ t₂ := by ext; simp
  vadd_vsub' dt t := by simp
