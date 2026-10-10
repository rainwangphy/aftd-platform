import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal

/-!
# Time.instVSubReal

Topic: classical_mechanics   Node: 9391245cc573

Provenance: formalization of a published result. Source: Physlib, `Time.instVSubReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.instVSubReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
noncomputable instance Time.instVSubReal : VSub ℝ Time where
  vsub t₁ t₂ := t₁.val - t₂.val
