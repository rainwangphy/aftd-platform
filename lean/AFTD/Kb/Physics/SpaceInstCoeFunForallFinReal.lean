import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceValEqIff

/-!
# Space.instCoeFunForallFinReal

Topic: classical_mechanics   Node: 9fd8f39507b3

Provenance: formalization of a published result. Source: Physlib, `Space.instCoeFunForallFinReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instCoeFunForallFinReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Space.instCoeFunForallFinReal {d} : CoeFun (Space d) (fun _ => Fin d → ℝ) where
  coe p := p.val
