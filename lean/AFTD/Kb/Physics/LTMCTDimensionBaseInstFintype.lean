import AFTD.Prelude
import AFTD.Kb.Physics.LTMCTDimensionBase

/-!
# LTMCTDimensionBase.instFintype

Topic: classical_mechanics   Node: a2b6f568dd29

Provenance: formalization of a published result. Source: Physlib, `LTMCTDimensionBase.instFintype`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/LTMCTDimensionBase.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LTMCTDimensionBase.instFintype
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance LTMCTDimensionBase.instFintype : Fintype LTMCTDimensionBase where
  elems := {.length, .time, .mass, .charge, .temperature}
  complete := fun x => by cases x <;> decide
