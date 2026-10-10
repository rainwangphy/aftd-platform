import AFTD.Prelude
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun

/-!
# HomogeneousQuadratic.map_smul

Topic: classical_mechanics   Node: e4f0f54d1bba

Provenance: formalization of a published result. Source: Physlib, `HomogeneousQuadratic.map_smul`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HomogeneousQuadratic.map_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HomogeneousQuadratic in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma HomogeneousQuadratic.map_smul (f : HomogeneousQuadratic V) (a : ℚ) (S : V) : f (a • S) = a ^ 2 * f S :=
  f.map_smul' a S
