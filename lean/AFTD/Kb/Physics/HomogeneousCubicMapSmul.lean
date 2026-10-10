import AFTD.Prelude
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.HomogeneousCubicInstFun

/-!
# HomogeneousCubic.map_smul

Topic: classical_mechanics   Node: 9b17971e0440

Provenance: formalization of a published result. Source: Physlib, `HomogeneousCubic.map_smul`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HomogeneousCubic.map_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HomogeneousCubic in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma HomogeneousCubic.map_smul (f : HomogeneousCubic V) (a : ℚ) (S : V) : f (a • S) = a ^ 3 * f S :=
  f.map_smul' a S
