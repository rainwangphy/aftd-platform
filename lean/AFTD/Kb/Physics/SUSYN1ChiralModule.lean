import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1ChiralColor
import AFTD.Kb.Physics.SUSYN1ChiralColorTau
import AFTD.Kb.Physics.ConjModule
import AFTD.Kb.Physics.BasisConjReprApply
import AFTD.Kb.Physics.SUSYN1ChiralColorBarBar
import AFTD.Kb.Physics.SUSYN1ChiralColorBarTau
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup
import AFTD.Kb.Physics.ConjModuleInstModule

/-!
# SUSY.N1.chiralModule

Topic: quantum_field_theory   Node: dd9b8fc15e21

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.chiralModule`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The carrier module of each colour, distinct for all four: the holomorphic vectors `ι → ℂ` and their dual `Module.Dual ℂ (ι → ℂ)` on the chiral side, and the conjugate module `ConjModule …` of each (where `i` acts as `−i`) on the anti side. Variance is the vector/dual axis, holomorphy the conjugate-module axis; both are genuine carrier data, not labels tracked separately.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
/-- The carrier module of each colour, distinct for all four: the holomorphic vectors `ι → ℂ` and their dual `Module.Dual ℂ (ι → ℂ)` on the chiral side, and the conjugate module `ConjModule …` of each (where `i` acts as `−i`) on the anti side. Variance is the vector/dual axis, holomorphy the conjugate-module axis; both are genuine carrier data, not labels tracked separately. -/
noncomputable abbrev SUSY.N1.chiralModule : ChiralColor → Type
  | .chiralUp   => ι → ℂ
  | .chiralDown => Module.Dual ℂ (ι → ℂ)
  | .antiUp     => ConjModule (ι → ℂ)
  | .antiDown   => ConjModule (Module.Dual ℂ (ι → ℂ))
