import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoMod
import AFTD.Kb.Physics.LorentzCoModInstAddCommGroup
import AFTD.Kb.Physics.LorentzCoModInstModuleReal
import AFTD.Kb.Physics.LorentzCoModToFin1dREquiv
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplySame

/-!
# Lorentz.CoMod.toFin1dℝ

Topic: special_relativity   Node: 8c47e304ba98

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoMod.toFin1dℝ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying element of `Fin 1 ⊕ Fin d → ℝ` of a element in `CoℝModule` defined through the linear equivalence `toFin1dℝEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.CoMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- The underlying element of `Fin 1 ⊕ Fin d → ℝ` of a element in `CoℝModule` defined through the linear equivalence `toFin1dℝEquiv`. -/
noncomputable abbrev Lorentz.CoMod.toFin1dℝ (ψ : CoMod d) := toFin1dℝEquiv ψ
