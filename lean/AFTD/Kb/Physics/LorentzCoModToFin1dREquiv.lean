import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoMod
import AFTD.Kb.Physics.LorentzCoModInstAddCommGroup
import AFTD.Kb.Physics.LorentzCoModInstModuleReal
import AFTD.Kb.Physics.LorentzCoModToFin1dRAddEquiv

/-!
# Lorentz.CoMod.toFin1dℝEquiv

Topic: special_relativity   Node: f84f91f72056

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoMod.toFin1dℝEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The linear equivalence between `CoℝModule` and `(Fin 1 ⊕ Fin d → ℝ)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.CoMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- The linear equivalence between `CoℝModule` and `(Fin 1 ⊕ Fin d → ℝ)`. -/
noncomputable def Lorentz.CoMod.toFin1dℝEquiv : CoMod d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) :=
  AddEquiv.linearEquiv ℝ toFin1dℝAddEquiv
