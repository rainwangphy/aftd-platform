import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoMod
import AFTD.Kb.Physics.LorentzCoModInstAddCommGroup
import AFTD.Kb.Physics.LorentzCoModToFin1dRFun

/-!
# Lorentz.CoMod.toFin1dℝAddEquiv

Topic: special_relativity   Node: c46eb20f88c5

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoMod.toFin1dℝAddEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The additive equivalence between `CoℝModule` and `Fin 1 ⊕ Fin d → ℝ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.CoMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- The additive equivalence between `CoℝModule` and `Fin 1 ⊕ Fin d → ℝ`. -/
noncomputable def Lorentz.CoMod.toFin1dℝAddEquiv : CoMod d ≃+ (Fin 1 ⊕ Fin d → ℝ) :=
  { toFin1dℝFun with map_add' _ _ := rfl }
