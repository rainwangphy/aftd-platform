import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModToFin1dRFun
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup

/-!
# Lorentz.ContrMod.toFin1dℝAddEquiv

Topic: special_relativity   Node: f1007336badd

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.toFin1dℝAddEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The additive equivalence between `ContrMod` and `Fin 1 ⊕ Fin d → ℝ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- The additive equivalence between `ContrMod` and `Fin 1 ⊕ Fin d → ℝ`. -/
noncomputable def Lorentz.ContrMod.toFin1dℝAddEquiv : ContrMod d ≃+ (Fin 1 ⊕ Fin d → ℝ) :=
  { toFin1dℝFun with map_add' _ _ := rfl }
