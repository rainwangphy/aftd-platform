import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModToFin1dR
import AFTD.Kb.Physics.LorentzContrModValAdd
import AFTD.Kb.Physics.LorentzContrModValSmul

/-!
# Lorentz.ContrMod.toFin1dℝ_eq_val

Topic: special_relativity   Node: 9042df8365df

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.toFin1dℝ_eq_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrMod.toFin1dℝ_eq_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
lemma Lorentz.ContrMod.toFin1dℝ_eq_val (ψ : ContrMod d) : ψ.toFin1dℝ = ψ.val := by rfl
