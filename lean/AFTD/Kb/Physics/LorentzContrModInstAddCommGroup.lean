import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModToFin1dRFun

/-!
# Lorentz.ContrMod.instAddCommGroup

Topic: special_relativity   Node: 296f065bf216

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.instAddCommGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `AddCommGroup` on `ContrMod` defined via its equivalence with `Fin 1 ⊕ Fin d → ℝ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- The instance of `AddCommGroup` on `ContrMod` defined via its equivalence with `Fin 1 ⊕ Fin d → ℝ`. -/
noncomputable instance Lorentz.ContrMod.instAddCommGroup : AddCommGroup (ContrMod d) := Equiv.addCommGroup toFin1dℝFun
