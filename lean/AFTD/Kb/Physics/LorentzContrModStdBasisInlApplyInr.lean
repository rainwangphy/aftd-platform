import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrModInstModuleReal
import AFTD.Kb.Physics.LorentzContrModStdBasis
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplyNe
import AFTD.Kb.Physics.LorentzContrModValAdd
import AFTD.Kb.Physics.LorentzContrModValSmul
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplySame
import AFTD.Kb.Physics.LorentzContrModStdBasisApplySame

/-!
# Lorentz.ContrMod.stdBasis_inl_apply_inr

Topic: special_relativity   Node: a1045e5bcfdf

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.stdBasis_inl_apply_inr`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrMod.stdBasis_inl_apply_inr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
@[simp]
lemma Lorentz.ContrMod.stdBasis_inl_apply_inr (i : Fin d) : (stdBasis (Sum.inl 0)).val (Sum.inr i) = 0 := by
  refine stdBasis_toFin1dℝEquiv_apply_ne ?_
  simp
