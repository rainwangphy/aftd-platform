import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzContrCModuleToFin13CAddEquiv

/-!
# Lorentz.ContrℂModule.instModuleComplex

Topic: special_relativity   Node: 51d597a2acf6

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrℂModule.instModuleComplex`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `Module` on `ContrℂModule` defined via its equivalence with `Fin 1 ⊕ Fin 3 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
/-- The instance of `Module` on `ContrℂModule` defined via its equivalence with `Fin 1 ⊕ Fin 3 → ℂ`. -/
noncomputable instance Lorentz.ContrℂModule.instModuleComplex : Module ℂ ContrℂModule := AddEquiv.module ℂ toFin13ℂAddEquiv
