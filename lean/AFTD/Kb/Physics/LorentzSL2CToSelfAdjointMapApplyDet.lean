import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CToSelfAdjointMap

/-!
# Lorentz.SL2C.toSelfAdjointMap_apply_det

Topic: special_relativity   Node: b53d88d9665c

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.toSelfAdjointMap_apply_det`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.SL2C.toSelfAdjointMap_apply_det
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
lemma Lorentz.SL2C.toSelfAdjointMap_apply_det (M : SL(2, ℂ)) (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    det ((toSelfAdjointMap M) A).1 = det A.1 := by
  simp [toSelfAdjointMap]
