import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugRow

/-!
# EconCSLib.LinearAlgebra.farkasAugB

Topic: lp_duality   Node: 59963f2a8821

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.farkasAugB`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/Farkas.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Augmented RHS `b_aug : FarkasAugRow I → 𝕜`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Augmented RHS `b_aug : FarkasAugRow I → 𝕜`. -/
def EconCSLib.LinearAlgebra.farkasAugB (b : I → 𝕜) : FarkasAugRow I → 𝕜
  | Sum.inl _ => 0
  | Sum.inr false => 0
  | Sum.inr true => 1
