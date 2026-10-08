import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugRow

/-!
# EconCSLib.LinearAlgebra.farkasAugA

Topic: lp_duality   Node: 966fd5902345

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.farkasAugA`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/Farkas.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Augmented matrix `A_aug : FarkasAugRow I → Fin (n+1) → 𝕜`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Augmented matrix `A_aug : FarkasAugRow I → Fin (n+1) → 𝕜`. -/
def EconCSLib.LinearAlgebra.farkasAugA (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (d : 𝕜) :
    FarkasAugRow I → Fin (n+1) → 𝕜
  | Sum.inl i, j => Fin.lastCases (-b i) (fun j' => A i j') j
  | Sum.inr false, j => Fin.lastCases 1 (fun _ => (0 : 𝕜)) j
  | Sum.inr true, j => Fin.lastCases d (fun j' => -c j') j
