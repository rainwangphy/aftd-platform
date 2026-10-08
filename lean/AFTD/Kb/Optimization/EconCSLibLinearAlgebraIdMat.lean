import AFTD.Prelude

/-!
# EconCSLib.LinearAlgebra.idMat

Topic: lp_duality   Node: b363ce86f31b

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.idMat`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/PerronFrobenius.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The identity matrix on `Fin n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {n : ℕ} [NeZero n] in
/-- The identity matrix on `Fin n`. -/
def EconCSLib.LinearAlgebra.idMat : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0
