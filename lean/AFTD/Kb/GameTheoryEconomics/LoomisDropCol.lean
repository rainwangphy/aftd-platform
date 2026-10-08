import AFTD.Prelude

/-!
# Loomis.dropCol

Topic: equilibria   Node: 9983ae27ad45

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.dropCol`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Drop the `j₀`-column of `A` and view as a matrix on `I × {j // j ≠ j₀}`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Drop the `j₀`-column of `A` and view as a matrix on `I × {j // j ≠ j₀}`. -/
noncomputable def Loomis.dropCol [DecidableEq J] (A : I → J → ℝ) (j₀ : J) :
    I → {j : J // j ≠ j₀} → ℝ :=
  fun i j' => A i j'.val
