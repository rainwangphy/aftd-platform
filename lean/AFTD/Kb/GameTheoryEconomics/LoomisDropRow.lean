import AFTD.Prelude

/-!
# Loomis.dropRow

Topic: equilibria   Node: 49ab42eff089

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.dropRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Drop the `i₀`-row of `A` and view as a matrix on `{i // i ≠ i₀} × J`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Drop the `i₀`-row of `A` and view as a matrix on `{i // i ≠ i₀} × J`. -/
noncomputable def Loomis.dropRow [DecidableEq I] (A : I → J → ℝ) (i₀ : I) :
    {i : I // i ≠ i₀} → J → ℝ :=
  fun i' j => A i'.val j
