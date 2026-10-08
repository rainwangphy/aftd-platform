import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive

/-!
# Loomis.IsPositive.one

Topic: equilibria   Node: 5d9765ba56a2

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.IsPositive.one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The all-ones matrix is positive; the simplified-Loomis specialisation plugs `B := fun _ _ => 1` into the general theorem.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- The all-ones matrix is positive; the simplified-Loomis specialisation plugs `B := fun _ _ => 1` into the general theorem. -/
theorem Loomis.IsPositive.one : IsPositive (fun (_ : I) (_ : J) => (1 : ℝ)) := fun _ _ => one_pos
