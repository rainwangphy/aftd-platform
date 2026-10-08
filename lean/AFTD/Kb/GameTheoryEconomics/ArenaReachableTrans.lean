import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaReachable

/-!
# Arena.Reachable.trans

Topic: equilibria   Node: 09fdf231d26e

Provenance: formalization of a published result. Source: EconCSLib, `Arena.Reachable.trans`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reachability is transitive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Reachability is transitive. -/
theorem Arena.Reachable.trans {A : Arena} {s t u : A.State}
    (h₁ : A.Reachable s t) (h₂ : A.Reachable t u) :
    A.Reachable s u := by
  induction h₁ with
  | refl => exact h₂
  | step action _ ih => exact .step action (ih h₂)
