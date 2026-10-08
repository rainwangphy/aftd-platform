import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum

/-!
# GameTree.IsZeroSum.head

Topic: equilibria   Node: 82e1398a57fe

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsZeroSum.head`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The head child of a zero-sum node is zero-sum.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The head child of a zero-sum node is zero-sum. -/
theorem GameTree.IsZeroSum.head {m : Fin 2} {h : GameTree (Fin 2) ℚ}
    {t : List (GameTree (Fin 2) ℚ)} (hzs : IsZeroSum (Node m h t)) :
    IsZeroSum h := by
  have hzs' : IsZeroSum h ∧ ∀ c ∈ t, IsZeroSum c := by
    simpa [IsZeroSum] using hzs
  exact hzs'.1
