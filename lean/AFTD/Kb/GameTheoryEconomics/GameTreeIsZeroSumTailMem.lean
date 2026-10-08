import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum

/-!
# GameTree.IsZeroSum.tail_mem

Topic: equilibria   Node: 41182769e354

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsZeroSum.tail_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every tail child of a zero-sum node is zero-sum.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Every tail child of a zero-sum node is zero-sum. -/
theorem GameTree.IsZeroSum.tail_mem {m : Fin 2} {h : GameTree (Fin 2) ℚ}
    {t : List (GameTree (Fin 2) ℚ)} {c : GameTree (Fin 2) ℚ}
    (hzs : IsZeroSum (Node m h t)) (hmem : c ∈ t) :
    IsZeroSum c := by
  have hzs' : IsZeroSum h ∧ ∀ c ∈ t, IsZeroSum c := by
    simpa [IsZeroSum] using hzs
  exact hzs'.2 c hmem
