import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGamePureStrategy
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGamePureStrategyActionAt

/-!
# FiniteImperfectGame.actionAt_same_info_label

Topic: equilibria   Node: 18ef012620a6

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.actionAt_same_info_label`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If two states are in the same information set, a strategy is queried through the same information-set label at both states. This is the formal constancy-by-indexing property; comparing concrete action values requires an action equivalence from `SameActionsOnInfo`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- If two states are in the same information set, a strategy is queried through the same information-set label at both states. This is the formal constancy-by-indexing property; comparing concrete action values requires an action equivalence from `SameActionsOnInfo`. -/
theorem FiniteImperfectGame.actionAt_same_info_label {i : N} (σ : G.PureStrategy i)
    {s t : G.State} {k : G.InfoSet}
    (hs : G.info s = some k) (ht : G.info t = some k)
    (hms : G.mover s = some i) (hmt : G.mover t = some i) :
    PureStrategy.actionAt G σ hs hms = σ k s hs hms ∧
      PureStrategy.actionAt G σ ht hmt = σ k t ht hmt :=
  ⟨rfl, rfl⟩
