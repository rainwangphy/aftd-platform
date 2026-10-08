import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSMeetMan
import AFTD.Kb.GameTheoryEconomics.GSMeetEquiv
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.stableMeet

Topic: matching_markets   Node: 4c63fc430283

Provenance: formalization of a published result. Source: EconCSLib, `GS.stableMeet`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The **meet** `μ ∧ ν`: each woman keeps her more-preferred man; each man keeps his less-preferred woman.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- The **meet** `μ ∧ ν`: each woman keeps her more-preferred man; each man keeps his less-preferred woman. -/
noncomputable def GS.stableMeet : Matching (Fin n) (Fin n) where
  matchM i := some (meetMan μ ν hμ hν i)
  matchW j := some ((meetEquiv μ ν hμ hν).symm j)
  consistent := by
    intro i j
    simp only [Option.some.injEq]
    rw [Equiv.symm_apply_eq]
    exact eq_comm
