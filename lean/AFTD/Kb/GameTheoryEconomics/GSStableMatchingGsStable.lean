import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSStableMatching
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.MatchingOfGS
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.GsBijective
import AFTD.Kb.GameTheoryEconomics.GaleShapleyIsStable
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingInstPartialOrder
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingInstLattice
import AFTD.Kb.GameTheoryEconomics.MatchingMarket

/-!
# GS.StableMatching.gsStable

Topic: matching_markets   Node: 89420e5851ca

Provenance: formalization of a published result. Source: EconCSLib, `GS.StableMatching.gsStable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The men-proposing Gale–Shapley output, as an element of the lattice of stable matchings.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- The men-proposing Gale–Shapley output, as an element of the lattice of stable matchings. -/
noncomputable def GS.StableMatching.gsStable (w' m' : Preferences n) [NeZero n] : StableMatching w' m' :=
  ⟨Matching.ofGS (gs w' m') (gs_bijective w' m'), galeShapley_isStable w' m'⟩
