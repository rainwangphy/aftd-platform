import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSStableMatching
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingInstPartialOrder
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingGsStable
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingGsStableGreatest
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingInstLattice
import AFTD.Kb.GameTheoryEconomics.MatchingMarket

/-!
# GS.StableMatching.gsStable_isGreatest

Topic: matching_markets   Node: 67ade6d310bd

Provenance: formalization of a published result. Source: EconCSLib, `GS.StableMatching.gsStable_isGreatest`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`gsStable` is the greatest element of the stable-matching lattice.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS GS.StableMatching in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- `gsStable` is the greatest element of the stable-matching lattice. -/
theorem GS.StableMatching.gsStable_isGreatest [NeZero n] :
    IsGreatest (Set.univ : Set (StableMatching w m)) (gsStable w m) :=
  ⟨Set.mem_univ _, fun μ _ => gsStable_greatest μ⟩
