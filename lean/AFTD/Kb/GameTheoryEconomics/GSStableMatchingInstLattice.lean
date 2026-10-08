import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSStableMatching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSStableJoin
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingPartner
import AFTD.Kb.GameTheoryEconomics.GSStableJoinIsStable
import AFTD.Kb.GameTheoryEconomics.GSJoinWoman
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanLeLeft
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingInstPartialOrder
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanEqOr
import AFTD.Kb.GameTheoryEconomics.GSStableMeet
import AFTD.Kb.GameTheoryEconomics.GSMeetEquiv
import AFTD.Kb.GameTheoryEconomics.GSStableMeetGeRight
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanLeRight
import AFTD.Kb.GameTheoryEconomics.GSStableMeetIsStable
import AFTD.Kb.GameTheoryEconomics.GSStableMeetGeLeft
import AFTD.Kb.GameTheoryEconomics.GSMeetEquivSymmEqOr
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSStableJoinMatchW
import AFTD.Kb.GameTheoryEconomics.GSStableJoinMatchM
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchM
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchW
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.StableMatching.instLattice

Topic: matching_markets   Node: cd9f5d770057

Provenance: formalization of a published result. Source: EconCSLib, `GS.StableMatching.instLattice`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Conway–Knuth lattice.** The stable matchings of a one-to-one market form a lattice under the men-preference order: the join gives every man his more- preferred of two partners, the meet his less-preferred, and both are stable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- **Conway–Knuth lattice.** The stable matchings of a one-to-one market form a lattice under the men-preference order: the join gives every man his more- preferred of two partners, the meet his less-preferred, and both are stable. -/
noncomputable instance GS.StableMatching.instLattice : Lattice (StableMatching w m) :=
  { (inferInstance : PartialOrder (StableMatching w m)) with
    sup := fun μ ν => ⟨stableJoin μ.1 ν.1 μ.2 ν.2, stableJoin_isStable μ.1 ν.1 μ.2 ν.2⟩
    inf := fun μ ν => ⟨stableMeet μ.1 ν.1 μ.2 ν.2, stableMeet_isStable μ.1 ν.1 μ.2 ν.2⟩
    le_sup_left := fun μ ν j => joinWoman_le_left μ.1 ν.1 μ.2 ν.2 j
    le_sup_right := fun μ ν j => joinWoman_le_right μ.1 ν.1 μ.2 ν.2 j
    sup_le := fun μ ν bound h1 h2 j => by
      show (m.prefs j).idxOf (bound.partner j) ≤ (m.prefs j).idxOf (joinWoman μ.1 ν.1 μ.2 ν.2 j)
      rcases joinWoman_eq_or μ.1 ν.1 μ.2 ν.2 j with he | he
      · rw [he]; exact h1 j
      · rw [he]; exact h2 j
    inf_le_left := fun μ ν j => stableMeet_ge_left μ.1 ν.1 μ.2 ν.2 j
    inf_le_right := fun μ ν j => stableMeet_ge_right μ.1 ν.1 μ.2 ν.2 j
    le_inf := fun bound μ ν h1 h2 j => by
      show (m.prefs j).idxOf ((meetEquiv μ.1 ν.1 μ.2 ν.2).symm j)
        ≤ (m.prefs j).idxOf (bound.partner j)
      rcases meetEquiv_symm_eq_or μ.1 ν.1 μ.2 ν.2 j with he | he
      · rw [he]; exact h1 j
      · rw [he]; exact h2 j }
