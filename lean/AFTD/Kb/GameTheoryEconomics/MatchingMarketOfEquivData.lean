import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.IsPreference
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# MatchingMarket.ofEquivData

Topic: matching_markets   Node: c847bf4dabd0

Provenance: formalization of a published result. Source: EconCSLib, `MatchingMarket.ofEquivData`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Build a `MatchingMarket (Fin n) (Fin n)` from list-based preference data. `some j ≻ some k` iff `j` appears earlier in the list; `none` is worst. **Side transposition (read carefully).** `ofEquivData a b` puts `a` on the market's MEN (`prefM`) and `b` on the market's WOMEN (`prefW`). Hence when it is applied as `ofEquivData w m` with the algorithm's `w` (women's / choosing preferences) and `m` (men's / proposing preferences), the market's "men" are the algorithm's *women* and the market's "women" are the algorithm's *men* — the two sides are **transposed**. Stability is symmetric, so this is harmless, but be aware that a market-`M` index corresponds to an algorithm woman (and vice versa); the stability proof reasons in the algorithm frame.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- Build a `MatchingMarket (Fin n) (Fin n)` from list-based preference data. `some j ≻ some k` iff `j` appears earlier in the list; `none` is worst. **Side transposition (read carefully).** `ofEquivData a b` puts `a` on the market's MEN (`prefM`) and `b` on the market's WOMEN (`prefW`). Hence when it is applied as `ofEquivData w m` with the algorithm's `w` (women's / choosing preferences) and `m` (men's / proposing preferences), the market's "men" are the algorithm's *women* and the market's "women" are the algorithm's *men* — the two sides are **transposed**. Stability is symmetric, so this is harmless, but be aware that a market-`M` index corresponds to an algorithm woman (and vice versa); the stability proof reasons in the algorithm frame. -/
noncomputable def MatchingMarket.ofEquivData (wPrefs mPrefs : GS.Preferences n) :
    MatchingMarket (Fin n) (Fin n) where
  prefM := fun i =>
    { rel := fun ow1 ow2 =>
        match ow1, ow2 with
        | none,    none    => True
        | none,    some _  => False
        | some _,  none    => True
        | some w1, some w2 => (wPrefs.prefs i).idxOf w1 ≤ (wPrefs.prefs i).idxOf w2
      prop :=
        { reflexive := by intro ow; cases ow <;> simp
          transitive := by
            intro ow1 ow2 ow3 h12 h23
            cases ow1 <;> cases ow2 <;> cases ow3 <;> simp_all
            exact Nat.le_trans h12 h23
          total := by
            intro ow1 ow2; cases ow1 <;> cases ow2 <;> simp
            exact Nat.le_or_le _ _ } }
  prefW := fun j =>
    { rel := fun om1 om2 =>
        match om1, om2 with
        | none,    none    => True
        | none,    some _  => False
        | some _,  none    => True
        | some m1, some m2 => (mPrefs.prefs j).idxOf m1 ≤ (mPrefs.prefs j).idxOf m2
      prop :=
        { reflexive := by intro om; cases om <;> simp
          transitive := by
            intro om1 om2 om3 h12 h23
            cases om1 <;> cases om2 <;> cases om3 <;> simp_all
            exact Nat.le_trans h12 h23
          total := by
            intro om1 om2; cases om1 <;> cases om2 <;> simp
            exact Nat.le_or_le _ _ } }
