import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget

/-!
# GS.daStep

Topic: matching_markets   Node: 0836193de758

Provenance: formalization of a published result. Source: EconCSLib, `GS.daStep`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

One step of standard men-proposing DA. All free men propose; women pick the best of {held, new proposers} by rank; free men advance their cursor by 1.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- One step of standard men-proposing DA. All free men propose; women pick the best of {held, new proposers} by rank; free men advance their cursor by 1. -/
noncomputable def GS.daStep {n : ℕ} (w m : Preferences n) (s : DAState n) : DAState n :=
  let newNextChoice : Fin n → ℕ := fun i =>
    if isFree s i then s.nextChoice i + 1 else s.nextChoice i
  let proposerList : Fin n → List (Fin n) := fun j =>
    (Finset.univ.filter (fun i =>
      isFree s i && (propTarget m i (s.nextChoice i) == some j))).val.toList
  let bestNew : Fin n → Option (Fin n) := fun j =>
    (proposerList j).argmin (fun i => (w.prefs j).idxOf i)
  let newHolding : Fin n → Option (Fin n) := fun j =>
    match s.holding j, bestNew j with
    | none,   none   => none
    | some h, none   => some h
    | none,   some p => some p
    | some h, some p =>
        if (w.prefs j).idxOf p < (w.prefs j).idxOf h then some p else some h
  { nextChoice := newNextChoice, holding := newHolding }
