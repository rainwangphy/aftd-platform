import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget

/-!
# GS.daStep_holding

Topic: matching_markets   Node: 226772d65a00

Provenance: formalization of a published result. Source: EconCSLib, `GS.daStep_holding`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

One step of DA: woman `p`'s new holding, expanded once. This is the workhorse rewrite for any proof that needs to case-split on what `(daStep w m s).holding p` is. It unfolds the outermost `match` inside `daStep`'s `newHolding`. The statement **does inline** the auxiliary `proposerList` / `bestNew` formulae verbatim; downstream proofs re-abbreviate them with `set` *after* rewriting (see `holdinv_step`). The match shape is: ``` match s.holding p, bestNew p with | none, none => none -- still free | some h, none => some h -- old hold kept | none, some q => some q -- new proposer | some h, some q => if rank q < rank h then q else h -- upgrade? ``` where `bestNew p = (proposerList p).argmin (rank in w.prefs p)` and `proposerList p` is the list of free men who proposed to `p` this step. Provable by `rfl` because `daStep` is `noncomputable def` and the body is a sequence of `let`s ending in a structure literal whose `.holding p` projects directly to the inner `match`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- One step of DA: woman `p`'s new holding, expanded once. This is the workhorse rewrite for any proof that needs to case-split on what `(daStep w m s).holding p` is. It unfolds the outermost `match` inside `daStep`'s `newHolding`. The statement **does inline** the auxiliary `proposerList` / `bestNew` formulae verbatim; downstream proofs re-abbreviate them with `set` *after* rewriting (see `holdinv_step`). The match shape is: ``` match s.holding p, bestNew p with | none, none => none -- still free | some h, none => some h -- old hold kept | none, some q => some q -- new proposer | some h, some q => if rank q < rank h then q else h -- upgrade? ``` where `bestNew p = (proposerList p).argmin (rank in w.prefs p)` and `proposerList p` is the list of free men who proposed to `p` this step. Provable by `rfl` because `daStep` is `noncomputable def` and the body is a sequence of `let`s ending in a structure literal whose `.holding p` projects directly to the inner `match`. -/
lemma GS.daStep_holding {n : ℕ} (w m : Preferences n) (s : DAState n) (p : Fin n) :
    (daStep w m s).holding p =
      (match s.holding p,
        ((Finset.univ.filter (fun i : Fin n =>
            isFree s i && (propTarget m i (s.nextChoice i) == some p))).val.toList).argmin
          (fun i => (w.prefs p).idxOf i) with
        | none,   none   => none
        | some h, none   => some h
        | none,   some q => some q
        | some h, some q =>
            if (w.prefs p).idxOf q < (w.prefs p).idxOf h then some q else some h) := rfl
