import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultiItemBundle

/-!
# MultiItemBundle.toFinset

Topic: mechanism_design   Node: eca11848120d

Provenance: formalization of a published result. Source: EconCSLib, `MultiItemBundle.toFinset`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/AuctionBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

View a named multi-item bundle as the underlying finite set of item indices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- View a named multi-item bundle as the underlying finite set of item indices. -/
def MultiItemBundle.toFinset {k : ℕ} (bundle : MultiItemBundle k) : Finset (Fin k) :=
  bundle
