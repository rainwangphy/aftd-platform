import AFTD.Prelude

/-!
# OpponentProfile

Topic: mechanism_design   Node: a6fd7efa8e26

Provenance: formalization of a published result. Source: EconCSLib, `OpponentProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Opponent profiles for agent `i`, with constant coordinate type `X`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
/-- Opponent profiles for agent `i`, with constant coordinate type `X`. -/
abbrev OpponentProfile (I : Type*) (X : Type*) (i : I) := ∀ _ : {j // j ≠ i}, X
