import AFTD.Prelude

/-!
# MinimaxLoomis.singleton_of_card_one

Topic: equilibria   Node: c39fcc87fd37

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.singleton_of_card_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

When the row index type has cardinality 1, every simplex point is the unique pure strategy and `Finset.univ` is a singleton.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- When the row index type has cardinality 1, every simplex point is the unique pure strategy and `Finset.univ` is a singleton. -/
theorem MinimaxLoomis.singleton_of_card_one {K : Type*} [Fintype K] [DecidableEq K]
    (H : Fintype.card K = 1) :
    ∃ a : K, (Finset.univ : Finset K) = {a} := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 H
  exact ⟨a, by ext; simp [ha]⟩
