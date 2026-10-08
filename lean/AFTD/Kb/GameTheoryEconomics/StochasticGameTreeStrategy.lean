import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree

/-!
# StochasticGameTree.Strategy

Topic: equilibria   Node: 860313328700

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.Strategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pure strategy chooses a child at every player-controlled node.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- A pure strategy chooses a child at every player-controlled node. -/
def StochasticGameTree.Strategy (N : Type*) : Type _ :=
  (m : N) → (h : StochasticGameTree N) → (t : List (StochasticGameTree N)) →
    { c : StochasticGameTree N // c ∈ h :: t }
