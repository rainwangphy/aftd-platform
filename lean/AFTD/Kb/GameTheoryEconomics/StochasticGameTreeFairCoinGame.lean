import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree

/-!
# StochasticGameTree.fairCoinGame

Topic: equilibria   Node: 08962e567466

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.fairCoinGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A one-step fair coin game for examples and CI regression checks.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- A one-step fair coin game for examples and CI regression checks. -/
def StochasticGameTree.fairCoinGame : StochasticGameTree (Fin 2) :=
  StochasticGameTree.Chance (1 / 2)
    (StochasticGameTree.Leaf (fun i => if i = 0 then 1 else 0))
    (List.cons
      (1 / 2, StochasticGameTree.Leaf (fun i => if i = 0 then 0 else 1))
      List.nil)
