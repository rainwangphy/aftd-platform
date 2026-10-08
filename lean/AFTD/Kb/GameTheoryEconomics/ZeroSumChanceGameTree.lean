import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChancePlayer
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# ZeroSumChance.GameTree

Topic: equilibria   Node: 5b52af2b4ae0

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.GameTree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite binary game tree for a 2-player zero-sum game with Nature. * `Leaf val` — terminal node; `val` is A's payoff (B gets `-val`). * `Pnode p L R` — player `p`'s decision node; player chooses L or R. * `Nnode prob L R` — Nature's chance node; Nature picks L with probability `prob ∈ [0,1]` and R with probability `1 - prob`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A finite binary game tree for a 2-player zero-sum game with Nature. * `Leaf val` — terminal node; `val` is A's payoff (B gets `-val`). * `Pnode p L R` — player `p`'s decision node; player chooses L or R. * `Nnode prob L R` — Nature's chance node; Nature picks L with probability `prob ∈ [0,1]` and R with probability `1 - prob`. -/
inductive ZeroSumChance.GameTree : Type | Leaf  (val : ℚ)                                           : GameTree
  | Pnode (p : Player) (L R : GameTree)                       : GameTree
  | Nnode (prob : Set.Icc (0 : ℚ) 1) (L R : GameTree)        : GameTree
  deriving Repr, DecidableEq
